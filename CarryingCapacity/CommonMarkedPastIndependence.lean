import CarryingCapacity.MarkedPastIndependence
import CarryingCapacity.MarkedBoundedCounts
import CarryingCapacity.IndependentProductHistory
import CarryingCapacity.CommonFrozenStopping

/-!
# Future bounded counts are independent of the full common-noise history

The actual independent strip samples lift the proved strip past/future
independence to complete arrays. A guarded height translation recovers the
existing common-noise observation on every sample, including unarrived
sentinels. Finite strip summation then gives independence for the genuine
bounded time-height rectangle mass, also under the completed observation law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace CarryingCapacity.CommonMarkedPastIndependence
open MarkedNoise MarkedObservation MarkedStripCounts MarkedPastIndependence
  MarkedBoundedCounts

variable {J : Type*}

abbrev StripViews (J : Type*) := J × ℕ → ℕ → ℝ × ℝ

def stripViews (s : ℝ) (ω : MarkedNoise.Sample J) : StripViews J :=
  fun i => stripView s (ω i)

theorem measurable_stripViews (s : ℝ) :
    Measurable (stripViews (J := J) s) :=
  measurable_pi_lambda _ (fun i =>
    (measurable_pi_lambda _ (measurable_stripView s)).comp (measurable_pi_apply i))

/-- Shift only observed heights. The unarrived sentinel remains exactly `(s+1,0)`. -/
def shiftedStripViews (s : ℝ) (v : StripViews J) : CommonNoiseFiltration.EventView J :=
  fun e => if (v (e.1, e.2.1) e.2.2).1 ≤ s then
    ((v (e.1, e.2.1) e.2.2).1, (e.2.1 : ℝ) + (v (e.1, e.2.1) e.2.2).2)
      else (s + 1, 0)

theorem measurable_shiftedStripViews (s : ℝ) :
    Measurable (shiftedStripViews (J := J) s) := by
  apply measurable_pi_lambda
  intro e
  have hp : Measurable (fun v : StripViews J => v (e.1, e.2.1) e.2.2) :=
    (measurable_pi_apply e.2.2).comp (measurable_pi_apply (e.1, e.2.1))
  exact (hp.fst.prodMk (measurable_const.add hp.snd)).ite
    (measurableSet_le hp.fst measurable_const) measurable_const

/-- Exact factorization of the existing common observation, without an exceptional event. -/
theorem view_eq_shiftedStripViews (s : ℝ) (ω : MarkedNoise.Sample J) :
    CommonNoiseFiltration.view s ω = shiftedStripViews s (stripViews s ω) := by
  funext e
  by_cases h : CountableJumpProcess.arrival (ω (e.1, e.2.1)).1 (e.2.2 + 1) ≤ s
  · simp only [CommonNoiseFiltration.view, CommonNoiseFiltration.censor,
      CommonNoiseFiltration.points, MarkedNoise.point, shiftedStripViews,
      stripViews, stripView, h, if_true]
  · have hsent : ¬s + 1 ≤ s := by linarith
    simp only [CommonNoiseFiltration.view, CommonNoiseFiltration.censor,
      CommonNoiseFiltration.points, MarkedNoise.point, shiftedStripViews,
      stripViews, stripView, h, if_false, hsent]

def stripFutureCounts (B : J × ℕ → Set ℝ) (s t : ℝ)
    (ω : MarkedNoise.Sample J) : J × ℕ → ℕ :=
  fun i => windowCount (B i) s (s + t) (ω i)

theorem measurable_stripFutureCounts (B : J × ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i)) (s t : ℝ) :
    Measurable (stripFutureCounts B s t) :=
  measurable_pi_lambda _ (fun i =>
    (measurable_windowCount (B i) (hB i) s (s + t)).comp (measurable_pi_apply i))

/-- Each strip may use its own measurable future category. Full arrays are independent. -/
theorem independent_stripViews_stripFutureCounts (B : J × ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i)) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IndepFun (stripViews (J := J) s) (stripFutureCounts B s t) (law J) := by
  exact IndependentProductHistory.indepFun_observations_futures
    (fun _ : J × ℕ => stripLaw)
    (fun _ => stripView s) (fun _ => measurable_pi_lambda _ (measurable_stripView s))
    (fun i => windowCount (B i) s (s + t))
    (fun i => measurable_windowCount (B i) (hB i) s (s + t))
    (fun i => independent_stripView_windowCount (B i) (hB i) s t hs ht)

/-- The full existing common-noise view is independent of the future category-count array. -/
theorem independent_view_stripFutureCounts (B : J × ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i)) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IndepFun (CommonNoiseFiltration.view (J := J) s) (stripFutureCounts B s t) (law J) := by
  have h := (independent_stripViews_stripFutureCounts B hB s t hs ht).comp
    (measurable_shiftedStripViews s) measurable_id
  have he : shiftedStripViews (J := J) s ∘ stripViews s = CommonNoiseFiltration.view s :=
    funext (fun ω => (view_eq_shiftedStripViews s ω).symm)
  simpa only [he, Function.id_comp] using h

def stripSum (j : J) (m : ℕ) (v : J × ℕ → ℕ) : ℕ :=
  ∑ n ∈ Finset.range m, v (j, n)

theorem measurable_stripSum (j : J) (m : ℕ) : Measurable (stripSum j m) :=
  Finset.measurable_sum _ (fun n _ => measurable_pi_apply (j, n))

/-- Finite future strip sums are independent of the entire observed marked past. -/
theorem independent_view_boundedWindowCount (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IndepFun (CommonNoiseFiltration.view (J := J) s)
      (boundedWindowCount j m B s (s + t)) (law J) := by
  let A : J × ℕ → Set ℝ := fun i => (fun x : ℝ => (i.2 : ℝ) + x) ⁻¹' B
  have hA (i : J × ℕ) : MeasurableSet (A i) :=
    hB.preimage (measurable_const.add measurable_id)
  exact (independent_view_stripFutureCounts A hA s t hs ht).comp
    measurable_id (measurable_stripSum j m)

/-- Independence is transferred to the genuine mass of the original random measure. -/
theorem independent_view_countingMeasure_windowrectangle (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IndepFun (CommonNoiseFiltration.view (J := J) s)
      (fun ω => countingMeasure j ω (Ioc s (s + t) ×ˢ B)) (law J) := by
  have h := (independent_view_boundedWindowCount j m B hB s t hs ht).comp
    measurable_id (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞)))
  apply h.congr (Eventually.of_forall (fun _ => rfl))
  filter_upwards [ae_countingMeasure_eq_boundedWindowCount j] with ω hω
  exact (hω m B hB hbound s (s + t) hs (le_add_of_nonneg_right ht)).symm

/-- The raw natural filtration has the exact future bounded-count independence property. -/
theorem independent_filtration_countingMeasure_windowrectangle
    (j : J) (m : ℕ) (B : Set ℝ) (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Indep (CommonNoiseFiltration.filtration J s)
      (MeasurableSpace.comap (fun ω : MarkedNoise.Sample J =>
        countingMeasure j ω (Ioc s (s + t) ×ˢ B)) inferInstance) (law J) :=
  independent_view_countingMeasure_windowrectangle j m B hB hbound s t hs ht

/-- The same actual future count remains independent after completing the ambient law
and augmenting the history by its null sets. -/
theorem independent_completedAt_countingMeasure_windowrectangle
    (j : J) (m : ℕ) (B : Set ℝ) (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Indep (CommonFrozenStopping.completedAt J s)
      (MeasurableSpace.comap (fun ω : MarkedNoise.Sample J =>
        countingMeasure j ω (Ioc s (s + t) ×ˢ B)) inferInstance)
      (CommonFrozenStopping.completedLaw J) := by
  apply NullAugmentedIndependence.indep_completion_iff.mpr
  exact NullAugmentedIndependence.indep_augment_left
    (independent_filtration_countingMeasure_windowrectangle j m B hB hbound s t hs ht)

end CarryingCapacity.CommonMarkedPastIndependence
