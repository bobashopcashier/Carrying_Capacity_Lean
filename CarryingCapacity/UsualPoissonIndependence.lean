import CarryingCapacity.PrescribedMartingale
import CarryingCapacity.InitialMarkedPastIndependence
import CarryingCapacity.CommonFrozenRegularity
import CarryingCapacity.MarkedSetCounts
import CarryingCapacity.IndependenceLimit

/-!
# Future Poisson counts and the usual natural filtration

Actual bounded marked counts are constant under sufficiently small right shifts
of their lower time endpoint. This follows from their finite chronological
list, including on one event for all time endpoints. The supplied-space raw
independence follows by pulling back genuine canonical past events.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal NNReal

namespace CarryingCapacity.UsualPoissonIndependence
open PrescribedPoissonRealization PrescribedPoissonFiltration

variable {J : Type} [Fintype J]

/-- Moving the excluded lower endpoint a little to the right changes no
actual bounded rectangle count. The result includes all endpoints on one event. -/
theorem ae_window_right_constant (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ)) :
    ∀ᵐ ω ∂MarkedNoise.law J, ∀ s t : ℝ, ∃ b, s < b ∧ ∀ u ∈ Ico s b,
      MarkedNoise.countingMeasure j ω (Ioc u t ×ˢ B) =
        MarkedNoise.countingMeasure j ω (Ioc s t ×ˢ B) := by
  filter_upwards [CommonFrozenRegularity.ae_boxedList_right_constant (J := J),
    ChronologicalEvents.ae_boxedList_mem (J := J)] with ω hc hm
  intro s t
  obtain ⟨b,hb,hlist⟩ := hc m s
  refine ⟨b,hb,?_⟩
  intro u hu
  rw [MarkedSetCounts.countingMeasure_eq_count_preimage j ω _ (measurableSet_Ioc.prod hB),
    MarkedSetCounts.countingMeasure_eq_count_preimage j ω _ (measurableSet_Ioc.prod hB)]
  congr 1
  ext k
  change (MarkedNoise.point j ω k).1 ∈ Ioc u t ∧ (MarkedNoise.point j ω k).2 ∈ B ↔
    (MarkedNoise.point j ω k).1 ∈ Ioc s t ∧ (MarkedNoise.point j ω k).2 ∈ B
  constructor
  · rintro ⟨⟨hku,hkt⟩,hkB⟩
    exact ⟨⟨hu.1.trans_lt hku,hkt⟩,hkB⟩
  · rintro ⟨⟨hks,hkt⟩,hkB⟩
    refine ⟨⟨?_,hkt⟩,hkB⟩
    by_contra hnot
    have hheight : (MarkedNoise.point j ω k).2 ≤ (m : ℝ) :=
      le_of_lt (show (MarkedNoise.point j ω k).2 < (m : ℝ) from hbound hkB)
    have hmemb : (j,k) ∈ ChronologicalEvents.boxedList (ω,u,(m : ℝ)) :=
      (hm u m (j,k)).mpr ⟨le_of_not_gt hnot,hheight⟩
    rw [hlist u hu] at hmemb
    exact (not_le_of_gt hks) ((hm s m (j,k)).mp hmemb).1

/-- Right-approximating deterministic times give eventually identical
actual future counts, stronger than convergence in probability. -/
theorem ae_window_eventually_eq (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ) (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 s)) (hsu : ∀ n, s ≤ u n) :
    ∀ᵐ ω ∂MarkedNoise.law J, ∀ᶠ n in atTop,
      MarkedNoise.countingMeasure j ω (Ioc (u n) t ×ˢ B) =
        MarkedNoise.countingMeasure j ω (Ioc s t ×ˢ B) := by
  filter_upwards [ae_window_right_constant j m B hB hbound] with ω hω
  obtain ⟨b,hb,he⟩ := hω s t
  filter_upwards [hu.eventually (gt_mem_nhds hb)] with n hn
  exact he (u n) ⟨hsu n,hn⟩

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  (M : J → Ω → Measure (ℝ × ℝ)) (ξ : Ω → A)
  (P : Measure Ω) [IsProbabilityMeasure P]
  (hM : ∀ j, Measurable (M j)) (hPoisson : PoissonObservationLaw.HasDisjointLaws P J M)
  (hξ : Measurable ξ) (hIndependent : IndepFun ξ (fun ω j => M j ω) P)
include hM hPoisson

/-- The exact same eventual-count equality holds for the specified measures,
not just for the canonical reconstruction. -/
theorem ae_supplied_window_eventually_eq (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ) (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 s)) (hsu : ∀ n, s ≤ u n) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      M j ω (Ioc (u n) t ×ˢ B) = M j ω (Ioc s t ×ˢ B) := by
  have hc := ae_window_eventually_eq j m B hB hbound s t u hu hsu
  rw [← noise_map J M P hM hPoisson] at hc
  have hp := ae_of_ae_map (measurable_noise J M hM).aemeasurable hc
  filter_upwards [hp,ae_countingMeasure_noise J M P hM hPoisson] with ω hω he
  simpa only [he j] using hω

include hξ hIndependent

/-- Genuine supplied completed-past independence, before imposing right
continuity on the filtration. -/
theorem independent_completedAt_window (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Indep (UsualFiltration.completedAt P (rawFiltration J M ξ hM hξ) s)
      (MeasurableSpace.comap (fun ω => M j ω (Ioc s t ×ˢ B)) inferInstance)
      (UsualFiltration.completedLaw P) := by
  letI : IsProbabilityMeasure (P.map ξ) := isProbabilityMeasure_map hξ.aemeasurable
  apply NullAugmentedIndependence.indep_completion_iff.mpr
  apply (Indep_iff _ _ _).mpr
  intro S H hS hH
  obtain ⟨C,hC,heC⟩ := PrescribedMartingale.completed_event_pullback J M ξ P hM hPoisson s hS
  obtain ⟨U,hU,rfl⟩ := hH
  let F := fun p : CommonInitialNoise.Sample A J => MarkedNoise.countingMeasure j p.2 (Ioc s t ×ˢ B)
  have hF : Measurable F :=
    ((Measure.measurable_coe (measurableSet_Ioc.prod hB)).comp
      (MarkedNoise.measurable_countingMeasure j)).comp measurable_snd
  have heU : (fun ω => M j ω (Ioc s t ×ˢ B)) ⁻¹' U =ᵐ[P]
      record J M ξ ⁻¹' (F ⁻¹' U) := by
    filter_upwards [ae_countingMeasure_noise J M P hM hPoisson] with ω hω
    change (M j ω (Ioc s t ×ˢ B) ∈ U) =
      (MarkedNoise.countingMeasure j (noise J M ω) (Ioc s t ×ˢ B) ∈ U)
    rw [hω j]
  have heI : (S ∩ (fun ω => M j ω (Ioc s t ×ˢ B)) ⁻¹' U : Set Ω) =ᵐ[P]
      record J M ξ ⁻¹' (C ∩ F ⁻¹' U) := by
    filter_upwards [heC,heU] with ω hC' hU'
    exact congrArg₂ And hC' hU'
  have hCm : MeasurableSet C := (CommonInitialNoise.filtration A J).le s C hC
  have hm (V : Set (CommonInitialNoise.Sample A J)) (hV : MeasurableSet V) :
      P (record J M ξ ⁻¹' V) = CommonInitialNoise.law (P.map ξ) J V := by
    rw [← record_map J M ξ P hM hPoisson hξ hIndependent]
    exact (Measure.map_apply (measurable_record J M ξ hM hξ) hV).symm
  rw [measure_congr heI,measure_congr heC,measure_congr heU,
    hm _ (hCm.inter (hU.preimage hF)),hm _ hCm,hm _ (hU.preimage hF)]
  have hi := InitialMarkedPastIndependence.independent_filtration_countingMeasure_windowrectangle
    (P.map ξ) j m B hB hbound s (t-s) hs (sub_nonneg.mpr hst)
  rw [add_sub_cancel] at hi
  exact (Indep_iff _ _ _).mp hi C (F ⁻¹' U) hC ⟨U,hU,rfl⟩

/-- Future counts are independent of the completed right-continuous
natural history, not just of its completed raw past. -/
theorem independent_usual_window (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Indep (UsualFiltration.filtration P (rawFiltration J M ξ hM hξ) s)
      (MeasurableSpace.comap (fun ω => M j ω (Ioc s t ×ˢ B)) inferInstance)
      (UsualFiltration.completedLaw P) := by
  rcases eq_or_lt_of_le hst with rfl | hst
  · simp only [Ioc_self,empty_prod,measure_empty]
    rw [MeasurableSpace.comap_const]
    exact indep_bot_right _
  obtain ⟨u,_,hu,hlim⟩ := exists_seq_strictAnti_tendsto' hst
  have hm (r : ℝ) : Measurable (fun ω => M j ω (Ioc r t ×ˢ B)) :=
    (Measure.measurable_coe (measurableSet_Ioc.prod hB)).comp (hM j)
  let F := UsualFiltration.filtration P (rawFiltration J M ξ hM hξ)
  let Q := UsualFiltration.completedLaw P
  have hind : ∀ n, Indep (F s)
      (MeasurableSpace.comap (fun ω => M j ω (Ioc (u n) t ×ˢ B)) inferInstance) Q := by
    intro n
    exact indep_of_indep_of_le_left
      (independent_completedAt_window M ξ P hM hPoisson hξ hIndependent j m B hB hbound
        (u n) t (hs.trans (hu n).1.le) (hu n).2.le)
      (UsualFiltration.at_le_completedAt P (rawFiltration J M ξ hM hξ) (hu n).1)
  have he : ∀ᵐ ω ∂Q, ∀ᶠ n in atTop,
      M j ω (Ioc (u n) t ×ˢ B) = M j ω (Ioc s t ×ˢ B) :=
    ae_supplied_window_eventually_eq M P hM hPoisson j m B hB hbound s t u hlim
      (fun n => (hu n).1.le)
  have hm' (r : ℝ) : @Measurable Ω ℝ≥0∞ (UsualFiltration.completedSpace P) inferInstance
      (fun ω => M j ω (Ioc r t ×ˢ B)) :=
    (hm r).mono EventuallyMeasurableSpace.measurable_le le_rfl
  letI : MeasurableSpace Ω := UsualFiltration.completedSpace P
  exact IndependenceLimit.indep_of_ae_eventuallyEq Q (F s) (F.le s)
    (fun n ω => M j ω (Ioc (u n) t ×ˢ B)) (fun ω => M j ω (Ioc s t ×ˢ B))
    (fun n => hm' (u n)) (hm' s) hind he

end CarryingCapacity.UsualPoissonIndependence
