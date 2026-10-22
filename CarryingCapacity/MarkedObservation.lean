import CarryingCapacity.MarkedPastProducts
import CarryingCapacity.MarkedStripCounts
import CarryingCapacity.ClockPastObservation

/-!
# Finite cylinders of the actual censored strip observation

The strip observation reveals both arrival time and mark only after an arrival.
Finite products of arbitrary measurable complex test functions are measurable,
and unit bounds give genuine integrability. Integrating out the independent
marks computes their clock-dependent mean. On good clocks, the same integration
factors from a subsequent block of marks using the proved deterministic-index
factorization.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace CarryingCapacity.MarkedObservation
open CountableJumpProcess FrozenProcess MarkedNoise MarkedStripCounts
  MarkedBlockProducts MarkedPastProducts

def stripView (s : ℝ) (ω : StripSample) (k : ℕ) : ℝ × ℝ :=
  if arrival ω.1 (k + 1) ≤ s then (arrival ω.1 (k + 1), ω.2 k) else (s + 1, 0)

theorem measurable_stripView (s : ℝ) (k : ℕ) :
    Measurable (fun ω : StripSample => stripView s ω k) := by
  exact (((measurable_arrival (k + 1)).comp measurable_fst).prodMk
    ((measurable_pi_apply k).comp measurable_snd)).ite
    (measurableSet_le ((measurable_arrival (k + 1)).comp measurable_fst) measurable_const)
    measurable_const

def observedProduct (s : ℝ) (K : Finset ℕ) (F : ℕ → (ℝ × ℝ) → ℂ)
    (ω : StripSample) : ℂ :=
  ∏ k ∈ K, F k (stripView s ω k)

theorem measurable_observedProduct (s : ℝ) (K : Finset ℕ) (F : ℕ → (ℝ × ℝ) → ℂ)
    (hF : ∀ k, Measurable (F k)) : Measurable (observedProduct s K F) :=
  Finset.measurable_prod _ (fun k _ => (hF k).comp (measurable_stripView s k))

theorem norm_observedProduct_le_one (s : ℝ) (K : Finset ℕ) (F : ℕ → (ℝ × ℝ) → ℂ)
    (hF : ∀ k p, ‖F k p‖ ≤ 1) (ω : StripSample) : ‖observedProduct s K F ω‖ ≤ 1 :=
  (Finset.norm_prod_le _ _).trans
    (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun k _ => hF k (stripView s ω k)))

theorem integrable_observedProduct (s : ℝ) (K : Finset ℕ) (F : ℕ → (ℝ × ℝ) → ℂ)
    (hF : ∀ k, Measurable (F k)) (hbound : ∀ k p, ‖F k p‖ ≤ 1) :
    Integrable (observedProduct s K F) stripLaw := by
  exact (integrable_const (1 : ℝ)).mono'
    (measurable_observedProduct s K F hF).aestronglyMeasurable
    (Eventually.of_forall (norm_observedProduct_le_one s K F hbound))

def clockMean (s : ℝ) (K : Finset ℕ) (F : ℕ → (ℝ × ℝ) → ℂ) (ω : ClockSpace) : ℂ :=
  ∏ k ∈ K, if arrival ω (k + 1) ≤ s then
    ∫ x, F k (arrival ω (k + 1), x) ∂uniformUnit else F k (s + 1, 0)

theorem measurable_clockMean (s : ℝ) (K : Finset ℕ) (F : ℕ → (ℝ × ℝ) → ℂ)
    (hF : ∀ k, Measurable (F k)) : Measurable (clockMean s K F) := by
  apply Finset.measurable_prod
  intro k _
  have hm : Measurable (fun y : ℝ => ∫ x, F k (y, x) ∂uniformUnit) :=
    (hF k).stronglyMeasurable.integral_prod_right'.measurable
  exact (hm.comp (measurable_arrival (k + 1))).ite
    (measurableSet_le (measurable_arrival (k + 1)) measurable_const) measurable_const

/-- Every fixed clock admits the exact finite-mark integration identity. -/
theorem integral_observedProduct_marks (s : ℝ) (K : Finset ℕ)
    (F : ℕ → (ℝ × ℝ) → ℂ) (hF : ∀ k, Measurable (F k)) (ω : ClockSpace) :
    (∫ v, observedProduct s K F (ω, v) ∂unitMarksLaw) = clockMean s K F ω := by
  classical
  let f : ℕ → ℝ → ℂ := fun k x => if arrival ω (k + 1) ≤ s then
    F k (arrival ω (k + 1), x) else F k (s + 1, 0)
  have hf (k : ℕ) : Measurable (f k) := by
    by_cases hk : arrival ω (k + 1) ≤ s
    · simpa only [f, hk, if_true] using
        (hF k).comp (measurable_const.prodMk measurable_id)
    · simpa only [f, hk, if_false] using
        (measurable_const : Measurable (fun _ : ℝ => F k (s + 1, 0)))
  have h := integral_distinct_products (fun k : K => (k : ℕ)) Subtype.val_injective
    (fun k => f k) (fun k => hf k)
  have hprod (v : ℕ → ℝ) : (∏ k : K, f k (v k)) = observedProduct s K F (ω, v) := by
    rw [Finset.prod_coe_sort K (fun k => f k (v k))]
    simp only [observedProduct, stripView, apply_ite, f]
  rw [show (fun v => ∏ k : K, f k (v k)) = observedProduct s K F ∘ (fun v => (ω, v))
    from funext hprod] at h
  change (∫ v, observedProduct s K F (ω, v) ∂unitMarksLaw) = _ at h
  rw [h, Finset.prod_coe_sort K (fun k => ∫ x, f k x ∂uniformUnit)]
  apply Finset.prod_congr rfl
  intro k _
  by_cases hk : arrival ω (k + 1) ≤ s
  · simp only [f, hk, if_true]
  · simp only [f, hk, if_false]
    simp

theorem norm_clockMean_le_one (s : ℝ) (K : Finset ℕ) (F : ℕ → (ℝ × ℝ) → ℂ)
    (hbound : ∀ k p, ‖F k p‖ ≤ 1) (ω : ClockSpace) : ‖clockMean s K F ω‖ ≤ 1 := by
  apply (Finset.norm_prod_le _ _).trans
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro k _
  split_ifs
  · simpa using norm_integral_le_of_norm_le_const (μ := uniformUnit) (C := 1)
      (Eventually.of_forall (fun x => hbound k (arrival ω (k + 1), x)))
  · exact hbound k (s + 1, 0)

theorem integrable_clockMean (r : ℝ) (hr : 0 < r) (s : ℝ) (K : Finset ℕ)
    (F : ℕ → (ℝ × ℝ) → ℂ) (hF : ∀ k, Measurable (F k))
    (hbound : ∀ k p, ‖F k p‖ ≤ 1) :
    Integrable (clockMean s K F) (waitingTimeLaw r hr) := by
  exact (integrable_const (1 : ℝ)).mono'
    (measurable_clockMean s K F hF).aestronglyMeasurable
    (Eventually.of_forall (norm_clockMean_le_one s K F hbound))

/-- Fubini identifies the actual strip-cylinder expectation with its clock mean. -/
theorem integral_observedProduct (s : ℝ) (K : Finset ℕ) (F : ℕ → (ℝ × ℝ) → ℂ)
    (hF : ∀ k, Measurable (F k)) (hbound : ∀ k p, ‖F k p‖ ≤ 1) :
    (∫ ω, observedProduct s K F ω ∂stripLaw) =
      ∫ ω, clockMean s K F ω ∂waitingTimeLaw 1 (by norm_num) := by
  rw [stripLaw, integral_prod _ (integrable_observedProduct s K F hF hbound)]
  exact integral_congr_ae (Eventually.of_forall (integral_observedProduct_marks s K F hF))

/-- On a good clock, the observation uses exactly the indices below its past count. -/
theorem observedProduct_eq_censoredPast (s : ℝ) (hs : 0 ≤ s) (K : Finset ℕ)
    (F : ℕ → (ℝ × ℝ) → ℂ) (ω : ClockSpace)
    (hmono : StrictMono (arrival ω)) (hdiv : Tendsto (arrival ω) atTop atTop)
    (v : ℕ → ℝ) :
    observedProduct s K F (ω, v) = censoredPast K (proposalCount ω s)
      (fun k x => F k (arrival ω (k + 1), x)) (fun k => F k (s + 1, 0)) v := by
  simp only [observedProduct, stripView, apply_ite, censoredPast,
    arrival_le_iff_lt_proposalCount hmono hdiv s hs]

/-- Fixed-good-clock integration separates past observations from the future mark block. -/
theorem integral_observedProduct_future_marks (s t : ℝ) (hs : 0 ≤ s) (K : Finset ℕ)
    (F : ℕ → (ℝ × ℝ) → ℂ) (hF : ∀ k, Measurable (F k))
    (g : ℝ → ℂ) (hg : Measurable g) (ω : ClockSpace)
    (hmono : StrictMono (arrival ω)) (hdiv : Tendsto (arrival ω) atTop atTop) :
    (∫ v, observedProduct s K F (ω, v) *
      futureProduct (proposalCount ω s) (proposalCount ω (s + t)) g v ∂unitMarksLaw) =
      clockMean s K F ω * (∫ x, g x ∂uniformUnit) ^
        (proposalCount ω (s + t) - proposalCount ω s) := by
  simp_rw [observedProduct_eq_censoredPast s hs K F ω hmono hdiv]
  have hf (k : ℕ) : Measurable (fun x : ℝ => F k (arrival ω (k + 1), x)) :=
    (hF k).comp (measurable_const.prodMk measurable_id)
  rw [integral_censoredPast_future K (proposalCount ω s) (proposalCount ω (s + t))
    (fun k x => F k (arrival ω (k + 1), x)) hf (fun k => F k (s + 1, 0)) g hg]
  congr 1
  simp only [clockMean, arrival_le_iff_lt_proposalCount hmono hdiv s hs]

/-- The finite cylinder mean depends measurably on the actual augmented clock past. -/
theorem measurable_clockMean_augmentedPast (r : ℝ) (hr : 0 < r) (s : ℝ) (hs : 0 ≤ s)
    (K : Finset ℕ) (F : ℕ → (ℝ × ℝ) → ℂ) (hF : ∀ k, Measurable (F k)) :
    Measurable[ClockPastObservation.augmentedPast r hr s] (clockMean s K F) := by
  let H : ℕ → ℝ → ℂ := fun k y =>
    if y ≤ s then ∫ x, F k (y, x) ∂uniformUnit else F k (s + 1, 0)
  have hH (k : ℕ) : Measurable (H k) := by
    have hm : Measurable (fun y : ℝ => ∫ x, F k (y, x) ∂uniformUnit) :=
      (hF k).stronglyMeasurable.integral_prod_right'.measurable
    exact hm.ite measurableSet_Iic measurable_const
  have he : clockMean s K F = fun ω =>
      ∏ k ∈ K, H k (ClockPastObservation.censoredArrival s k ω) := by
    funext ω
    apply Finset.prod_congr rfl
    intro k _
    by_cases hk : arrival ω (k + 1) ≤ s
    · simp only [H, ClockPastObservation.censoredArrival, hk, if_true]
    · have hsent : ¬s + 1 ≤ s := by linarith
      simp only [H, ClockPastObservation.censoredArrival, hk, if_false, hsent]
  rw [he]
  exact Finset.measurable_prod _ (fun k _ => (hH k).comp
    (ClockPastObservation.measurable_censoredArrival_augmentedPast r hr s hs k))

end CarryingCapacity.MarkedObservation
