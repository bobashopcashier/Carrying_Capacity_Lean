import CarryingCapacity.FrozenProcess

/-!
# Distributional facts for the constructed exponential clock

These are genuine probability identities for the canonical exponential
construction. They establish memorylessness and the zero-count Poisson
probability. The complete Poisson count distribution, independent increments,
and compensator are not asserted here.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace CarryingCapacity.PoissonClockLaw
open CountableJumpProcess FrozenProcess

/-- The exponential survival probabilities multiply over successive intervals. -/
theorem survival_add (r : ℝ) (hr : 0 < r) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    expMeasure r (Ioi (s + t)) = expMeasure r (Ioi s) * expMeasure r (Ioi t) := by
  rw [exponential_survival r hr (s + t) (add_nonneg hs ht),
    exponential_survival r hr s hs, exponential_survival r hr t ht]
  rw [show -(r * (s + t)) = -(r * s) + -(r * t) by ring, Real.exp_add,
    ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]

/-- Conditioning on survival to s gives the same survival probability for a
further t units. The conditioning measure is mathlib's normalized restriction. -/
theorem exponential_memoryless (r : ℝ) (hr : 0 < r) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (ProbabilityTheory.cond (expMeasure r) (Ioi s)) (Ioi (s + t)) =
      expMeasure r (Ioi t) := by
  letI := isProbabilityMeasureExponential hr
  rw [ProbabilityTheory.cond_apply measurableSet_Ioi, Ioi_inter_Ioi,
    max_eq_right (by linarith : s ≤ s + t), survival_add r hr s t hs ht,
    ← mul_assoc]
  have hne : expMeasure r (Ioi s) ≠ 0 := by
    rw [exponential_survival r hr s hs]
    positivity
  rw [ENNReal.inv_mul_cancel hne (measure_ne_top _ _), one_mul]

/-- Exponential waiting times exceed every nonpositive threshold almost surely. -/
theorem exponential_survival_nonpos (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : t ≤ 0) :
    expMeasure r (Ioi t) = 1 := by
  letI := isProbabilityMeasureExponential hr
  rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _),
    measure_univ, ← ofReal_cdf (expMeasure r) t]
  change 1 - ENNReal.ofReal (exponentialCDFReal r t) = 1
  rw [exponentialCDFReal_eq hr t]
  by_cases h : 0 ≤ t
  · have heq : t = 0 := le_antisymm ht h
    simp [heq]
  · simp [h]

/-- Survival of the residual waiting time, including negative thresholds. -/
theorem conditional_residual_survival (r : ℝ) (hr : 0 < r) (s : ℝ) (hs : 0 ≤ s)
    (t : ℝ) :
    (ProbabilityTheory.cond (expMeasure r) (Ioi s)) {x | t < x - s} =
      expMeasure r (Ioi t) := by
  letI := isProbabilityMeasureExponential hr
  have heq : {x : ℝ | t < x - s} = Ioi (s + t) := by
    ext x
    simp only [mem_setOf_eq, mem_Ioi]
    constructor <;> intro h <;> linarith
  rw [heq]
  by_cases ht : 0 ≤ t
  · exact exponential_memoryless r hr s t hs ht
  · rw [exponential_survival_nonpos r hr t (le_of_not_ge ht),
      ProbabilityTheory.cond_apply measurableSet_Ioi, Ioi_inter_Ioi,
      max_eq_left (by linarith : s + t ≤ s)]
    apply ENNReal.inv_mul_cancel
    · rw [exponential_survival r hr s hs]
      positivity
    · exact measure_ne_top _ _

/-- Full measure-valued memorylessness: the law of `X-s` conditional on `X>s`
is exactly the original exponential law. This is stronger than matching one
nonnegative survival probability. -/
theorem conditional_residual_law (r : ℝ) (hr : 0 < r) (s : ℝ) (hs : 0 ≤ s) :
    Measure.map (fun x : ℝ => x - s)
      (ProbabilityTheory.cond (expMeasure r) (Ioi s)) = expMeasure r := by
  letI := isProbabilityMeasureExponential hr
  have hne : expMeasure r (Ioi s) ≠ 0 := by
    rw [exponential_survival r hr s hs]
    positivity
  letI := ProbabilityTheory.cond_isProbabilityMeasure hne
  let μ := Measure.map (fun x : ℝ => x - s)
    (ProbabilityTheory.cond (expMeasure r) (Ioi s))
  have hm : Measurable (fun x : ℝ => x - s) := measurable_id.sub_const s
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_map hm.aemeasurable
  apply Measure.ext_of_Iic
  intro t
  have htail : μ (Ioi t) = expMeasure r (Ioi t) := by
    dsimp only [μ]
    rw [Measure.map_apply hm measurableSet_Ioi]
    exact conditional_residual_survival r hr s hs t
  change μ (Iic t) = expMeasure r (Iic t)
  calc
    μ (Iic t) = 1 - μ (Ioi t) := by
      rw [← compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top _ _), measure_univ]
    _ = 1 - expMeasure r (Ioi t) := by rw [htail]
    _ = expMeasure r (Iic t) := by
      rw [← compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top _ _), measure_univ]

/-- On a strictly increasing locally finite clock, zero proposals before t is
exactly the event that the first waiting time exceeds t. -/
theorem proposalCount_eq_zero_iff {ω : ClockSpace}
    (hmono : StrictMono (arrival ω))
    (hfin : ∀ T : ℝ, {n : ℕ | arrival ω n ≤ T}.Finite) (t : ℝ) :
    proposalCount ω t = 0 ↔ t < ω 0 := by
  have hf : {n : ℕ | arrival ω (n + 1) ≤ t}.Finite :=
    Set.Finite.preimage (f := fun n : ℕ => n + 1)
      (fun _ _ _ _ h => Nat.succ_injective h) (hfin t)
  rw [proposalCount, Set.ncard_eq_zero hf, Set.eq_empty_iff_forall_not_mem]
  constructor
  · intro h
    have hn := h 0
    simpa only [Nat.zero_add, arrival_succ, arrival_zero, zero_add,
      mem_setOf_eq, not_le] using hn
  · intro h n hn
    have ha : ω 0 ≤ arrival ω (n + 1) := by
      have hh := hmono.monotone (show 1 ≤ n + 1 by omega)
      simpa only [arrival_succ, arrival_zero, zero_add] using hh
    exact (not_lt_of_ge hn) (h.trans_le ha)

/-- The zero-count probability has the Poisson value exp(-r*t), derived from
the actual construction rather than placed in a counting-process structure. -/
theorem probability_zero_proposals (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : 0 ≤ t) :
    waitingTimeLaw r hr {ω | proposalCount ω t = 0} = ENNReal.ofReal (Real.exp (-(r * t))) := by
  have heq : {ω : ClockSpace | proposalCount ω t = 0} =ᵐ[waitingTimeLaw r hr]
      {ω : ClockSpace | t < ω 0} := by
    filter_upwards [ae_locally_finite r hr] with ω hω
    exact propext (proposalCount_eq_zero_iff hω.1 hω.2 t)
  rw [measure_congr heq]
  have hmap := coordinate_map r hr 0
  have h := congrArg (fun μ : Measure ℝ => μ (Ioi t)) hmap
  dsimp only at h
  rw [Measure.map_apply (measurable_pi_apply 0) measurableSet_Ioi] at h
  exact h.trans (exponential_survival r hr t ht)

end CarryingCapacity.PoissonClockLaw
