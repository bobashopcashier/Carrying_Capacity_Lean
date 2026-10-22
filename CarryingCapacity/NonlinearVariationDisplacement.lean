import CarryingCapacity.NonlinearPathVariation

/-!
# Actual path displacement is bounded by accepted weighted jump variation

The proved counting equations for the countable family of distance-to-state
tests hold simultaneously on one event. Subtracting their equations at two
times is legitimate because the actual signed counting integrals are
pathwise integrable. The reverse triangle inequality then bounds displacement
by the accepted weighted-jump integral. No displacement or variation bound is
assumed, and all interval endpoints share the same probability-one event.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.NonlinearVariationDisplacement
open CommonInitialNoise NonlinearPathVariation DeterministicEnvironmentLyapunov

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)

local notation "v" => NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment
local notation "hv" => Continuous.continuousOn (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment)
local notation "X" => NonlinearFixedPoint.process control hActivity ν T hT hCoupling hMoment
local notation "Z" => NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment

private def signedWindow (f : State D → ℝ) (j : Jump D) (s t : ℝ)
    (w : Sample (State D) (Jump D) × (ℝ × ℝ)) : ℝ :=
  if w.2.1 ∈ Ioc s t ∧ w.2.2 ≤ DeterministicEnvironmentFrozen.timeRate κ q v T j w.2.1
      (Z w.1 w.2.1)
  then f (Jump.advance j (Z w.1 w.2.1)) - f (Z w.1 w.2.1) else 0

private theorem signedWindow_zero_eq_horizon (f : State D → ℝ) (j : Jump D) (t : ℝ)
    (p : Sample (State D) (Jump D)) (z : ℝ × ℝ) :
    signedWindow control hActivity ν T hT hCoupling hMoment f j 0 t (p,z) =
      DeterministicEnvironmentProcess.horizonIncrement control hActivity v T hT hv id f j t (p,z) :=
  (TimeDependentGlobalCounting.horizonIncrement_apply _ _ _ _ _ _ _ _ _ _ _ _).symm

private theorem signedWindow_eq_sub (f : State D → ℝ) (j : Jump D) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) (w : Sample (State D) (Jump D) × (ℝ × ℝ)) :
    signedWindow control hActivity ν T hT hCoupling hMoment f j s t w =
      signedWindow control hActivity ν T hT hCoupling hMoment f j 0 t w -
        signedWindow control hActivity ν T hT hCoupling hMoment f j 0 s w := by
  unfold signedWindow
  by_cases hrate : w.2.2 ≤ DeterministicEnvironmentFrozen.timeRate κ q v T j w.2.1 (Z w.1 w.2.1)
  · simp only [hrate, and_true]
    by_cases hws : w.2.1 ≤ s
    · have hn : ¬ s < w.2.1 := not_lt_of_ge hws
      have hwt := hws.trans hst
      simp only [mem_Ioc, hn, false_and, hws, hwt, and_true, ↓reduceIte, sub_self]
    · have hsw : s < w.2.1 := lt_of_not_ge hws
      have hw0 : 0 < w.2.1 := hs.trans_lt hsw
      simp only [mem_Ioc, hsw, hw0, true_and, hws, and_false, ↓reduceIte, sub_zero]
  · simp only [hrate, and_false, ↓reduceIte, sub_zero]

private theorem abs_distance_test_increment_le (a x y : State D) :
    |adaptedDistance κ x a - adaptedDistance κ y a| ≤ adaptedDistance κ x y := by
  apply abs_le.mpr
  constructor
  · have h := adaptedDistance_triangle κ y x a
    rw [adaptedDistance_symm κ y x] at h
    linarith
  · linarith [adaptedDistance_triangle κ x y a]

private theorem signedWindow_norm_le_weight (a : State D) (j : Jump D) (s u t : ℝ)
    (hut : u ≤ t) (w : Sample (State D) (Jump D) × (ℝ × ℝ)) :
    ENNReal.ofReal |signedWindow control hActivity ν T hT hCoupling hMoment
      (fun x => adaptedDistance κ x a) j s u w| ≤
        acceptedWeight control hActivity ν T hT hCoupling hMoment j s t w := by
  unfold signedWindow acceptedWeight NonlinearPathVariation.rate
  by_cases h : w.2.1 ∈ Ioc s u ∧
      w.2.2 ≤ DeterministicEnvironmentFrozen.timeRate κ q v T j w.2.1 (Z w.1 w.2.1)
  · have ht : w.2.1 ∈ Ioc s t ∧
        w.2.2 ≤ DeterministicEnvironmentFrozen.timeRate κ q v T j w.2.1 (Z w.1 w.2.1) :=
      ⟨⟨h.1.1, h.1.2.trans hut⟩, h.2⟩
    simp only [if_pos h, if_pos ht]
    exact ENNReal.ofReal_le_ofReal (abs_distance_test_increment_le a _ _)
  · simp only [if_neg h, abs_zero, ENNReal.ofReal_zero, zero_le]

/-- On one event, every pair of nonnegative times in the construction
interval satisfies the actual displacement bound. The right endpoint can
be any intermediate time in the variation interval. -/
theorem ae_distance_le_variation :
    ∀ᵐ p ∂law ν.measure (Jump D), ∀ s u t : ℝ,
      0 ≤ s → s ≤ u → u ≤ t → t ≤ T →
        ENNReal.ofReal (adaptedDistance κ (X p u) (X p s)) ≤
          variation control hActivity ν T hT hCoupling hMoment s t p := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  let B := manuscriptBound control ν (driftConstant control) T
  have hB : 0 ≤ B := manuscriptBound_nonnegative control ν (driftConstant control) T
    (driftConstant_nonnegative control) hT
  have hEnv : ∀ s ∈ Icc 0 T,
      LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B :=
    fun s _ => manuscriptExtension_bound control ν (driftConstant control) T
      (driftConstant_nonnegative control) hT
      (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hMoment) s
  have hi := DeterministicEnvironmentProcess.ae_integrable_horizonIncrement control hActivity
    v T hT hv id ν.measure hCoupling measurable_id B hB hEnv hMoment
  have he : ∀ᵐ p ∂law ν.measure (Jump D), ∀ a : State D, ∀ S : ℝ≥0,
      adaptedDistance κ (X p S) a - adaptedDistance κ p.1 a =
        ∑ j, ∫ z, signedWindow control hActivity ν T hT hCoupling hMoment
          (fun x => adaptedDistance κ x a) j 0 S (p,z) ∂MarkedNoise.countingMeasure j p.2 := by
    apply ae_all_iff.mpr
    intro a
    filter_upwards [DeterministicEnvironmentProcess.ae_counting_identity control hActivity
      v T hT hv id ν.measure hCoupling measurable_id B hB hEnv hMoment
      (fun x => adaptedDistance κ x a)] with p hp
    intro S
    simpa only [signedWindow_zero_eq_horizon] using hp S
  filter_upwards [hi, he] with p hi he
  intro s u t hs hsu hut _
  let f : State D → ℝ := fun x => adaptedDistance κ x (X p s)
  let W : Jump D → (ℝ × ℝ) → ℝ := fun j z =>
    signedWindow control hActivity ν T hT hCoupling hMoment f j s u (p,z)
  have hW (j : Jump D) :
      (∫ z, W j z ∂MarkedNoise.countingMeasure j p.2) =
        (∫ z, signedWindow control hActivity ν T hT hCoupling hMoment f j 0 u (p,z)
          ∂MarkedNoise.countingMeasure j p.2) -
        (∫ z, signedWindow control hActivity ν T hT hCoupling hMoment f j 0 s (p,z)
          ∂MarkedNoise.countingMeasure j p.2) := by
    have his : Integrable (fun z => signedWindow control hActivity ν T hT hCoupling hMoment
        f j 0 s (p,z)) (MarkedNoise.countingMeasure j p.2) := by
      simpa only [signedWindow_zero_eq_horizon] using hi ⟨s, hs⟩ f j
    have hiu : Integrable (fun z => signedWindow control hActivity ν T hT hCoupling hMoment
        f j 0 u (p,z)) (MarkedNoise.countingMeasure j p.2) := by
      simpa only [signedWindow_zero_eq_horizon] using hi ⟨u, hs.trans hsu⟩ f j
    calc
      _ = ∫ z, signedWindow control hActivity ν T hT hCoupling hMoment f j 0 u (p,z) -
          signedWindow control hActivity ν T hT hCoupling hMoment f j 0 s (p,z)
            ∂MarkedNoise.countingMeasure j p.2 := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => signedWindow_eq_sub control hActivity ν T hT
          hCoupling hMoment f j s u hs hsu (p,z))
      _ = _ := integral_sub hiu his
  have hid : adaptedDistance κ (X p u) (X p s) =
      ∑ j, ∫ z, W j z ∂MarkedNoise.countingMeasure j p.2 := by
    simp_rw [hW]
    rw [Finset.sum_sub_distrib]
    have hu := he (X p s) ⟨u, hs.trans hsu⟩
    have hs' := he (X p s) ⟨s, hs⟩
    simp only [NNReal.coe_mk] at hu hs'
    dsimp only [f]
    rw [← hu, ← hs', adaptedDistance_self]
    ring
  calc
    _ = ENNReal.ofReal |∑ j, ∫ z, W j z ∂MarkedNoise.countingMeasure j p.2| := by
      rw [← hid, abs_of_nonneg (adaptedDistance_nonneg κ _ _)]
    _ ≤ ENNReal.ofReal (∑ j, |∫ z, W j z ∂MarkedNoise.countingMeasure j p.2|) :=
      ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ j, ENNReal.ofReal |∫ z, W j z ∂MarkedNoise.countingMeasure j p.2| :=
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)
    _ ≤ ∑ j, ∫⁻ z, ENNReal.ofReal |W j z| ∂MarkedNoise.countingMeasure j p.2 := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [← ofReal_norm_eq_enorm, Real.norm_eq_abs] using
        enorm_integral_le_lintegral_enorm (W j)
    _ ≤ variation control hActivity ν T hT hCoupling hMoment s t p := by
      apply Finset.sum_le_sum
      intro j _
      exact lintegral_mono (fun z => signedWindow_norm_le_weight control hActivity ν T hT
        hCoupling hMoment (X p s) j s u t hut (p,z))

end CarryingCapacity.NonlinearVariationDisplacement
