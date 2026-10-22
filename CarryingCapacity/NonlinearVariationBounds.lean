import CarryingCapacity.NonlinearActivityBound
import CarryingCapacity.NonlinearVariationDisplacement

/-!
# Integrable jump variation and the nonlinear law's time modulus

Actual predictable compensation and the actual nonlinear marginal activity
bound give a finite expected variation proportional to the interval length.
Integrability and displacement domination follow, and the same-path coupling
then proves the law's Wasserstein time modulus. No variation estimate or
integrability premise is supplied.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.NonlinearVariationBounds
open CommonInitialNoise NonlinearPathVariation

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)

local notation "v" => NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment
local notation "X" => NonlinearFixedPoint.process control hActivity ν T hT hCoupling hMoment
local notation "V" => variation control hActivity ν T hT hCoupling hMoment
local notation "C" => NonlinearActivityBound.variationConstant hActivity control ν T

/-- The real version of the genuine accepted weighted jump variation. -/
def variationReal (s t : ℝ) (p : Sample (State D) (Jump D)) : ℝ := (V s t p).toReal

theorem variationReal_nonnegative (s t : ℝ) (p : Sample (State D) (Jump D)) :
    0 ≤ variationReal control hActivity ν T hT hCoupling hMoment s t p :=
  ENNReal.toReal_nonneg

theorem measurable_variationReal (s t : ℝ) (hs : 0 ≤ s) :
    Measurable (variationReal control hActivity ν T hT hCoupling hMoment s t) :=
  (measurable_variation control hActivity ν T hT hCoupling hMoment s t hs).ennreal_toReal

/-- Expected variation is bounded by the activity coefficient times the
length of the actual interval, including jumps at its right endpoint. -/
theorem expected_variation_le (s t : ℝ) (hs : 0 ≤ s) (ht : t ≤ T) :
    (∫⁻ p, V s t p ∂law ν.measure (Jump D)) ≤ ENNReal.ofReal (C * (t-s)) := by
  rw [expected_variation_eq control hActivity ν T hT hCoupling hMoment s t hs ht]
  calc
    _ ≤ ∫⁻ _r in Ioc s t, ENNReal.ofReal C := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact NonlinearActivityBound.lintegral_currentActivity_le hActivity control ν T hT
        hCoupling hMoment r ⟨hs.trans hr.1.le, hr.2.trans ht⟩
    _ = _ := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
      rw [ENNReal.ofReal_mul
        (NonlinearActivityBound.variationConstant_nonnegative hActivity control ν T)]

theorem lintegral_variation_lt_top (s t : ℝ) (hs : 0 ≤ s) (ht : t ≤ T) :
    (∫⁻ p, V s t p ∂law ν.measure (Jump D)) < ⊤ :=
  lt_of_le_of_lt
    (expected_variation_le control hActivity ν T hT hCoupling hMoment s t hs ht)
    ENNReal.ofReal_lt_top

theorem ae_variation_lt_top (s t : ℝ) (hs : 0 ≤ s) (ht : t ≤ T) :
    ∀ᵐ p ∂law ν.measure (Jump D), V s t p < ⊤ :=
  ae_lt_top' (measurable_variation control hActivity ν T hT hCoupling hMoment s t hs).aemeasurable
    (lintegral_variation_lt_top control hActivity ν T hT hCoupling hMoment s t hs ht).ne

/-- Ordinary integrability follows from finite extended expectation. -/
theorem integrable_variationReal (s t : ℝ) (hs : 0 ≤ s) (_hst : s ≤ t) (ht : t ≤ T) :
    Integrable (variationReal control hActivity ν T hT hCoupling hMoment s t)
      (law ν.measure (Jump D)) :=
  integrable_toReal_of_lintegral_ne_top
    (measurable_variation control hActivity ν T hT hCoupling hMoment s t hs).aemeasurable
    (lintegral_variation_lt_top control hActivity ν T hT hCoupling hMoment s t hs ht).ne

theorem integral_variationReal_le (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    (∫ p, variationReal control hActivity ν T hT hCoupling hMoment s t p
      ∂law ν.measure (Jump D)) ≤ C * (t-s) := by
  unfold variationReal
  rw [integral_toReal
    (measurable_variation control hActivity ν T hT hCoupling hMoment s t hs).aemeasurable
    (ae_variation_lt_top control hActivity ν T hT hCoupling hMoment s t hs ht)]
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (expected_variation_le control hActivity ν T hT hCoupling hMoment s t hs ht)
  simpa only [ENNReal.toReal_ofReal (mul_nonneg
    (NonlinearActivityBound.variationConstant_nonnegative hActivity control ν T)
    (sub_nonneg.mpr hst))] using hb

/-- For a fixed cell, the real integrable variation bounds displacement
at every time of that cell on one event. -/
theorem ae_distance_le_variationReal (s t : ℝ) (hs : 0 ≤ s) (ht : t ≤ T) :
    ∀ᵐ p ∂law ν.measure (Jump D), ∀ u ∈ Icc s t,
      adaptedDistance κ (X p u) (X p s) ≤
        variationReal control hActivity ν T hT hCoupling hMoment s t p := by
  filter_upwards [ae_variation_lt_top control hActivity ν T hT hCoupling hMoment s t hs ht,
    NonlinearVariationDisplacement.ae_distance_le_variation control hActivity ν T hT hCoupling hMoment]
    with p hp hd
  intro u hu
  have hb := ENNReal.toReal_mono hp.ne (hd s u t hs hu.1 hu.2 ht)
  simpa only [ENNReal.toReal_ofReal (adaptedDistance_nonneg κ _ _)] using hb

/-- The exact same-path endpoint coupling gives a linear Wasserstein
modulus for the genuine nonlinear environment. -/
theorem wasserstein_environment_le (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    wasserstein (v s) (v t) ≤ C * (t-s) := by
  have hx (r : ℝ) : Measurable (fun p => X p r) :=
    (NonlinearFixedPoint.measurable_process control hActivity ν T hT hCoupling hMoment).of_uncurry_right
  have hd : AEStronglyMeasurable (fun p => adaptedDistance κ (X p t) (X p s))
      (law ν.measure (Jump D)) :=
    ((measurable_of_countable (fun z : State D × State D => adaptedDistance κ z.1 z.2)).comp
      ((hx t).prodMk (hx s))).aestronglyMeasurable
  have hb : ∀ᵐ p ∂law ν.measure (Jump D), adaptedDistance κ (X p t) (X p s) ≤
      variationReal control hActivity ν T hT hCoupling hMoment s t p := by
    filter_upwards [ae_distance_le_variationReal control hActivity ν T hT hCoupling hMoment s t hs ht]
      with p hp
    exact hp t ⟨hst, le_rfl⟩
  have hi := integrable_variationReal control hActivity ν T hT hCoupling hMoment s t hs hst ht
  have hdist : Integrable (fun p => adaptedDistance κ (X p t) (X p s))
      (law ν.measure (Jump D)) := by
    apply hi.mono' hd
    filter_upwards [hb] with p hp
    simpa only [Real.norm_of_nonneg (adaptedDistance_nonneg κ _ _)] using hp
  rw [wasserstein_symm]
  apply (LawCurveContinuity.wasserstein_le_integral_distance (law ν.measure (Jump D))
    (fun p => X p t) (fun p => X p s) (hx t) (hx s) (v t) (v s)
    (NonlinearFixedPoint.environment_measure_eq_marginal control hActivity ν T hT hCoupling hMoment
      ⟨t, ⟨hs.trans hst, ht⟩⟩).symm
    (NonlinearFixedPoint.environment_measure_eq_marginal control hActivity ν T hT hCoupling hMoment
      ⟨s, ⟨hs, hst.trans ht⟩⟩).symm).trans
  exact (integral_mono_ae hdist hi hb).trans
    (integral_variationReal_le control hActivity ν T hT hCoupling hMoment s t hs hst ht)

end CarryingCapacity.NonlinearVariationBounds
