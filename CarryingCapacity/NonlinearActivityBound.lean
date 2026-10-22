import CarryingCapacity.NonlinearFixedPoint

/-!
# Expected weighted activity of the actual nonlinear process

The activity hypothesis and a genuine finite moment imply integrability of
weighted jump activity under any moment law. The canonical nonlinear process
has exactly its nonlinear environment as its marginal on the construction
interval. Its activity expectation is therefore bounded by the manuscript's
activity constant times the square of one plus the terminal moment envelope.
No expected activity or variation estimate is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.NonlinearActivityBound
open CommonInitialNoise DeterministicEnvironmentRates DeterministicEnvironmentLyapunov

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}

theorem weightedActivity_nonnegative (x : State D) (μ : MomentLaw κ D) :
    0 ≤ weightedActivity κ q x μ :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (q.nonnegative j x μ) (adaptedDistance_nonneg κ _ _))

variable (hActivity : MomentActivityBound κ q)
include hActivity

/-- The ordinary activity integral is genuine, by domination with a finite
moment rather than by assigning a value to a divergent integral. -/
theorem integrable_weightedActivity (μ : MomentLaw κ D) :
    Integrable (fun x => weightedActivity κ q x μ) μ.measure := by
  letI : IsProbabilityMeasure μ.measure := μ.probability
  have hi : Integrable (fun x => activityConstant κ q hActivity *
      (1 + momentWeight κ x) * (1 + moment μ)) μ.measure :=
    (((integrable_const (1 : ℝ)).add μ.integrable_weight).const_mul _).mul_const _
  apply hi.mono' (measurable_of_countable _).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (weightedActivity_nonnegative x μ)]
    exact (Classical.choose_spec hActivity).2 x μ)

/-- Exact integration of the affine state-moment bound gives a quadratic
bound in the law's own moment. -/
theorem integral_weightedActivity_le (μ : MomentLaw κ D) :
    (∫ x, weightedActivity κ q x μ ∂μ.measure) ≤
      activityConstant κ q hActivity * (1 + moment μ) ^ 2 := by
  letI : IsProbabilityMeasure μ.measure := μ.probability
  have hi : Integrable (fun x => activityConstant κ q hActivity *
      (1 + momentWeight κ x) * (1 + moment μ)) μ.measure :=
    (((integrable_const (1 : ℝ)).add μ.integrable_weight).const_mul _).mul_const _
  calc
    _ ≤ ∫ x, activityConstant κ q hActivity * (1 + momentWeight κ x) *
        (1 + moment μ) ∂μ.measure :=
      integral_mono (integrable_weightedActivity hActivity μ) hi
        (fun x => (Classical.choose_spec hActivity).2 x μ)
    _ = _ := by
      rw [integral_mul_const, integral_const_mul,
        integral_add (integrable_const (1 : ℝ)) μ.integrable_weight]
      simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul, moment]
      ring

variable (control : LyapunovControl κ q) (ν : MomentLaw κ D) (T : ℝ)

/-- The explicit population-independent coefficient in the expected interval
variation estimate. -/
def variationConstant : ℝ :=
  activityConstant κ q hActivity *
    (1 + manuscriptBound control ν (driftConstant control) T) ^ 2

theorem variationConstant_nonnegative : 0 ≤ variationConstant hActivity control ν T := by
  unfold variationConstant
  exact mul_nonneg (activityConstant_nonnegative κ q hActivity) (sq_nonneg _)

variable (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)

local notation "v" => NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment
local notation "X" => NonlinearFixedPoint.process control hActivity ν T hT hCoupling hMoment
local notation "K" => manuscriptBound control ν (driftConstant control) T

/-- Every value of the actual fixed environment has the required adapted
moment bound, including the endpoint-held extension. -/
theorem environment_moment_le (r : ℝ) : moment (v r) ≤ K := by
  have hb := manuscriptExtension_integrable_and_bound control ν (driftConstant control) T
    (driftConstant_nonnegative control) hT
    (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hMoment) r
  exact (integral_mono (v r).integrable_weight hb.1
    (fun x => by linarith [control.dominates x])).trans hb.2

/-- The weighted activity along the actual nonlinear path is integrable at
every time in the construction interval. -/
theorem integrable_currentActivity (r : ℝ) (hr : r ∈ Icc 0 T) :
    Integrable (fun p => weightedActivity κ q (X p r) (v r))
      (law ν.measure (Jump D)) := by
  have hi := integrable_weightedActivity hActivity (v r)
  rw [NonlinearFixedPoint.environment_measure_eq_marginal control hActivity ν T hT hCoupling hMoment ⟨r,hr⟩] at hi
  exact hi.comp_measurable
    (NonlinearFixedPoint.measurable_process control hActivity ν T hT hCoupling hMoment).of_uncurry_right

/-- The manuscript's uniform expected weighted-activity bound, derived from
the actual marginal identity and its Lyapunov envelope. -/
theorem integral_currentActivity_le (r : ℝ) (hr : r ∈ Icc 0 T) :
    (∫ p, weightedActivity κ q (X p r) (v r) ∂law ν.measure (Jump D)) ≤
      variationConstant hActivity control ν T := by
  have he : (∫ p, weightedActivity κ q (X p r) (v r) ∂law ν.measure (Jump D)) =
      ∫ x, weightedActivity κ q x (v r) ∂(v r).measure := by
    have hx : Measurable (fun p => X p r) :=
      (NonlinearFixedPoint.measurable_process control hActivity ν T hT hCoupling hMoment).of_uncurry_right
    rw [NonlinearFixedPoint.environment_measure_eq_marginal control hActivity ν T hT hCoupling hMoment ⟨r,hr⟩]
    exact (integral_map_of_stronglyMeasurable hx
      (measurable_of_countable (fun x => weightedActivity κ q x (v r))).stronglyMeasurable).symm
  rw [he]
  apply (integral_weightedActivity_le hActivity (v r)).trans
  apply mul_le_mul_of_nonneg_left _ (activityConstant_nonnegative κ q hActivity)
  exact pow_le_pow_left₀ (by linarith [moment_nonneg (v r)])
    (add_le_add_left (environment_moment_le hActivity control ν T hT hCoupling hMoment r) 1) 2

/-- The same bound in extended nonnegative expectations, with genuine
integrability established before conversion. -/
theorem lintegral_currentActivity_le (r : ℝ) (hr : r ∈ Icc 0 T) :
    (∫⁻ p, ENNReal.ofReal (weightedActivity κ q (X p r) (v r))
      ∂law ν.measure (Jump D)) ≤ ENNReal.ofReal (variationConstant hActivity control ν T) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_currentActivity hActivity control ν T hT hCoupling hMoment r hr)
    (Eventually.of_forall (fun p => weightedActivity_nonnegative (X p r) (v r)))]
  exact ENNReal.ofReal_le_ofReal (integral_currentActivity_le hActivity control ν T hT hCoupling hMoment r hr)

end CarryingCapacity.NonlinearActivityBound
