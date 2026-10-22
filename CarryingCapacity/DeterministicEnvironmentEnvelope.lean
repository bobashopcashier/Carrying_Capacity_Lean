import CarryingCapacity.DeterministicEnvironmentProcess
import CarryingCapacity.DeterministicEnvironmentLaw
import CarryingCapacity.TimeDependentGlobalComparison

/-!
# Preservation of the manuscript Lyapunov envelope

The explicit exponential envelope solves its scalar integral equation by the
fundamental theorem of calculus. For every prescribed curve in the manuscript
space, the actual nonexplosive common-noise process retains this same envelope
on the construction horizon. Initial integrability, coarse nonexplosion, and
the sharper pointwise generator bound all follow from the paper's assumptions.

This proves the moment component of an invariant evolution map. It does not
assert continuity of the resulting law curve or construct a nonlinear fixed
point.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace CarryingCapacity.DeterministicEnvironmentEnvelope
open CommonInitialNoise LyapunovFlowSpace DeterministicEnvironmentLyapunov
open DeterministicEnvironmentProcess DeterministicEnvironmentFrozen

/-- The manuscript envelope has exactly the scalar derivative used by the
Lyapunov comparison, including when its drift constant is zero. -/
theorem hasDerivAt_exponentialEnvelope (m c t : ℝ) :
    HasDerivAt (exponentialEnvelope m c) (c * (1 + 2 * exponentialEnvelope m c t)) t := by
  have hd := ((((hasDerivAt_id t).const_mul (2 * c)).exp).const_mul (m + 1 / 2)).sub_const (1 / 2)
  convert hd using 1
  simp only [exponentialEnvelope, ContinuousMap.coe_mk, id_eq]
  ring

/-- The deterministic scalar supersolution premise is proved directly from
the stated exponential formula, rather than assumed for the process. -/
theorem exponentialEnvelope_integral_eq (m c t : ℝ) (ht : 0 ≤ t) :
    m + ∫ s in Ioc 0 t, c * (1 + 2 * exponentialEnvelope m c s) =
      exponentialEnvelope m c t := by
  have hi : IntervalIntegrable (fun s => c * (1 + 2 * exponentialEnvelope m c s)) volume 0 t :=
    (continuous_const.mul (continuous_const.add
      (continuous_const.mul (exponentialEnvelope m c).continuous))).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_exponentialEnvelope m c s) hi
  rw [intervalIntegral.integral_of_le ht, exponentialEnvelope_zero] at he
  linarith

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T)
  (v : ManuscriptCurves control.function ν (driftConstant control) T hT)
  (hCoupling : MomentCouplingBound κ q)
include hCoupling

/-- The actual prescribed-environment process retains the same Lyapunov
envelope that defines the input curve space. Both integral notions are genuine:
integrability is proved and the nonnegative extended integral is bounded. -/
theorem manuscript_moment_bounds (t : ℝ) (ht : t ∈ Icc 0 T) :
    Integrable (fun p => control.function (manuscriptProcess control hActivity ν T hT v p t))
      (law ν.measure (Jump D)) ∧
    (∫ p, control.function (manuscriptProcess control hActivity ν T hT v p t)
      ∂law ν.measure (Jump D)) ≤
      exponentialEnvelope (∫ x, control.function x ∂ν.measure) (driftConstant control) t ∧
    (∫⁻ p, ENNReal.ofReal (control.function (manuscriptProcess control hActivity ν T hT v p t))
      ∂law ν.measure (Jump D)) ≤
      ENNReal.ofReal (exponentialEnvelope (∫ x, control.function x ∂ν.measure)
        (driftConstant control) t) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  apply TimeDependentGlobalComparison.bounds_of_manuscript_envelope control.function
    (finite_sublevels control) Jump.advance
    (timeRate κ q (manuscriptExtension control ν (driftConstant control) T hT v) T)
    (exists_uniform_rate_bounds control _ T hT hActivity
      (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn)
    id 0 ν.measure (manuscript_measurable_timeRate control hCoupling ν (driftConstant control) T hT v)
    measurable_id (affineConstant control (manuscriptBound control ν (driftConstant control) T))
    (affineConstant_nonnegative control _ (manuscriptBound_nonnegative control ν
      (driftConstant control) T (driftConstant_nonnegative control) hT))
    (function_nonnegative control) (fun x j s _ => timeRate_nonnegative κ q _ T j s x)
    (manuscript_initial_integrable control ν T hT v)
    (fun x s _ => manuscript_generator_affine_bound control ν (driftConstant control) T
      (driftConstant_nonnegative control) hT v s x)
    (driftConstant control) (driftConstant_nonnegative control)
    (exponentialEnvelope (∫ x, control.function x ∂ν.measure) (driftConstant control)) T hT
    (exponentialEnvelope _ _).continuous.continuousOn
    (fun s hs => (integral_nonneg (function_nonnegative control)).trans
      (le_exponentialEnvelope (integral_nonneg (function_nonnegative control))
        (driftConstant_nonnegative control) hs.1))
    (fun s hs x => manuscript_generator_envelope_bound control ν (driftConstant control) T
      (driftConstant_nonnegative control) hT v s hs x)
    (fun s hs => (exponentialEnvelope_integral_eq _ _ s hs.1).le) t ht

/-- The actual finite-moment output law satisfies exactly the extended
Lyapunov constraint defining the manuscript's candidate curve space. -/
theorem lyapunovIntegral_outputLaw_le (t : ℝ≥0) (ht : (t : ℝ) ≤ T) :
    lyapunovIntegral control.function
      (DeterministicEnvironmentLaw.outputLaw control hActivity ν T hT v hCoupling t) ≤
      ENNReal.ofReal (exponentialEnvelope (∫ x, control.function x ∂ν.measure)
        (driftConstant control) t) := by
  rw [DeterministicEnvironmentLaw.lyapunovIntegral_outputLaw]
  exact (manuscript_moment_bounds control hActivity ν T hT v hCoupling t ⟨t.coe_nonneg, ht⟩).2.2

/-- The corresponding ordinary integral bound for the actual output law;
its Lyapunov integrability is independently proved in the law construction. -/
theorem integral_outputLaw_le (t : ℝ≥0) (ht : (t : ℝ) ≤ T) :
    (∫ x, control.function x
      ∂(DeterministicEnvironmentLaw.outputLaw control hActivity ν T hT v hCoupling t).measure) ≤
      exponentialEnvelope (∫ x, control.function x ∂ν.measure) (driftConstant control) t := by
  rw [DeterministicEnvironmentLaw.integral_outputLaw]
  exact (manuscript_moment_bounds control hActivity ν T hT v hCoupling t ⟨t.coe_nonneg, ht⟩).2.1

end CarryingCapacity.DeterministicEnvironmentEnvelope
