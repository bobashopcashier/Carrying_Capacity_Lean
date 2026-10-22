import CarryingCapacity.DeterministicEnvironmentGeneralForward
import CarryingCapacity.TimeDependentStochasticContinuity
import CarryingCapacity.LawCurveContinuity

/-!
# Continuous actual laws for a general prescribed environment

The prescribed environment is only required to be continuous on the original
interval and to have a bounded genuine Lyapunov moment. Its value at zero is
unrelated to the initial law. The existing constructed process supplies the
actual marginals. Their finite moments and uniform superlinear control are
derived from its Lyapunov estimate, and diffuse proposal times supply the
fixed-time path continuity needed for genuine Wasserstein continuity.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace CarryingCapacity.DeterministicEnvironmentGeneralLaw
open CommonInitialNoise DeterministicEnvironmentLyapunov DeterministicEnvironmentFrozen
open LyapunovFlowSpace

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))
  (ν : MomentLaw κ D) (hCoupling : MomentCouplingBound κ q)
  (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ s ∈ Icc 0 T, lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
  (hInitial : Integrable control.function ν.measure)

/-- The explicit general-environment Lyapunov bound at a given time. -/
def momentBound (s : ℝ) : ℝ :=
  (1 + ∫ x, control.function x ∂ν.measure) * Real.exp (affineConstant control B * s) - 1

include hB in
theorem momentBound_nonnegative (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ momentBound control ν B s := by
  have hi : (0 : ℝ) ≤ ∫ x, control.function x ∂ν.measure :=
    integral_nonneg (function_nonnegative control)
  have he : 1 ≤ Real.exp (affineConstant control B * s) :=
    Real.one_le_exp (mul_nonneg (affineConstant_nonnegative control B hB) hs)
  unfold momentBound
  nlinarith

include hB in
theorem momentBound_mono {s t : ℝ} (hst : s ≤ t) :
    momentBound control ν B s ≤ momentBound control ν B t := by
  have hi : (0 : ℝ) ≤ ∫ x, control.function x ∂ν.measure :=
    integral_nonneg (function_nonnegative control)
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst
    (affineConstant_nonnegative control B hB))
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left he (by linarith)) 1

include hCoupling

/-- Evaluation of the actual general-environment process is measurable. -/
theorem measurable_at (s : ℝ) : Measurable (fun p =>
    DeterministicEnvironmentProcess.process control hActivity v T hT hv id p s) := by
  have hpair : Measurable (fun p : Sample (State D) (Jump D) => (p,s)) :=
    measurable_id.prodMk measurable_const
  have hm := (DeterministicEnvironmentProcess.measurable_process control hActivity v T hT hv id
    hCoupling measurable_id).comp hpair
  simpa only [Function.comp_def] using hm

include hB hEnv hInitial

/-- The actual process has a genuine integrable Lyapunov function at every
nonnegative time, as a consequence of the constructed exit exhaustion. -/
theorem integrable_lyapunov_at (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun p => control.function
      (DeterministicEnvironmentProcess.process control hActivity v T hT hv id p s))
      (law ν.measure (Jump D)) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact DeterministicEnvironmentProcess.integrable_lyapunov control hActivity v T hT hv
    id ν.measure hCoupling measurable_id B hB hEnv hInitial s hs

/-- The adapted weight is dominated by the genuine Lyapunov integrable random variable. -/
theorem integrable_weight_at (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun p => momentWeight κ
      (DeterministicEnvironmentProcess.process control hActivity v T hT hv id p s))
      (law ν.measure (Jump D)) := by
  apply (integrable_lyapunov_at control hActivity v T hT hv ν hCoupling B hB hEnv hInitial s hs).mono'
    ((measurable_of_countable (momentWeight κ : State D → ℝ)).comp
      (measurable_at control hActivity v T hT hv hCoupling s)).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    change ‖momentWeight κ (DeterministicEnvironmentProcess.process control hActivity v T hT hv id p s)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (momentWeight_nonneg κ _)]
    linarith [control.dominates (DeterministicEnvironmentProcess.process control hActivity v T hT hv id p s)]

/-- Actual finite-moment marginals, without an initial/environment consistency premise. -/
def outputLaw (s : ℝ≥0) : MomentLaw κ D where
  measure := DeterministicEnvironmentGeneralForward.actualLaw control hActivity v T hT hv ν s
  probability := DeterministicEnvironmentGeneralForward.actualLaw_probability
    control hActivity v T hT hv ν hCoupling s
  integrable_weight := by
    apply (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_at control hActivity v T hT hv hCoupling s).aemeasurable).mpr
    exact integrable_weight_at control hActivity v T hT hv ν hCoupling B hB hEnv hInitial s s.2

/-- The law package retains exactly the already constructed forward law. -/
theorem outputLaw_measure (s : ℝ≥0) :
    (outputLaw control hActivity v T hT hv ν hCoupling B hB hEnv hInitial s).measure =
      DeterministicEnvironmentGeneralForward.actualLaw control hActivity v T hT hv ν s := rfl

/-- The output's initial law is precisely the given initial law. -/
theorem outputLaw_zero : outputLaw control hActivity v T hT hv ν hCoupling B hB hEnv hInitial 0 = ν := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  apply MomentLaw.ext
  change (law ν.measure (Jump D)).map
    (fun p => DeterministicEnvironmentProcess.process control hActivity v T hT hv id p 0) = ν.measure
  rw [DeterministicEnvironmentProcess.initial_law control hActivity v T hT hv id ν.measure measurable_id]
  exact Measure.map_id

/-- Exact pushforward integration for every real observable. -/
theorem integral_outputLaw (s : ℝ≥0) (f : State D → ℝ) :
    (∫ x, f x ∂(outputLaw control hActivity v T hT hv ν hCoupling B hB hEnv hInitial s).measure) =
      ∫ p, f (DeterministicEnvironmentProcess.process control hActivity v T hT hv id p s)
        ∂law ν.measure (Jump D) :=
  DeterministicEnvironmentGeneralForward.integral_actualLaw control hActivity v T hT hv ν hCoupling f s

/-- Every actual output law has finite genuine Lyapunov moment. -/
theorem integrable_lyapunov_outputLaw (s : ℝ≥0) :
    Integrable control.function
      (outputLaw control hActivity v T hT hv ν hCoupling B hB hEnv hInitial s).measure := by
  apply (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_at control hActivity v T hT hv hCoupling s).aemeasurable).mpr
  exact integrable_lyapunov_at control hActivity v T hT hv ν hCoupling B hB hEnv hInitial s s.2

/-- The actual sample-space Lyapunov expectation satisfies the proved explicit bound. -/
theorem lyapunov_expectation_le (s : ℝ) (hs : 0 ≤ s) :
    (∫ p, control.function (DeterministicEnvironmentProcess.process control hActivity v T hT hv id p s)
      ∂law ν.measure (Jump D)) ≤ momentBound control ν B s := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact DeterministicEnvironmentProcess.lyapunov_expectation_le control hActivity v T hT hv
    id ν.measure hCoupling measurable_id B hB hEnv hInitial s hs

/-- The sharp affine-exponential estimate applies to the actual law integral. -/
theorem lyapunov_outputLaw_le (s : ℝ≥0) :
    (∫ x, control.function x
      ∂(outputLaw control hActivity v T hT hv ν hCoupling B hB hEnv hInitial s).measure) ≤
      momentBound control ν B s := by
  rw [integral_outputLaw]
  exact lyapunov_expectation_le control hActivity v T hT hv ν hCoupling B hB hEnv hInitial s s.2

/-- The genuine extended moment obeys the same bound; it is not a totalized
ordinary integral of a potentially nonintegrable function. -/
theorem lyapunovIntegral_outputLaw_le (s : ℝ≥0) :
    lyapunovIntegral control.function
      (outputLaw control hActivity v T hT hv ν hCoupling B hB hEnv hInitial s) ≤
      ENNReal.ofReal (momentBound control ν B s) := by
  apply (lyapunovIntegral_le_iff (function_nonnegative control) _
    (momentBound_nonnegative control ν B hB s s.2)).mpr
  exact ⟨integrable_lyapunov_outputLaw control hActivity v T hT hv ν hCoupling B hB hEnv hInitial s,
    lyapunov_outputLaw_le control hActivity v T hT hv ν hCoupling B hB hEnv hInitial s⟩

/-- The genuine moment-law curve restricted to the construction interval. -/
def intervalLaw (s : Icc (0 : ℝ) T) : MomentLaw κ D :=
  outputLaw control hActivity v T hT hv ν hCoupling B hB hEnv hInitial ⟨s, s.property.1⟩

/-- Actual path continuity at each deterministic nonnegative time follows
from diffuse proposal times and the proved nonexplosion. -/
theorem ae_continuousWithinAt_process (s : ℝ) (hs : 0 ≤ s) :
    ∀ᵐ p ∂law ν.measure (Jump D), ContinuousWithinAt
      (DeterministicEnvironmentProcess.process control hActivity v T hT hv id p) (Ici 0) s := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact TimeDependentStochasticContinuity.ae_continuousWithinAt control.function
    (finite_sublevels control) Jump.advance (timeRate κ q v T)
    (exists_uniform_rate_bounds control v T hT hActivity hv) id 0 ν.measure
    (DeterministicEnvironmentProcess.ae_exhaustive control hActivity v T hT hv
      id ν.measure hCoupling measurable_id B hB hEnv hInitial) s hs

/-- On the interval subtype the fixed-time assertion includes both endpoints.
Its probability-one event may depend on the time. -/
theorem ae_continuousAt_intervalProcess (t : Icc (0 : ℝ) T) :
    ∀ᵐ p ∂law ν.measure (Jump D), ContinuousAt
      (fun s : Icc (0 : ℝ) T => DeterministicEnvironmentProcess.process control hActivity v T hT hv id p s) t := by
  filter_upwards [ae_continuousWithinAt_process control hActivity v T hT hv ν hCoupling B hB hEnv hInitial
    t t.property.1] with p hp
  exact (continuousWithinAt_iff_continuousAt_restrict _ t.property).mp
    (hp.mono (fun _ hs => hs.1))

/-- A single finite superlinear moment bound holds for all actual times in the interval. -/
theorem uniform_integral_lyapunov_bound (t : Icc (0 : ℝ) T) :
    (∫ p, control.function (DeterministicEnvironmentProcess.process control hActivity v T hT hv id p t)
      ∂law ν.measure (Jump D)) ≤ momentBound control ν B T :=
  (lyapunov_expectation_le control hActivity v T hT hv ν hCoupling B hB hEnv hInitial t t.property.1).trans
    (momentBound_mono control ν B hB t.property.2)

/-- The actual general output law is continuous in the adapted Wasserstein
metric, proved from superlinear uniform integrability and fixed-time path continuity. -/
theorem continuous_intervalLaw :
    Continuous (intervalLaw control hActivity v T hT hv ν hCoupling B hB hEnv hInitial) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact LawCurveContinuity.continuous_marginals (law ν.measure (Jump D))
    control.function control.dominates control.superlinear
    (fun (s : Icc (0 : ℝ) T) p => DeterministicEnvironmentProcess.process control hActivity v T hT hv id p s)
    (fun s => measurable_at control hActivity v T hT hv hCoupling s)
    (fun s => integrable_lyapunov_at control hActivity v T hT hv ν hCoupling B hB hEnv hInitial s s.property.1)
    (momentBound control ν B T) (momentBound_nonnegative control ν B hB T hT)
    (uniform_integral_lyapunov_bound control hActivity v T hT hv ν hCoupling B hB hEnv hInitial)
    (intervalLaw control hActivity v T hT hv ν hCoupling B hB hEnv hInitial) (fun _ => rfl)
    (ae_continuousAt_intervalProcess control hActivity v T hT hv ν hCoupling B hB hEnv hInitial)

/-- A continuous moment-law curve realized by the actual process marginals. -/
def outputCurve : C(Icc (0 : ℝ) T, MomentLaw κ D) :=
  ⟨intervalLaw control hActivity v T hT hv ν hCoupling B hB hEnv hInitial,
    continuous_intervalLaw control hActivity v T hT hv ν hCoupling B hB hEnv hInitial⟩

/-- The continuous curve still has exactly the actual forward-equation laws. -/
theorem outputCurve_measure (s : Icc (0 : ℝ) T) :
    ((outputCurve control hActivity v T hT hv ν hCoupling B hB hEnv hInitial) s).measure =
      DeterministicEnvironmentGeneralForward.actualLaw control hActivity v T hT hv ν s := rfl

/-- The continuous output curve starts at the prescribed initial law. -/
theorem outputCurve_initial :
    outputCurve control hActivity v T hT hv ν hCoupling B hB hEnv hInitial ⟨0, le_rfl, hT⟩ = ν :=
  outputLaw_zero control hActivity v T hT hv ν hCoupling B hB hEnv hInitial

/-- Uniform genuine Lyapunov control of the continuous output curve. -/
theorem outputCurve_lyapunov_bound (s : Icc (0 : ℝ) T) :
    lyapunovIntegral control.function
      (outputCurve control hActivity v T hT hv ν hCoupling B hB hEnv hInitial s) ≤
      ENNReal.ofReal (momentBound control ν B T) :=
  (lyapunovIntegral_outputLaw_le control hActivity v T hT hv ν hCoupling B hB hEnv hInitial
    ⟨s,s.property.1⟩).trans (ENNReal.ofReal_le_ofReal (momentBound_mono control ν B hB s.property.2))

end CarryingCapacity.DeterministicEnvironmentGeneralLaw
