import CarryingCapacity.DeterministicEnvironmentProcess

/-!
# Actual time marginals of a prescribed-environment process

The output law is the pushforward of the constructed process, with its finite
adapted moment derived from the proved global Lyapunov estimate. These laws
have the prescribed initial value and exact expectation identities. This file
does not assume or assert continuity of the output curve or self-consistency
with its input environment.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace CarryingCapacity.DeterministicEnvironmentLaw
open CommonInitialNoise DeterministicEnvironmentLyapunov DeterministicEnvironmentProcess
open LyapunovFlowSpace

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T)
  (v : ManuscriptCurves control.function ν (driftConstant control) T hT)
  (hCoupling : MomentCouplingBound κ q)
include hCoupling

/-- Every time evaluation of the actual manuscript process is measurable. -/
theorem measurable_at (s : ℝ) : Measurable
    (fun p => manuscriptProcess control hActivity ν T hT v p s) := by
  have hpair : Measurable (fun p : Sample (State D) (Jump D) => (p, s)) :=
    measurable_id.prodMk measurable_const
  have hm := (measurable_manuscriptProcess control hActivity ν T hT v hCoupling).comp hpair
  simpa only [Function.comp_def] using hm

/-- The adapted state weight is genuinely integrable under the constructed path law. -/
theorem integrable_weight_at (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun p => momentWeight κ (manuscriptProcess control hActivity ν T hT v p s))
      (law ν.measure (Jump D)) := by
  apply (manuscript_integrable_lyapunov control hActivity ν T hT v hCoupling s hs).mono'
    ((measurable_of_countable (momentWeight κ : State D → ℝ)).comp
      (measurable_at control hActivity ν T hT v hCoupling s)).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    change ‖momentWeight κ (manuscriptProcess control hActivity ν T hT v p s)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (momentWeight_nonneg κ _)]
    linarith [control.dominates (manuscriptProcess control hActivity ν T hT v p s)]

/-- The genuine finite-moment time marginal of the constructed global process. -/
def outputLaw (s : ℝ≥0) : MomentLaw κ D where
  measure := (law ν.measure (Jump D)).map
    (fun p => manuscriptProcess control hActivity ν T hT v p s)
  probability := by
    letI : IsProbabilityMeasure ν.measure := ν.probability
    exact isProbabilityMeasure_map (measurable_at control hActivity ν T hT v hCoupling s).aemeasurable
  integrable_weight := by
    apply (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_at control hActivity ν T hT v hCoupling s).aemeasurable).mpr
    exact integrable_weight_at control hActivity ν T hT v hCoupling s s.2

/-- The initial output law equals the actual input initial law. -/
theorem outputLaw_zero : outputLaw control hActivity ν T hT v hCoupling 0 = ν := by
  apply MomentLaw.ext
  exact manuscript_initial_law control hActivity ν T hT v

/-- All real-valued observables have the exact pushforward integral identity. -/
theorem integral_outputLaw (s : ℝ≥0) (f : State D → ℝ) :
    (∫ x, f x ∂(outputLaw control hActivity ν T hT v hCoupling s).measure) =
      ∫ p, f (manuscriptProcess control hActivity ν T hT v p s) ∂law ν.measure (Jump D) :=
  integral_map_of_stronglyMeasurable
    (measurable_at control hActivity ν T hT v hCoupling s)
    (measurable_of_countable f).stronglyMeasurable

/-- The Lyapunov function is integrable under each actual output law. -/
theorem integrable_lyapunov_outputLaw (s : ℝ≥0) :
    Integrable control.function (outputLaw control hActivity ν T hT v hCoupling s).measure := by
  apply (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_at control hActivity ν T hT v hCoupling s).aemeasurable).mpr
  exact manuscript_integrable_lyapunov control hActivity ν T hT v hCoupling s s.2

/-- The output moment is the expectation of the actual process weight. -/
theorem moment_outputLaw (s : ℝ≥0) :
    moment (outputLaw control hActivity ν T hT v hCoupling s) =
      ∫ p, momentWeight κ (manuscriptProcess control hActivity ν T hT v p s) ∂law ν.measure (Jump D) :=
  integral_outputLaw control hActivity ν T hT v hCoupling s (momentWeight κ)

/-- The extended Lyapunov integral also agrees with the actual sample integral. -/
theorem lyapunovIntegral_outputLaw (s : ℝ≥0) :
    lyapunovIntegral control.function (outputLaw control hActivity ν T hT v hCoupling s) =
      ∫⁻ p, ENNReal.ofReal (control.function (manuscriptProcess control hActivity ν T hT v p s))
        ∂law ν.measure (Jump D) := by
  unfold lyapunovIntegral
  exact lintegral_map' (measurable_of_countable (fun x : State D => ENNReal.ofReal (control.function x))).aemeasurable
    (measurable_at control hActivity ν T hT v hCoupling s).aemeasurable

/-- The proved global affine-exponential estimate applies to the output law itself. -/
theorem lyapunov_outputLaw_le (s : ℝ≥0) :
    (∫ x, control.function x ∂(outputLaw control hActivity ν T hT v hCoupling s).measure) ≤
      (1 + ∫ x, control.function x ∂ν.measure) *
        Real.exp (affineConstant control (manuscriptBound control ν (driftConstant control) T) * s) - 1 := by
  rw [integral_outputLaw]
  exact manuscript_expectation_le control hActivity ν T hT v hCoupling s s.2

end CarryingCapacity.DeterministicEnvironmentLaw
