import CarryingCapacity.DeterministicEnvironmentEnvelope
import CarryingCapacity.TimeDependentStochasticContinuity
import CarryingCapacity.LawCurveContinuity

/-!
# The actual prescribed-environment evolution on the manuscript interval

These laws are the marginals of the constructed common-noise process. The
fixed-time regularity is derived from diffuse proposal times and genuine
localization exhaustion; the uniform moment bound uses the exact manuscript
envelope. Superlinear uniform integrability upgrades this to actual adapted
transport continuity, giving an evolution map into the manuscript curve space.
No nonlinear self-consistency or contraction conclusion is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace CarryingCapacity.DeterministicEnvironmentEvolution
open CommonInitialNoise LyapunovFlowSpace DeterministicEnvironmentLyapunov
open DeterministicEnvironmentProcess DeterministicEnvironmentLaw DeterministicEnvironmentFrozen

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T)
  (v : ManuscriptCurves control.function ν (driftConstant control) T hT)
  (hCoupling : MomentCouplingBound κ q)

/-- The actual time marginals restricted to the manuscript construction interval. -/
def intervalLaw (t : Icc (0 : ℝ) T) : MomentLaw κ D :=
  outputLaw control hActivity ν T hT v hCoupling ⟨t, t.property.1⟩

include hCoupling

/-- The actual process is almost surely continuous at each fixed nonnegative time.
The probability-one event is allowed to depend on that fixed time. -/
theorem ae_continuousWithinAt_manuscriptProcess (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ p ∂law ν.measure (Jump D),
      ContinuousWithinAt (manuscriptProcess control hActivity ν T hT v p) (Ici 0) t := by
  exact TimeDependentStochasticContinuity.ae_continuousWithinAt control.function
    (finite_sublevels control) Jump.advance
    (timeRate κ q (manuscriptExtension control ν (driftConstant control) T hT v) T)
    (exists_uniform_rate_bounds control _ T hT hActivity
      (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn)
    id 0 ν.measure (manuscript_exhaustive control hActivity ν T hT v hCoupling) t ht

/-- On the compact time subtype, the same assertion is ordinary continuity
at each deterministic point, including both endpoints and a zero horizon. -/
theorem ae_continuousAt_intervalProcess (t : Icc (0 : ℝ) T) :
    ∀ᵐ p ∂law ν.measure (Jump D), ContinuousAt
      (fun s : Icc (0 : ℝ) T => manuscriptProcess control hActivity ν T hT v p s) t := by
  filter_upwards [ae_continuousWithinAt_manuscriptProcess control hActivity ν T hT v hCoupling
    t t.property.1] with p hp
  exact (continuousWithinAt_iff_continuousAt_restrict _ t.property).mp
    (hp.mono (fun _ hs => hs.1))

/-- The exact initial law is retained by the interval family. -/
theorem intervalLaw_initial :
    intervalLaw control hActivity ν T hT v hCoupling ⟨0, le_rfl, hT⟩ = ν :=
  outputLaw_zero control hActivity ν T hT v hCoupling

/-- Each actual output marginal satisfies the time-specific Lyapunov constraint. -/
theorem intervalLaw_envelope (t : Icc (0 : ℝ) T) :
    lyapunovIntegral control.function (intervalLaw control hActivity ν T hT v hCoupling t) ≤
      ENNReal.ofReal (intervalEnvelope (∫ x, control.function x ∂ν.measure)
        (driftConstant control) T t) :=
  DeterministicEnvironmentEnvelope.lyapunovIntegral_outputLaw_le
    control hActivity ν T hT v hCoupling ⟨t, t.property.1⟩ t.property.2

/-- A uniform genuine sample-space Lyapunov bound on the entire interval. -/
theorem uniform_integral_lyapunov_bound (t : Icc (0 : ℝ) T) :
    (∫ p, control.function (manuscriptProcess control hActivity ν T hT v p t)
      ∂law ν.measure (Jump D)) ≤ manuscriptBound control ν (driftConstant control) T :=
  (DeterministicEnvironmentEnvelope.manuscript_moment_bounds
    control hActivity ν T hT v hCoupling t t.property).2.1.trans
      (exponentialEnvelope_mono_time (integral_nonneg (function_nonnegative control))
        (driftConstant_nonnegative control) t.property.2)

/-- The actual output law curve is continuous in the genuine adapted
Wasserstein metric, including at zero and the final time. -/
theorem continuous_intervalLaw :
    Continuous (intervalLaw control hActivity ν T hT v hCoupling) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact LawCurveContinuity.continuous_marginals (law ν.measure (Jump D))
    control.function control.dominates control.superlinear
    (fun (s : Icc (0 : ℝ) T) p => manuscriptProcess control hActivity ν T hT v p s)
    (fun s => measurable_at control hActivity ν T hT v hCoupling s)
    (fun s => manuscript_integrable_lyapunov control hActivity ν T hT v hCoupling s s.property.1)
    (manuscriptBound control ν (driftConstant control) T)
    (manuscriptBound_nonnegative control ν (driftConstant control) T
      (driftConstant_nonnegative control) hT)
    (uniform_integral_lyapunov_bound control hActivity ν T hT v hCoupling)
    (intervalLaw control hActivity ν T hT v hCoupling) (fun _ => rfl)
    (ae_continuousAt_intervalProcess control hActivity ν T hT v hCoupling)

/-- The actual continuous output law curve, built from the process marginals. -/
def outputCurve : C(Icc (0 : ℝ) T, MomentLaw κ D) :=
  ⟨intervalLaw control hActivity ν T hT v hCoupling,
    continuous_intervalLaw control hActivity ν T hT v hCoupling⟩

/-- The prescribed-environment evolution maps the manuscript curve space to
itself. Initial law, continuity, and the exact moment envelope are all proved
properties of its constructed marginals, rather than hypotheses of this map. -/
def evolution : ManuscriptCurves control.function ν (driftConstant control) T hT :=
  ⟨outputCurve control hActivity ν T hT v hCoupling,
    intervalLaw_initial control hActivity ν T hT v hCoupling,
    intervalLaw_envelope control hActivity ν T hT v hCoupling⟩

/-- Every value of the evolution is exactly the constructed process law. -/
theorem evolution_measure (t : Icc (0 : ℝ) T) :
    ((evolution control hActivity ν T hT v hCoupling).val t).measure =
      (law ν.measure (Jump D)).map
        (fun p => manuscriptProcess control hActivity ν T hT v p t) := rfl

/-- The realized evolution retains the prescribed initial law. -/
theorem evolution_initial :
    (evolution control hActivity ν T hT v hCoupling).val ⟨0, le_rfl, hT⟩ = ν :=
  intervalLaw_initial control hActivity ν T hT v hCoupling

end CarryingCapacity.DeterministicEnvironmentEvolution
