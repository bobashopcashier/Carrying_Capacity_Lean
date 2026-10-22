import CarryingCapacity.GlobalLocalizedCountingIdentity
import CarryingCapacity.ConfigurationNonexplosion

/-!
# The actual global particle counting equation

The Lyapunov non-explosion theorem supplies the genuine-exit exhaustion
required by the pathwise counting-identity bridge. Thus the actual globally
defined process satisfies the unrestricted rate-threshold jump equation for
real test functions, with pathwise-integrable counting integrands. The
empirical configuration specialization uses only the original LyapunovControl
and the initial empirical Lyapunov moment, not an exhaustion assumption.

This proves the equation for the constructed counting measures. Their full
independently scattered law on arbitrary planar sets and global pathwise
uniqueness remain separate results.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace CarryingCapacity.ActualGlobalCounting
open CommonInitialNoise LyapunovLocalization

section General
variable {A E J : Type*} [MeasurableSpace A] [DecidableEq E] [Fintype J]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → E → ℝ) (initial : A → E) (e : E)
  (μ : Measure A) [IsProbabilityMeasure μ]
  (hinit : Measurable initial) (b : ℝ) (hb : 0 ≤ b)
  (hVnonneg : ∀ x, 0 ≤ V x) (hq : ∀ x j, 0 ≤ rate j x)
  (hV : Integrable (fun a => V (initial a)) μ)
  (hdrift : ∀ x, (∑ j, rate j x * (V (jump j x) - V x)) ≤ b * (1 + V x))
include hinit hb hVnonneg hq hV hdrift

/-- The actual unrestricted global counting integrands are pathwise
integrable on every finite horizon, for every real test function. -/
theorem ae_integrable_horizonIncrement : ∀ᵐ p ∂law μ J,
    ∀ (T : ℝ≥0) (f : E → ℝ) (j : J),
      Integrable (fun q => GlobalLocalizedCountingIdentity.horizonIncrement
        V hfinite jump rate initial e f j T (p,q)) (MarkedNoise.countingMeasure j p.2) :=
  GlobalLocalizedCountingIdentity.ae_integrable_horizonIncrement V hfinite jump rate initial e μ
    (ActualNonexplosion.ae_exhaustive V hfinite jump rate initial e μ hinit b hb hVnonneg hq hV hdrift)

/-- The nonexplosive global construction solves the actual test-function
counting equation with no localization or height cutoff in its integrand. -/
theorem ae_testFunction_counting_identity (f : E → ℝ) :
    ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0,
      f (GlobalLocalizedProcess.process V hfinite jump rate initial e p T) - f (initial p.1) =
        ∑ j : J, ∫ q, GlobalLocalizedCountingIdentity.horizonIncrement
          V hfinite jump rate initial e f j T (p,q) ∂MarkedNoise.countingMeasure j p.2 :=
  GlobalLocalizedCountingIdentity.ae_testFunction_counting_identity
    V hfinite jump rate initial e μ f
      (ActualNonexplosion.ae_exhaustive V hfinite jump rate initial e μ hinit b hb hVnonneg hq hV hdrift)

end General

section Configuration
open ConfigurationLocalization
variable {A : Type*} [MeasurableSpace A] {N D : ℕ}
  {κ : MomentScale} {q : Rates D (MomentLaw κ D)} (control : LyapunovControl κ q)
  (hN : 0 < N) (initial : A → Configuration N D)
  (μ : Measure A) [IsProbabilityMeasure μ] (hinit : Measurable initial)
  (hV : Integrable (fun a => lyapunov control (initial a)) μ)
include hinit hV

/-- The actual empirical particle system satisfies the unrestricted
accepted-jump equation for every real test function on configurations. -/
theorem configuration_counting_identity (f : Configuration N D → ℝ) :
    ∀ᵐ p ∂law μ (Label N D), ∀ T : ℝ≥0,
      f (ConfigurationNonexplosion.process control hN initial p T) - f (initial p.1) =
        ∑ j : Label N D, ∫ r, GlobalLocalizedCountingIdentity.horizonIncrement
          (lyapunov control) (finite_sublevel control hN) jump (rate κ q hN)
          initial 0 f j T (p,r) ∂MarkedNoise.countingMeasure j p.2 :=
  ae_testFunction_counting_identity (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q hN) initial 0 μ hinit (2 * driftConstant control)
    (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
    (lyapunov_nonnegative control) (fun z j => rate_nonnegative κ q hN j z) hV
    (ConfigurationNonexplosion.generator_affine_bound control hN) f

/-- Pathwise counting-integrability also holds for arbitrary configuration
test functions, with no assumed expected activity bound. -/
theorem configuration_integrable_horizonIncrement : ∀ᵐ p ∂law μ (Label N D),
    ∀ (T : ℝ≥0) (f : Configuration N D → ℝ) (j : Label N D),
      Integrable (fun r => GlobalLocalizedCountingIdentity.horizonIncrement
        (lyapunov control) (finite_sublevel control hN) jump (rate κ q hN)
        initial 0 f j T (p,r)) (MarkedNoise.countingMeasure j p.2) :=
  ae_integrable_horizonIncrement (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q hN) initial 0 μ hinit (2 * driftConstant control)
    (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
    (lyapunov_nonnegative control) (fun z j => rate_nonnegative κ q hN j z) hV
    (ConfigurationNonexplosion.generator_affine_bound control hN)

end Configuration
end CarryingCapacity.ActualGlobalCounting
