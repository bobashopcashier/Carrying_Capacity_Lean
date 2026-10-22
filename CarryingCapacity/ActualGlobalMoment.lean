import CarryingCapacity.GlobalLyapunovMoment
import CarryingCapacity.ConfigurationNonexplosion

/-!
# Actual global Lyapunov moments

The finite-level expectations and exhaustion needed for Fatou's lemma are
supplied by the proved non-explosion theorem. Thus the actual common-noise
global process has an integrable Lyapunov value at every finite nonnegative
time and retains the affine-exponential bound, including its subtract-one
term. The particle-system specialization derives its drift from the actual
single-lineage LyapunovControl, with a coefficient independent of N.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace CarryingCapacity.ActualGlobalMoment
open CommonInitialNoise LyapunovLocalization ActualNonexplosion

/-- The affine-exponential bound is nonnegative for a nonnegative initial
Lyapunov function, nonnegative drift coefficient, and nonnegative time. -/
theorem exponentialBound_nonnegative {A E : Type*} [MeasurableSpace A]
    (V : E → ℝ) (initial : A → E) (μ : Measure A) (b : ℝ) (hb : 0 ≤ b)
    (hV : ∀ x, 0 ≤ V x) (T : ℝ) (hT : 0 ≤ T) :
    0 ≤ exponentialBound V initial μ b T := by
  have hm : 0 ≤ ∫ a, V (initial a) ∂μ := integral_nonneg (fun _ => hV _)
  have he : 1 ≤ Real.exp (b * T) := Real.one_le_exp_iff.mpr (mul_nonneg hb hT)
  have hp : (1 : ℝ) ≤ (1 + ∫ a, V (initial a) ∂μ) * Real.exp (b * T) := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ (1 + ∫ a, V (initial a) ∂μ) * Real.exp (b * T) :=
        mul_le_mul (by linarith) he (by norm_num) (by linarith)
  exact sub_nonneg.mpr hp

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

/-- Global integrability follows from the initial Lyapunov moment and the
model drift assumptions. Exhaustion and finite-level moment bounds are proved. -/
theorem integrable (T : ℝ) (hT : 0 ≤ T) :
    Integrable (fun p => V (GlobalLocalizedProcess.process V hfinite jump rate initial e p T))
      (law μ J) :=
  GlobalLyapunovMoment.integrable V hfinite jump rate initial e μ hinit hVnonneg T hT
    (exponentialBound V initial μ b T)
    (ActualNonexplosion.ae_exhaustive V hfinite jump rate initial e μ hinit b hb hVnonneg hq hV hdrift)
    (fun n => integrable_localized_value V hfinite jump rate initial e μ hinit hV n T)
    (fun n => localized_expectation_le V hfinite jump rate initial e μ hinit b hb
      hVnonneg hq hV hdrift n T hT)

/-- The sharp affine-exponential expectation bound for the actual global
process, with no assumed global moment bound or exhaustion premise. -/
theorem expectation_le (T : ℝ) (hT : 0 ≤ T) :
    (∫ p, V (GlobalLocalizedProcess.process V hfinite jump rate initial e p T) ∂law μ J) ≤
      exponentialBound V initial μ b T :=
  GlobalLyapunovMoment.expectation_le V hfinite jump rate initial e μ hinit hVnonneg T hT
    (exponentialBound V initial μ b T)
    (exponentialBound_nonnegative V initial μ b hb hVnonneg T hT)
    (ActualNonexplosion.ae_exhaustive V hfinite jump rate initial e μ hinit b hb hVnonneg hq hV hdrift)
    (fun n => integrable_localized_value V hfinite jump rate initial e μ hinit hV n T)
    (fun n => localized_expectation_le V hfinite jump rate initial e μ hinit b hb
      hVnonneg hq hV hdrift n T hT)

/-- The equivalent extended-nonnegative moment estimate. -/
theorem lintegral_le (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ p, ENNReal.ofReal (V (GlobalLocalizedProcess.process V hfinite jump rate initial e p T))
      ∂law μ J) ≤ ENNReal.ofReal (exponentialBound V initial μ b T) :=
  GlobalLyapunovMoment.lintegral_le V hfinite jump rate initial e μ hinit hVnonneg T hT
    (exponentialBound V initial μ b T)
    (ActualNonexplosion.ae_exhaustive V hfinite jump rate initial e μ hinit b hb hVnonneg hq hV hdrift)
    (fun n => integrable_localized_value V hfinite jump rate initial e μ hinit hV n T)
    (fun n => localized_expectation_le V hfinite jump rate initial e μ hinit b hb
      hVnonneg hq hV hdrift n T hT)

end General

section Configuration
open ConfigurationLocalization
variable {A : Type*} [MeasurableSpace A] {N D : ℕ}
  {κ : MomentScale} {q : Rates D (MomentLaw κ D)} (control : LyapunovControl κ q)
  (hN : 0 < N) (initial : A → Configuration N D)
  (μ : Measure A) [IsProbabilityMeasure μ] (hinit : Measurable initial)
  (hV : Integrable (fun a => lyapunov control (initial a)) μ)
include hinit hV

/-- Integrability of the empirical Lyapunov value for the actual global
particle process follows from its initial empirical moment. -/
theorem configuration_integrable (T : ℝ) (hT : 0 ≤ T) :
    Integrable (fun p => lyapunov control (ConfigurationNonexplosion.process control hN initial p T))
      (law μ (Label N D)) :=
  integrable (lyapunov control) (finite_sublevel control hN) jump (rate κ q hN) initial 0 μ hinit
    (2 * driftConstant control) (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
    (lyapunov_nonnegative control) (fun z j => rate_nonnegative κ q hN j z) hV
    (ConfigurationNonexplosion.generator_affine_bound control hN) T hT

/-- The actual global particle system satisfies a bound uniform in the
particle number except through its initial empirical Lyapunov expectation. -/
theorem configuration_expectation_le (T : ℝ) (hT : 0 ≤ T) :
    (∫ p, lyapunov control (ConfigurationNonexplosion.process control hN initial p T)
      ∂law μ (Label N D)) ≤
      (1 + ∫ a, lyapunov control (initial a) ∂μ) *
        Real.exp ((2 * driftConstant control) * T) - 1 :=
  expectation_le (lyapunov control) (finite_sublevel control hN) jump (rate κ q hN) initial 0 μ hinit
    (2 * driftConstant control) (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
    (lyapunov_nonnegative control) (fun z j => rate_nonnegative κ q hN j z) hV
    (ConfigurationNonexplosion.generator_affine_bound control hN) T hT

end Configuration
end CarryingCapacity.ActualGlobalMoment
