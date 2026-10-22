import CarryingCapacity.GlobalCountingUniqueness
import CarryingCapacity.ConfigurationNonexplosion

/-!
# Pathwise uniqueness under the actual Lyapunov assumptions

The proved Lyapunov nonexplosion estimate discharges exhaustion in the global
counting-equation uniqueness theorem. A discrete cadlag candidate with the
same initial record and the same actual counting equations therefore agrees
with the constructed process at every nonnegative time, on one event.

The configuration specialization uses the manuscript's LyapunovControl and
initial empirical Lyapunov integrability. Candidate finite activity, rate
bounds, moment bounds, and agreement with frozen paths are not hypotheses.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical Topology ENNReal NNReal BigOperators

namespace CarryingCapacity.ActualGlobalUniqueness
open CommonInitialNoise CountingEquationUniqueness GlobalCountingUniqueness

section General
variable {A E J : Type*} [MeasurableSpace A] [DecidableEq E] [Fintype J]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E] [DiscreteTopology E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → E → ℝ) (initial : A → E) (e : E)
  (μ : Measure A) [IsProbabilityMeasure μ]
  (hinit : Measurable initial) (b : ℝ) (hb : 0 ≤ b)
  (hVnonneg : ∀ x, 0 ≤ V x) (hq : ∀ x j, 0 ≤ rate j x)
  (hV : Integrable (fun a => V (initial a)) μ)
  (hdrift : ∀ x, (∑ j, rate j x * (V (jump j x) - V x)) ≤ b * (1 + V x))
include hinit hb hVnonneg hq hV hdrift

/-- Actual pathwise uniqueness for any discrete cadlag candidate solving the
same common-noise counting equation, derived from the Lyapunov assumptions. -/
theorem ae_candidate_eq_process
    (X : Sample A J → ℝ → E)
    (hcadlag : ∀ᵐ p ∂law μ J,
      (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (X p) (Ici t) t) ∧
      (∀ t : ℝ, 0 < t → ∃ y : E, Tendsto (X p) (𝓝[<] t) (𝓝 y)))
    (hzero : ∀ᵐ p ∂law μ J, X p 0 = initial p.1)
    (heq : ∀ z : E, ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0,
      stateTest z (X p T) - stateTest z (initial p.1) =
        ∑ j : J, ∫ q, candidateIncrement jump rate X e (stateTest z) j T (p,q)
          ∂MarkedNoise.countingMeasure j p.2) :
    ∀ᵐ p ∂law μ J, ∀ t : ℝ, 0 ≤ t →
      X p t = GlobalLocalizedProcess.process V hfinite jump rate initial e p t :=
  GlobalCountingUniqueness.ae_candidate_eq_process V hfinite jump rate initial e μ
    (ActualNonexplosion.ae_exhaustive V hfinite jump rate initial e μ hinit b hb hVnonneg hq hV hdrift)
    X hcadlag hzero heq

end General

namespace ConfigurationCoordinates
open ConfigurationLocalization

/-- A particle coordinate, viewed as a real-valued counting-equation test. -/
def test {N D : ℕ} (i : Fin N × Fin D) (z : Configuration N D) : ℝ := z i.1 i.2

/-- Equality of all real-valued particle coordinates is equality of states. -/
theorem separate {N D : ℕ} (x y : Configuration N D)
    (h : ∀ i, test i x = test i y) : x = y := by
  funext i d
  have hi : (x i d : ℝ) = (y i d : ℝ) := h (i, d)
  exact_mod_cast hi

end ConfigurationCoordinates

section Configuration
open ConfigurationLocalization
variable {A : Type*} [MeasurableSpace A] {N D : ℕ}
  {κ : MomentScale} {q : Rates D (MomentLaw κ D)} (control : LyapunovControl κ q)
  (hN : 0 < N) (initial : A → Configuration N D)
  (μ : Measure A) [IsProbabilityMeasure μ] (hinit : Measurable initial)
  (hV : Integrable (fun a => lyapunov control (initial a)) μ)
include hinit hV

/-- The actual empirical particle process is pathwise unique among cadlag
configuration-valued solutions with the same initial record and marked noise. -/
theorem configuration_candidate_eq_process
    (X : Sample A (Label N D) → ℝ → Configuration N D)
    (hcadlag : ∀ᵐ p ∂law μ (Label N D),
      (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (X p) (Ici t) t) ∧
      (∀ t : ℝ, 0 < t → ∃ y : Configuration N D, Tendsto (X p) (𝓝[<] t) (𝓝 y)))
    (hzero : ∀ᵐ p ∂law μ (Label N D), X p 0 = initial p.1)
    (heq : ∀ z : Configuration N D, ∀ᵐ p ∂law μ (Label N D), ∀ T : ℝ≥0,
      stateTest z (X p T) - stateTest z (initial p.1) =
        ∑ j : Label N D, ∫ r, candidateIncrement jump (rate κ q hN) X 0
          (stateTest z) j T (p,r) ∂MarkedNoise.countingMeasure j p.2) :
    ∀ᵐ p ∂law μ (Label N D), ∀ t : ℝ, 0 ≤ t →
      X p t = ConfigurationNonexplosion.process control hN initial p t :=
  GlobalCountingUniqueness.ae_candidate_eq_process (lyapunov control)
    (finite_sublevel control hN) jump (rate κ q hN) initial 0 μ
    (ConfigurationNonexplosion.ae_exhaustive control hN initial μ hinit hV)
    X hcadlag hzero heq

/-- The original finite set of particle-coordinate counting equations alone
suffices for uniqueness; candidate singleton or nonlinear test equations are
not required. No chain-rule premise is used to pass between the two forms. -/
theorem configuration_eq_of_coordinate_equations
    (X : Sample A (Label N D) → ℝ → Configuration N D)
    (hcadlag : ∀ᵐ p ∂law μ (Label N D),
      (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (X p) (Ici t) t) ∧
      (∀ t : ℝ, 0 < t → ∃ y : Configuration N D, Tendsto (X p) (𝓝[<] t) (𝓝 y)))
    (hzero : ∀ᵐ p ∂law μ (Label N D), X p 0 = initial p.1)
    (heq : ∀ i : Fin N × Fin D, ∀ᵐ p ∂law μ (Label N D), ∀ T : ℝ≥0,
      (X p T i.1 i.2 : ℝ) - (initial p.1 i.1 i.2 : ℝ) =
        ∑ j : Label N D, ∫ r, candidateIncrement jump (rate κ q hN) X 0
          (ConfigurationCoordinates.test i) j T (p,r) ∂MarkedNoise.countingMeasure j p.2) :
    ∀ᵐ p ∂law μ (Label N D), ∀ t : ℝ, 0 ≤ t →
      X p t = ConfigurationNonexplosion.process control hN initial p t :=
  GlobalCountingUniqueness.ae_candidate_eq_process_of_separating_tests
    (lyapunov control) (finite_sublevel control hN) jump (rate κ q hN) initial 0 μ
    ConfigurationCoordinates.test ConfigurationCoordinates.separate
    (ConfigurationNonexplosion.ae_exhaustive control hN initial μ hinit hV)
    X hcadlag hzero heq

end Configuration
end CarryingCapacity.ActualGlobalUniqueness
