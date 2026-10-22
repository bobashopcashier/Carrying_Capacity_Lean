import CarryingCapacity.GlobalCountingUniqueness
import CarryingCapacity.TimeDependentEquationUniqueness
import CarryingCapacity.TimeDependentGlobalCounting

/-!
# Pathwise uniqueness against the actual time-dependent global construction

A candidate is required to have discrete cadlag paths, the prescribed initial
value, and the same rate-threshold counting equations. Its pre-state is defined
from its own strict-past approximants and is proved to be its genuine left
limit. Countability puts the singleton test equations on one event before
applying deterministic uniqueness at any sample-dependent disagreement state.

No candidate finite-activity, bounded-rate, localization-agreement, or moment
hypothesis is imposed. Exit exhaustion concerns only the constructed process
and is supplied by the separate Lyapunov nonexplosion theorem.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical Topology ENNReal NNReal BigOperators

namespace CarryingCapacity.TimeDependentGlobalUniqueness
open CommonInitialNoise LyapunovLocalization TimeDependentLocalization PredictableStepApproximation
open CountingEquationUniqueness TimeDependentEquationUniqueness
open GlobalCountingUniqueness (candidatePreState tendsto_candidatePreState)

variable {A E J : Type*} [TopologicalSpace E]

/-- The actual unrestricted rate-threshold integrand for a candidate path. -/
def candidateIncrement (jump : J → E → E) (rate : J → ℝ → E → ℝ)
    (X : Sample A J → ℝ → E) (e : E) (f : E → ℝ) (j : J)
    (T : ℝ) (p : Sample A J × (ℝ × ℝ)) : ℝ :=
  increment jump rate (candidatePreState X e p.1) f j T p.2

section Global
variable [MeasurableSpace A] [DecidableEq E] [Fintype J] [Countable E]
  [PolishSpace E] [DiscreteTopology E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (hbounded : ∀ n : ℕ, ∃ C : ℝ, ∀ x ∈ active V hfinite n, ∀ j t, rate j t x ≤ C)
  (initial : A → E) (e : E)
  (μ : Measure A)

omit [MeasurableSpace A] [Countable E] [PolishSpace E] [DiscreteTopology E] [Fintype J] μ in
/-- The constructed global integrand is exactly the same unrestricted
integrand used in the deterministic uniqueness theorem. -/
theorem horizonIncrement_eq_increment (f : E → ℝ) (j : J) (T : ℝ) (p : Sample A J) :
    (fun q => TimeDependentGlobalCounting.horizonIncrement
      V hfinite jump rate hbounded initial e f j T (p,q)) =
    increment jump rate (TimeDependentGlobalCounting.preState
      V hfinite jump rate hbounded initial e p) f j T := by
  funext q
  exact TimeDependentGlobalCounting.horizonIncrement_apply
    V hfinite jump rate hbounded initial e f j T p q

omit [Countable E] in
/-- A countable separating test family gives the same pathwise comparison.
Finite coordinate equations are enough for the configuration specialization. -/
theorem ae_candidate_eq_process_of_separating_tests {I : Type*} [Countable I]
    (test : I → E → ℝ)
    (hseparate : ∀ x y : E, (∀ i, test i x = test i y) → x = y)
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rate hbounded initial n p)
    (X : Sample A J → ℝ → E)
    (hcadlag : ∀ᵐ p ∂law μ J,
      (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (X p) (Ici t) t) ∧
      (∀ t : ℝ, 0 < t → ∃ y : E, Tendsto (X p) (𝓝[<] t) (𝓝 y)))
    (hzero : ∀ᵐ p ∂law μ J, X p 0 = initial p.1)
    (heq : ∀ i : I, ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0,
      test i (X p T) - test i (initial p.1) =
        ∑ j : J, ∫ q, candidateIncrement jump rate X e (test i) j T (p,q)
          ∂MarkedNoise.countingMeasure j p.2) :
    ∀ᵐ p ∂law μ J, ∀ t : ℝ, 0 ≤ t →
      X p t = TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p t := by
  have hgEq := ae_all_iff.mpr (fun i : I =>
    TimeDependentGlobalCounting.ae_testFunction_counting_identity
      V hfinite jump rate hbounded initial e μ (test i) hexhaust)
  filter_upwards [hcadlag, hzero, ae_all_iff.mpr heq,
    TimeDependentGlobalProcess.ae_process_cadlag V hfinite jump rate hbounded initial e μ hexhaust,
    TimeDependentGlobalProcess.ae_process_zero V hfinite jump rate hbounded initial e μ,
    TimeDependentGlobalCounting.ae_tendsto_preState
      V hfinite jump rate hbounded initial e μ hexhaust, hgEq]
    with p hc hz hxEq hg hgzero hgpre hgEq
  apply eq_of_separating_counting_equations test hseparate jump rate
    (fun j => MarkedNoise.countingMeasure j p.2)
    (X p) (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p)
    (candidatePreState X e p)
    (TimeDependentGlobalCounting.preState V hfinite jump rate hbounded initial e p)
    hc.1 hg.1 (tendsto_candidatePreState X e p hc.2) hgpre (hz.trans hgzero.symm)
  · intro i T hT
    rw [hz]
    exact hxEq i ⟨T, hT⟩
  · intro i T hT
    rw [hgzero]
    convert hgEq i ⟨T, hT⟩ using 1
    apply Finset.sum_congr rfl
    intro j _
    rw [horizonIncrement_eq_increment]
    rfl

/-- Any discrete cadlag candidate solving the same counting equation with
same initial record and actual noise is indistinguishable on nonnegative times.
The singleton equations may initially have different null sets; countability
of the state space provides the common event used by the proof. -/
theorem ae_candidate_eq_process
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rate hbounded initial n p)
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
      X p t = TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p t := by
  have hgEq := ae_all_iff.mpr (fun z : E =>
    TimeDependentGlobalCounting.ae_testFunction_counting_identity
      V hfinite jump rate hbounded initial e μ (stateTest z) hexhaust)
  filter_upwards [hcadlag, hzero, ae_all_iff.mpr heq,
    TimeDependentGlobalProcess.ae_process_cadlag V hfinite jump rate hbounded initial e μ hexhaust,
    TimeDependentGlobalProcess.ae_process_zero V hfinite jump rate hbounded initial e μ,
    TimeDependentGlobalCounting.ae_tendsto_preState
      V hfinite jump rate hbounded initial e μ hexhaust, hgEq]
    with p hc hz hxEq hg hgzero hgpre hgEq
  apply eq_of_counting_equations jump rate (fun j => MarkedNoise.countingMeasure j p.2)
    (X p) (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p)
    (candidatePreState X e p)
    (TimeDependentGlobalCounting.preState V hfinite jump rate hbounded initial e p)
    hc.1 hg.1 (tendsto_candidatePreState X e p hc.2) hgpre (hz.trans hgzero.symm)
  · intro z T hT
    rw [hz]
    exact hxEq z ⟨T, hT⟩
  · intro z T hT
    rw [hgzero]
    convert hgEq z ⟨T, hT⟩ using 1
    apply Finset.sum_congr rfl
    intro j _
    rw [horizonIncrement_eq_increment]
    rfl

end Global
end CarryingCapacity.TimeDependentGlobalUniqueness
