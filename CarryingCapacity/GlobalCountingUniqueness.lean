import CarryingCapacity.CountingEquationUniqueness
import CarryingCapacity.GlobalLocalizedCountingIdentity

/-!
# Pathwise uniqueness against the actual global construction

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

namespace CarryingCapacity.GlobalCountingUniqueness
open CommonInitialNoise LyapunovLocalization PredictableStepApproximation
open CountingEquationUniqueness

variable {A E J : Type*} [TopologicalSpace E]

/-- A candidate's strict-past version is built from its own path. -/
def candidatePreState (X : Sample A J → ℝ → E) (e : E) (p : Sample A J) (t : ℝ) : E :=
  pastLimit (fun s p => X p s) e p t

/-- The actual unrestricted rate-threshold integrand for a candidate path. -/
def candidateIncrement (jump : J → E → E) (rate : J → E → ℝ)
    (X : Sample A J → ℝ → E) (e : E) (f : E → ℝ) (j : J)
    (T : ℝ) (p : Sample A J × (ℝ × ℝ)) : ℝ :=
  increment jump rate (candidatePreState X e p.1) f j T p.2

section Limits
variable [PolishSpace E]

/-- The candidate pre-state is identified from actual left limits, rather
than assuming an independent pre-state process satisfies a limit relation. -/
theorem tendsto_candidatePreState (X : Sample A J → ℝ → E) (e : E)
    (p : Sample A J)
    (hleft : ∀ t : ℝ, 0 < t → ∃ y : E, Tendsto (X p) (𝓝[<] t) (𝓝 y)) :
    ∀ t : ℝ, 0 < t → Tendsto (X p) (𝓝[<] t) (𝓝 (candidatePreState X e p t)) := by
  intro t ht
  obtain ⟨y, hy⟩ := hleft t ht
  have he : candidatePreState X e p t = y :=
    pastLimit_eq_of_tendsto _ e p t ht y hy
  rwa [he]

end Limits

section Global
variable [MeasurableSpace A] [DecidableEq E] [Fintype J] [Countable E]
  [PolishSpace E] [DiscreteTopology E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → E → ℝ) (initial : A → E) (e : E)
  (μ : Measure A)

omit [MeasurableSpace A] [Countable E] [PolishSpace E] [DiscreteTopology E] μ in
/-- The constructed global integrand is exactly the same unrestricted
integrand used in the deterministic uniqueness theorem. -/
theorem horizonIncrement_eq_increment (f : E → ℝ) (j : J) (T : ℝ) (p : Sample A J) :
    (fun q => GlobalLocalizedCountingIdentity.horizonIncrement
      V hfinite jump rate initial e f j T (p,q)) =
    increment jump rate (GlobalLocalizedCountingIdentity.preState
      V hfinite jump rate initial e p) f j T := by
  funext q
  exact GlobalLocalizedCountingIdentity.horizonIncrement_apply
    V hfinite jump rate initial e f j T p q

omit [Countable E] in
/-- A countable separating test family gives the same pathwise comparison.
Finite coordinate equations are enough for the configuration specialization. -/
theorem ae_candidate_eq_process_of_separating_tests {I : Type*} [Countable I]
    (test : I → E → ℝ)
    (hseparate : ∀ x y : E, (∀ i, test i x = test i y) → x = y)
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rate initial n p)
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
      X p t = GlobalLocalizedProcess.process V hfinite jump rate initial e p t := by
  have hgEq := ae_all_iff.mpr (fun i : I =>
    GlobalLocalizedCountingIdentity.ae_testFunction_counting_identity
      V hfinite jump rate initial e μ (test i) hexhaust)
  filter_upwards [hcadlag, hzero, ae_all_iff.mpr heq,
    GlobalLocalizedProcess.ae_process_cadlag V hfinite jump rate initial e μ hexhaust,
    GlobalLocalizedProcess.ae_process_zero V hfinite jump rate initial e μ,
    GlobalLocalizedCountingIdentity.ae_tendsto_preState
      V hfinite jump rate initial e μ hexhaust, hgEq]
    with p hc hz hxEq hg hgzero hgpre hgEq
  apply eq_of_separating_counting_equations test hseparate jump rate
    (fun j => MarkedNoise.countingMeasure j p.2)
    (X p) (GlobalLocalizedProcess.process V hfinite jump rate initial e p)
    (candidatePreState X e p)
    (GlobalLocalizedCountingIdentity.preState V hfinite jump rate initial e p)
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
      (T : ℝ≥0∞) < exit V hfinite jump rate initial n p)
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
      X p t = GlobalLocalizedProcess.process V hfinite jump rate initial e p t := by
  have hgEq := ae_all_iff.mpr (fun z : E =>
    GlobalLocalizedCountingIdentity.ae_testFunction_counting_identity
      V hfinite jump rate initial e μ (stateTest z) hexhaust)
  filter_upwards [hcadlag, hzero, ae_all_iff.mpr heq,
    GlobalLocalizedProcess.ae_process_cadlag V hfinite jump rate initial e μ hexhaust,
    GlobalLocalizedProcess.ae_process_zero V hfinite jump rate initial e μ,
    GlobalLocalizedCountingIdentity.ae_tendsto_preState
      V hfinite jump rate initial e μ hexhaust, hgEq]
    with p hc hz hxEq hg hgzero hgpre hgEq
  apply eq_of_counting_equations jump rate (fun j => MarkedNoise.countingMeasure j p.2)
    (X p) (GlobalLocalizedProcess.process V hfinite jump rate initial e p)
    (candidatePreState X e p)
    (GlobalLocalizedCountingIdentity.preState V hfinite jump rate initial e p)
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
end CarryingCapacity.GlobalCountingUniqueness
