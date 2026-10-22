import CarryingCapacity.FrozenCountingIdentity
import CarryingCapacity.InitialFrozenCompensation

/-!
# The actual initialized test-function counting equation

The base chronological counting identity is lifted to the genuine product
law with an arbitrary initial record. Almost-sure equality of the constructed
increments identifies its integrals with the initialized predictable versions.
No integrability or initial-law moment assumption is imposed on this pathwise
identity; local finiteness also supplies pathwise integrability separately.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators

namespace CarryingCapacity.InitialFrozenCountingIdentity
open CommonInitialNoise InitialFrozenPredictable InitialFrozenCompensation

variable {A J E : Type*} [MeasurableSpace A] [Fintype J] [DecidableEq E]
  [TopologicalSpace E] [PolishSpace E]
  (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ) (initial : A → E)

omit [MeasurableSpace A] [Fintype J] [PolishSpace E] in
/-- The accepted increment already vanishes above its height cutoff. -/
theorem horizonIncrement_eq_time_indicator (C : ℝ) (e : E) (V : E → ℝ)
    (j : J) (T : ℝ) (p : Sample A J) :
    (fun q => horizonIncrement active jump rate initial C e V j T (p, q)) =
      (Ioc 0 T ×ˢ univ).indicator
        (fun q => jumpIncrement active jump rate initial C e V j (p, q)) := by
  classical
  funext q
  by_cases hT : q.1 ≤ T <;> by_cases hC : q.2 ≤ C <;> by_cases hp : 0 < q.1 <;>
    simp [horizonIncrement, PredictableSets.rectangle, jumpIncrement,
      Set.indicator_apply, hT, hC, hp]

/-- All initialized horizon integrands agree with the base construction on
one event, simultaneously for cutoffs, fallbacks, test functions and horizons. -/
theorem ae_horizonIncrement_eq_base (μ : Measure A) : ∀ᵐ p ∂law μ J,
    ∀ C e V j T,
      (fun q => horizonIncrement active jump rate initial C e V j T (p, q)) =
        (Ioc 0 T ×ˢ univ).indicator
          (fun q => FrozenPredictableIntegrand.jumpIncrement active jump rate C
            (initial p.1) V j (p.2, q)) := by
  filter_upwards [ae_jumpIncrement_eq_base active jump rate initial μ] with p hp
  intro C e V j T
  rw [horizonIncrement_eq_time_indicator]
  exact congrArg (fun f : ℝ × ℝ → ℝ => (Ioc 0 T ×ˢ univ).indicator f)
    (funext (fun q => hp C e V j q.1 q.2))

/-- Finite event support gives integrability for each actual realization on
one probability-one event, without an input moment bound. -/
theorem ae_integrable_horizonIncrement (μ : Measure A) : ∀ᵐ p ∂law μ J,
    ∀ C e T (V : E → ℝ) (j : J),
      Integrable (fun q => horizonIncrement active jump rate initial C e V j T (p, q))
        (MarkedNoise.countingMeasure j p.2) := by
  filter_upwards [ae_horizonIncrement_eq_base active jump rate initial μ,
    ae_noise μ (FrozenCountingIdentity.ae_integrable_jumpIncrement active jump rate)]
    with p he hi
  intro C e T V j
  rw [he C e V j T, integrable_indicator_iff (measurableSet_Ioc.prod MeasurableSet.univ)]
  exact hi C (initial p.1) T V j

/-- The actual initialized frozen path satisfies its test-function jump
equation with the original counting measures and the proved predictable
initialized increments. All cutoffs, fallbacks and horizons share one event. -/
theorem ae_testFunction_counting_identity (μ : Measure A) (V : E → ℝ) :
    ∀ᵐ p ∂law μ J, ∀ C e T,
      V (process active jump rate initial C p T) - V (process active jump rate initial C p 0) =
        ∑ j : J, ∫ q, horizonIncrement active jump rate initial C e V j T (p, q)
          ∂MarkedNoise.countingMeasure j p.2 := by
  filter_upwards [ae_horizonIncrement_eq_base active jump rate initial μ,
    ae_noise μ (FrozenCountingIdentity.ae_testFunction_counting_identity active jump rate V)]
    with p he hp
  intro C e T
  change V (CommonFrozenProcess.process active jump rate C (initial p.1) p.2 T) -
    V (CommonFrozenProcess.process active jump rate C (initial p.1) p.2 0) = _
  rw [hp C (initial p.1) T]
  apply Finset.sum_congr rfl
  intro j _
  rw [he C e V j T, integral_indicator (measurableSet_Ioc.prod MeasurableSet.univ)]

end CarryingCapacity.InitialFrozenCountingIdentity
