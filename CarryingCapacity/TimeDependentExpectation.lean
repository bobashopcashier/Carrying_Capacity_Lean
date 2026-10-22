import CarryingCapacity.TimeDependentDynkin
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Continuity of actual time-dependent frozen expectations

Measurable time-dependent rates with one active-state cap on nonnegative times
give a deterministic generator bound. Together with the proved actual Dynkin
formula this makes the test-function expectation a Lebesgue integral primitive
and proves it Lipschitz on nonnegative times. No continuity of the rates, or
continuity or drift inequality of the expected value, is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace CarryingCapacity.TimeDependentExpectation
open CommonInitialNoise TimeDependentInitial TimeDependentGeneratorIntegral

variable {A J E : Type*} [MeasurableSpace A] [Fintype J] [DecidableEq E]
  (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ) (initial : A → E)

/-- The actual current-state generator as a sample-time field. -/
def generatorField (C : ℝ) (V : E → ℝ) (p : Sample A J × ℝ) : ℝ :=
  frozenGenerator active jump rate V p.2 (process active jump rate initial C p.1 p.2)

/-- The expected actual generator at a deterministic time. -/
def expectedGenerator (μ : Measure A) (C : ℝ) (V : E → ℝ) (t : ℝ) : ℝ :=
  ∫ p, generatorField active jump rate initial C V (p,t) ∂law μ J

/-- The actual test-function expectation. Its integrability is proved below
from the initial test moment, through the already proved Dynkin construction. -/
def expectation (μ : Measure A) (C : ℝ) (V : E → ℝ) (t : ℝ) : ℝ :=
  ∫ p, V (process active jump rate initial C p t) ∂law μ J

variable [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]

theorem measurable_generatorField (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (V : E → ℝ) :
    Measurable (generatorField active jump rate initial C V) :=
  (measurable_frozenGenerator active jump rate hRate V).comp
    (measurable_snd.prodMk (measurable_process active jump rate initial hRate hinit C))

/-- Integrability at each nonnegative time follows from the active-state cap. -/
theorem integrable_generator_at (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x)) (hinit : Measurable initial)
    (C : ℝ) (V : E → ℝ)
    (hq : ∀ y ∈ active, ∀ j s, 0 ≤ s → 0 ≤ rate j s y)
    (hbound : ∀ y ∈ active, ∀ j s, 0 ≤ s → rate j s y ≤ C)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun p => frozenGenerator active jump rate V t
      (process active jump rate initial C p t)) (law μ J) := by
  have hm := (measurable_generatorField active jump rate initial hRate hinit C V).comp
    (measurable_id.prodMk (measurable_const (a := t)))
  exact ⟨hm.aestronglyMeasurable, hasFiniteIntegral_of_bounded
    (Eventually.of_forall (fun _ => norm_frozenGenerator_le active jump rate V C t
      (fun y hy j => hq y hy j t ht) (fun y hy j => hbound y hy j t ht) _))⟩

theorem stronglyMeasurable_expectedGenerator (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x)) (hinit : Measurable initial)
    (C : ℝ) (V : E → ℝ) :
    StronglyMeasurable (expectedGenerator active jump rate initial μ C V) :=
  (measurable_generatorField active jump rate initial hRate hinit C V).stronglyMeasurable.integral_prod_left'

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] in
theorem norm_expectedGenerator_le (μ : Measure A) [IsProbabilityMeasure μ]
    (C : ℝ) (V : E → ℝ)
    (hq : ∀ y ∈ active, ∀ j s, 0 ≤ s → 0 ≤ rate j s y)
    (hbound : ∀ y ∈ active, ∀ j s, 0 ≤ s → rate j s y ≤ C)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖expectedGenerator active jump rate initial μ C V t‖ ≤ generatorBound active jump V C := by
  have h := norm_integral_le_of_norm_le_const (μ := law μ J)
    (Eventually.of_forall (fun p : Sample A J => norm_frozenGenerator_le active jump rate V C t
      (fun y hy j => hq y hy j t ht) (fun y hy j => hbound y hy j t ht)
      (process active jump rate initial C p t)))
  simpa only [expectedGenerator, generatorField, measureReal_univ_eq_one, mul_one] using h

/-- The expected generator is genuinely integrable on every bounded
nonnegative interval. -/
theorem integrableOn_expectedGenerator (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x)) (hinit : Measurable initial)
    (C : ℝ) (V : E → ℝ)
    (hq : ∀ y ∈ active, ∀ j u, 0 ≤ u → 0 ≤ rate j u y)
    (hbound : ∀ y ∈ active, ∀ j u, 0 ≤ u → rate j u y ≤ C)
    (s t : ℝ) (hs : 0 ≤ s) :
    IntegrableOn (expectedGenerator active jump rate initial μ C V) (Ioc s t) := by
  letI : IsFiniteMeasure (volume.restrict (Ioc s t)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  refine ⟨(stronglyMeasurable_expectedGenerator active jump rate initial μ hRate hinit C V).aestronglyMeasurable,
    hasFiniteIntegral_of_bounded (C := generatorBound active jump V C) ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  exact norm_expectedGenerator_le active jump rate initial μ C V hq hbound u (hs.trans hu.1.le)

theorem intervalIntegrable_expectedGenerator (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x)) (hinit : Measurable initial)
    (C : ℝ) (V : E → ℝ)
    (hq : ∀ y ∈ active, ∀ j u, 0 ≤ u → 0 ≤ rate j u y)
    (hbound : ∀ y ∈ active, ∀ j u, 0 ≤ u → rate j u y ≤ C)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IntervalIntegrable (expectedGenerator active jump rate initial μ C V) volume s t :=
  ⟨integrableOn_expectedGenerator active jump rate initial μ hRate hinit C V hq hbound s t hs,
    integrableOn_expectedGenerator active jump rate initial μ hRate hinit C V hq hbound t s ht⟩

variable [TopologicalSpace E] [PolishSpace E] [BorelSpace E]

/-- Actual initialized Dynkin with the generator expectation inside the
ordinary Lebesgue time integral. -/
theorem expectation_eq_initial_add_integral (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x)) (hinit : Measurable initial)
    (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j s, 0 ≤ s → 0 ≤ rate j s y)
    (hbound : ∀ y ∈ active, ∀ j s, 0 ≤ s → rate j s y ≤ C)
    (hV : Integrable (fun a => V (initial a)) μ) :
    expectation active jump rate initial μ C V T = (∫ a, V (initial a) ∂μ) +
      ∫ s in Ioc 0 T, expectedGenerator active jump rate initial μ C V s :=
  TimeDependentDynkin.dynkin_expectation_integral active jump rate initial μ hRate hinit C e V T
    (fun y hy j s hs => hq y hy j s hs.1.le)
    (fun y hy j s hs => hbound y hy j s hs.1.le) hV

theorem expectation_sub_eq_integral (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x)) (hinit : Measurable initial)
    (C : ℝ) (e : E) (V : E → ℝ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hq : ∀ y ∈ active, ∀ j u, 0 ≤ u → 0 ≤ rate j u y)
    (hbound : ∀ y ∈ active, ∀ j u, 0 ≤ u → rate j u y ≤ C)
    (hV : Integrable (fun a => V (initial a)) μ) :
    expectation active jump rate initial μ C V t - expectation active jump rate initial μ C V s =
      ∫ u in s..t, expectedGenerator active jump rate initial μ C V u := by
  rw [expectation_eq_initial_add_integral active jump rate initial μ hRate hinit C e V t hq hbound hV,
    expectation_eq_initial_add_integral active jump rate initial μ hRate hinit C e V s hq hbound hV,
    ← intervalIntegral.integral_of_le ht, ← intervalIntegral.integral_of_le hs]
  simpa only [add_sub_add_left_eq_sub] using
    intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_expectedGenerator active jump rate initial μ hRate hinit C V hq hbound 0 t le_rfl ht)
      (intervalIntegrable_expectedGenerator active jump rate initial μ hRate hinit C V hq hbound 0 s le_rfl hs)

/-- The finite generator bound controls the variation of the actual expected
value even when the rates are merely measurable in time. -/
theorem norm_expectation_sub_le (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x)) (hinit : Measurable initial)
    (C : ℝ) (e : E) (V : E → ℝ) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hq : ∀ y ∈ active, ∀ j u, 0 ≤ u → 0 ≤ rate j u y)
    (hbound : ∀ y ∈ active, ∀ j u, 0 ≤ u → rate j u y ≤ C)
    (hV : Integrable (fun a => V (initial a)) μ) :
    ‖expectation active jump rate initial μ C V t - expectation active jump rate initial μ C V s‖ ≤
      generatorBound active jump V C * |t - s| := by
  rw [expectation_sub_eq_integral active jump rate initial μ hRate hinit C e V s t hs ht hq hbound hV]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro u hu
  exact norm_expectedGenerator_le active jump rate initial μ C V hq hbound u
    ((le_min hs ht).trans hu.1.le)

theorem lipschitzOnWith_expectation (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x)) (hinit : Measurable initial)
    (C : ℝ) (e : E) (V : E → ℝ)
    (hq : ∀ y ∈ active, ∀ j u, 0 ≤ u → 0 ≤ rate j u y)
    (hbound : ∀ y ∈ active, ∀ j u, 0 ≤ u → rate j u y ≤ C)
    (hV : Integrable (fun a => V (initial a)) μ) :
    LipschitzOnWith ⟨generatorBound active jump V C, generatorBound_nonneg active jump V C⟩
      (expectation active jump rate initial μ C V) (Ici 0) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht s hs
  simpa only [Real.dist_eq, Real.norm_eq_abs] using
    norm_expectation_sub_le active jump rate initial μ hRate hinit C e V s t hs ht hq hbound hV

theorem continuousOn_expectation (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x)) (hinit : Measurable initial)
    (C : ℝ) (e : E) (V : E → ℝ)
    (hq : ∀ y ∈ active, ∀ j u, 0 ≤ u → 0 ≤ rate j u y)
    (hbound : ∀ y ∈ active, ∀ j u, 0 ≤ u → rate j u y ≤ C)
    (hV : Integrable (fun a => V (initial a)) μ) :
    ContinuousOn (expectation active jump rate initial μ C V) (Ici 0) :=
  (lipschitzOnWith_expectation active jump rate initial μ hRate hinit C e V hq hbound hV).continuousOn

end CarryingCapacity.TimeDependentExpectation
