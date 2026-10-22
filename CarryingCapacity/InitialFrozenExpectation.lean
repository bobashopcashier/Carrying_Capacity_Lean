import CarryingCapacity.InitialFrozenDynkin
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Time-integral and continuity forms of initialized frozen Dynkin

The current-state frozen generator is uniformly bounded because it vanishes
outside the finite active set. This proves joint sample-time integrability
and allows Fubini to turn the actual process's Dynkin formula into a Lebesgue
time primitive. Its expectation is Lipschitz on nonnegative times.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace CarryingCapacity.InitialFrozenExpectation
open CommonInitialNoise FrozenProcess MarkedIntensity

variable {A J E : Type*} [MeasurableSpace A] [Fintype J] [DecidableEq E]
  (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ) (initial : A → E)

/-- A deterministic bound on the entire frozen generator, including the
inactive states where it is zero. -/
def generatorBound (V : E → ℝ) : ℝ :=
  ∑ x ∈ active, |frozenGenerator active jump rate V x|

theorem generatorBound_nonneg (V : E → ℝ) : 0 ≤ generatorBound active jump rate V := by
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem norm_generator_le (V : E → ℝ) (x : E) :
    ‖frozenGenerator active jump rate V x‖ ≤ generatorBound active jump rate V := by
  by_cases hx : x ∈ active
  · simpa only [generatorBound, Real.norm_eq_abs] using
      (Finset.single_le_sum (fun y _ => abs_nonneg (frozenGenerator active jump rate V y)) hx)
  · simpa only [frozenGenerator, if_neg hx, norm_zero] using
      generatorBound_nonneg active jump rate V

variable [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]

/-- The current-state generator as a jointly measurable sample-time field. -/
def generatorField (C : ℝ) (V : E → ℝ) (p : Sample A J × ℝ) : ℝ :=
  frozenGenerator active jump rate V (process active jump rate initial C p.1 p.2)

theorem measurable_generatorField (hinit : Measurable initial) (C : ℝ) (V : E → ℝ) :
    Measurable (generatorField active jump rate initial C V) :=
  (measurable_of_countable _).comp (measurable_process active jump rate initial hinit C)

/-- No moment assumption on the initial state is needed for the bounded
current generator on a finite time horizon. -/
theorem integrable_generatorField (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (V : E → ℝ) (s t : ℝ) :
    Integrable (generatorField active jump rate initial C V)
      ((law μ J).prod (volume.restrict (Ioc s t))) := by
  letI : IsFiniteMeasure (volume.restrict (Ioc s t)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  exact ⟨(measurable_generatorField active jump rate initial hinit C V).aestronglyMeasurable,
    hasFiniteIntegral_of_bounded (Eventually.of_forall (fun p =>
      norm_generator_le active jump rate V _))⟩

/-- Each current-state generator evaluation is integrable, independently of
integrability of the initial test value. -/
theorem integrable_generator_at (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (V : E → ℝ) (t : ℝ) :
    Integrable (fun p => frozenGenerator active jump rate V
      (process active jump rate initial C p t)) (law μ J) := by
  have hm : Measurable (fun p : Sample A J => generatorField active jump rate initial C V (p, t)) :=
    (measurable_generatorField active jump rate initial hinit C V).comp
      (measurable_id.prodMk measurable_const)
  exact ⟨hm.aestronglyMeasurable, hasFiniteIntegral_of_bounded
    (Eventually.of_forall (fun _ => norm_generator_le active jump rate V _))⟩

/-- The deterministic expected current generator. -/
def expectedGenerator (μ : Measure A) (C : ℝ) (V : E → ℝ) (t : ℝ) : ℝ :=
  ∫ p, generatorField active jump rate initial C V (p, t) ∂law μ J

theorem stronglyMeasurable_expectedGenerator (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (V : E → ℝ) :
    StronglyMeasurable (expectedGenerator active jump rate initial μ C V) :=
  (measurable_generatorField active jump rate initial hinit C V).stronglyMeasurable.integral_prod_left'

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] in
theorem norm_expectedGenerator_le (μ : Measure A) [IsProbabilityMeasure μ]
    (C : ℝ) (V : E → ℝ) (t : ℝ) :
    ‖expectedGenerator active jump rate initial μ C V t‖ ≤ generatorBound active jump rate V := by
  have h := norm_integral_le_of_norm_le_const (μ := law μ J)
    (Eventually.of_forall (fun p : Sample A J => norm_generator_le active jump rate V
      (process active jump rate initial C p t)))
  simpa only [expectedGenerator, generatorField, measureReal_univ_eq_one, mul_one] using h

theorem integrableOn_expectedGenerator (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (V : E → ℝ) (s t : ℝ) :
    IntegrableOn (expectedGenerator active jump rate initial μ C V) (Ioc s t) := by
  letI : IsFiniteMeasure (volume.restrict (Ioc s t)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  exact ⟨(stronglyMeasurable_expectedGenerator active jump rate initial μ hinit C V).aestronglyMeasurable,
    hasFiniteIntegral_of_bounded (Eventually.of_forall (fun u =>
      norm_expectedGenerator_le active jump rate initial μ C V u))⟩

theorem intervalIntegrable_expectedGenerator (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (V : E → ℝ) (s t : ℝ) :
    IntervalIntegrable (expectedGenerator active jump rate initial μ C V) volume s t :=
  ⟨integrableOn_expectedGenerator active jump rate initial μ hinit C V s t,
    integrableOn_expectedGenerator active jump rate initial μ hinit C V t s⟩

/-- Fubini for the actual current generator, with product integrability
proved from the finite active set. -/
theorem integral_timeGenerator_swap (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (V : E → ℝ) (s t : ℝ) :
    (∫ p, ∫ u in Ioc s t, generatorField active jump rate initial C V (p, u) ∂volume ∂law μ J) =
      ∫ u in Ioc s t, expectedGenerator active jump rate initial μ C V u :=
  integral_integral_swap (integrable_generatorField active jump rate initial μ hinit C V s t)

theorem positiveVolume_restrict_Ioc_zero (T : ℝ) :
    positiveVolume.restrict (Ioc 0 T) = volume.restrict (Ioc 0 T) := by
  rw [positiveVolume, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (fun _ hx => hx.1.le)]

/-- The actual test-function expectation, as a function of time. -/
def expectation (μ : Measure A) (C : ℝ) (V : E → ℝ) (T : ℝ) : ℝ :=
  ∫ p, V (process active jump rate initial C p T) ∂law μ J

variable [TopologicalSpace E] [PolishSpace E] [BorelSpace E]

/-- Initialized Dynkin with expectation taken inside the ordinary Lebesgue
time integral. -/
theorem expectation_eq_initial_add_integral (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j, 0 ≤ rate j y)
    (hbound : ∀ y ∈ active, ∀ j, rate j y ≤ C)
    (hV : Integrable (fun a => V (initial a)) μ) :
    expectation active jump rate initial μ C V T = (∫ a, V (initial a) ∂μ) +
      ∫ s in Ioc 0 T, expectedGenerator active jump rate initial μ C V s := by
  have h := InitialFrozenDynkin.dynkin active jump rate initial μ hinit C e V T hq hbound hV
  simp_rw [positiveVolume_restrict_Ioc_zero] at h
  change expectation active jump rate initial μ C V T = (∫ a, V (initial a) ∂μ) +
    ∫ p, ∫ s in Ioc 0 T, generatorField active jump rate initial C V (p, s) ∂volume ∂law μ J at h
  rw [integral_timeGenerator_swap active jump rate initial μ hinit C V 0 T] at h
  exact h

theorem expectation_sub_eq_integral (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hq : ∀ y ∈ active, ∀ j, 0 ≤ rate j y)
    (hbound : ∀ y ∈ active, ∀ j, rate j y ≤ C)
    (hV : Integrable (fun a => V (initial a)) μ) :
    expectation active jump rate initial μ C V t - expectation active jump rate initial μ C V s =
      ∫ u in s..t, expectedGenerator active jump rate initial μ C V u := by
  rw [expectation_eq_initial_add_integral active jump rate initial μ hinit C e V t hq hbound hV,
    expectation_eq_initial_add_integral active jump rate initial μ hinit C e V s hq hbound hV,
    ← intervalIntegral.integral_of_le ht, ← intervalIntegral.integral_of_le hs]
  simpa only [add_sub_add_left_eq_sub] using
    intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_expectedGenerator active jump rate initial μ hinit C V 0 t)
      (intervalIntegrable_expectedGenerator active jump rate initial μ hinit C V 0 s)

/-- In fact the expected test function is globally Lipschitz on nonnegative
times, for each fixed finite active set. -/
theorem norm_expectation_sub_le (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hq : ∀ y ∈ active, ∀ j, 0 ≤ rate j y)
    (hbound : ∀ y ∈ active, ∀ j, rate j y ≤ C)
    (hV : Integrable (fun a => V (initial a)) μ) :
    ‖expectation active jump rate initial μ C V t - expectation active jump rate initial μ C V s‖ ≤
      generatorBound active jump rate V * |t - s| := by
  rw [expectation_sub_eq_integral active jump rate initial μ hinit C e V s t hs ht hq hbound hV]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun u _ =>
    norm_expectedGenerator_le active jump rate initial μ C V u)

theorem lipschitzOnWith_expectation (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ)
    (hq : ∀ y ∈ active, ∀ j, 0 ≤ rate j y)
    (hbound : ∀ y ∈ active, ∀ j, rate j y ≤ C)
    (hV : Integrable (fun a => V (initial a)) μ) :
    LipschitzOnWith ⟨generatorBound active jump rate V, generatorBound_nonneg active jump rate V⟩
      (expectation active jump rate initial μ C V) (Ici 0) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht s hs
  simpa only [Real.dist_eq, Real.norm_eq_abs] using
    norm_expectation_sub_le active jump rate initial μ hinit C e V s t hs ht hq hbound hV

theorem continuousOn_expectation (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ)
    (hq : ∀ y ∈ active, ∀ j, 0 ≤ rate j y)
    (hbound : ∀ y ∈ active, ∀ j, rate j y ≤ C)
    (hV : Integrable (fun a => V (initial a)) μ) :
    ContinuousOn (expectation active jump rate initial μ C V) (Ici 0) :=
  (lipschitzOnWith_expectation active jump rate initial μ hinit C e V hq hbound hV).continuousOn

end CarryingCapacity.InitialFrozenExpectation
