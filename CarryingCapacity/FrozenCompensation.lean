import CarryingCapacity.FrozenPredictableIntegrand
import CarryingCapacity.FrozenIntensity
import CarryingCapacity.PredictableIntegral

/-!
# Compensation for actual frozen jump increments

The actual predictable pre-jump state is inserted into the finite-region
increment. Integrability follows from the finite active set and finite
time-height support, rather than from an assumed stochastic moment estimate.
Signed predictable compensation then gives an expectation identity for the
actual counting-measure integral and proves its integrability.
-/

noncomputable section
open MeasureTheory Set

namespace CarryingCapacity.FrozenCompensation
open MarkedNoise MarkedIntensity PredictableSets PredictableCompensation
  FrozenPredictableIntegrand FrozenIntensity PredictableIntegral

variable {J E : Type*} [Fintype J] [DecidableEq E]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)

/-- The actual accepted jump increment up to a deterministic horizon. -/
def horizonIncrement (C : ℝ) (x : E) (V : E → ℝ) (j : J) (T : ℝ) :
    SamplePoint J → ℝ :=
  (rectangle univ 0 T (Iic C)).indicator (jumpIncrement active jump rate C x V j)

theorem measurable_horizonIncrement (C : ℝ) (x : E) (V : E → ℝ) (j : J) (T : ℝ) :
    Measurable[predictable (CommonNoiseFiltration.filtration J)]
      (horizonIncrement active jump rate C x V j T) :=
  (measurable_jumpIncrement active jump rate C x V j).indicator
    (measurableSet_predictable_rectangle (CommonNoiseFiltration.filtration J)
      0 T le_rfl univ MeasurableSet.univ (Iic C) measurableSet_Iic)

omit [Fintype J] [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [PolishSpace E] [BorelSpace E] in
theorem horizonIncrement_eq_localizedIncrement (C : ℝ) (x : E)
    (V : E → ℝ) (j : J) (T : ℝ) :
    horizonIncrement active jump rate C x V j T =
      localizedIncrement active jump rate V j
        (fun p => preState active jump rate C x p.1 p.2.1) T C := by
  classical
  funext p
  simp only [horizonIncrement, rectangle, Set.indicator, mem_prod, mem_univ,
    true_and, mem_Ioc, mem_Iic, jumpIncrement, localizedIncrement]
  split_ifs <;> simp_all

/-- The deterministic finite-region estimate applies to the actual pre-jump
state, whose ambient measurability follows from its proved predictability. -/
theorem integrable_horizonIncrement_product (C : ℝ) (x : E)
    (V : E → ℝ) (j : J) (T : ℝ) :
    Integrable (horizonIncrement active jump rate C x V j T) (productIntensity J) := by
  rw [horizonIncrement_eq_localizedIncrement]
  exact integrable_localizedIncrement (law J) active jump rate V j _
    ((measurable_preState active jump rate C x).mono (predictable_le _) le_rfl) T C

/-- Integrability also holds against the actual Campbell measure. -/
theorem integrable_horizonIncrement_campbell (C : ℝ) (x : E)
    (V : E → ℝ) (j : J) (T : ℝ) :
    Integrable (horizonIncrement active jump rate C x V j T) (campbell j) :=
  (integrable_campbell_iff j _
    (measurable_horizonIncrement active jump rate C x V j T).stronglyMeasurable).mpr
      (integrable_horizonIncrement_product active jump rate C x V j T)

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

/-- Deterministic intensity sections are integrable almost surely as well. -/
theorem ae_integrable_horizonIncrement_intensity (C : ℝ) (x : E)
    (V : E → ℝ) (j : J) (T : ℝ) :
    ∀ᵐ ω ∂law J, Integrable
      (fun p => horizonIncrement active jump rate C x V j T (ω,p))
        (positiveVolume.prod positiveVolume) :=
  (integrable_horizonIncrement_product active jump rate C x V j T).prod_right_ae

theorem integrable_horizon_intensityIntegral (C : ℝ) (x : E)
    (V : E → ℝ) (j : J) (T : ℝ) :
    Integrable
      (fun ω => ∫ p, horizonIncrement active jump rate C x V j T (ω,p)
        ∂positiveVolume.prod positiveVolume) (law J) :=
  (integrable_horizonIncrement_product active jump rate C x V j T).integral_prod_left

/-- The actual signed random-measure sections are integrable almost surely. -/
theorem ae_integrable_horizonIncrement_counting (C : ℝ) (x : E)
    (V : E → ℝ) (j : J) (T : ℝ) :
    ∀ᵐ ω ∂law J, Integrable
      (fun p => horizonIncrement active jump rate C x V j T (ω,p)) (countingMeasure j ω) :=
  ae_integrable_counting j _
    (measurable_horizonIncrement active jump rate C x V j T).stronglyMeasurable
    (integrable_horizonIncrement_product active jump rate C x V j T)

/-- Thus the counting integral is an integrable random variable. -/
theorem integrable_horizon_countingIntegral (C : ℝ) (x : E)
    (V : E → ℝ) (j : J) (T : ℝ) :
    Integrable
      (fun ω => ∫ p, horizonIncrement active jump rate C x V j T (ω,p)
        ∂countingMeasure j ω) (law J) :=
  integrable_counting_integral j _
    (measurable_horizonIncrement active jump rate C x V j T).stronglyMeasurable
    (integrable_horizonIncrement_product active jump rate C x V j T)

/-- Signed compensation for the actual finite-horizon frozen increment,
with every integrability premise discharged by the finite-region bound. -/
theorem compensation_horizonIncrement (C : ℝ) (x : E)
    (V : E → ℝ) (j : J) (T : ℝ) :
    (∫ ω, ∫ p, horizonIncrement active jump rate C x V j T (ω,p)
      ∂countingMeasure j ω ∂law J) =
    ∫ ω, ∫ p, horizonIncrement active jump rate C x V j T (ω,p)
      ∂positiveVolume.prod positiveVolume ∂law J :=
  compensation_integrable j _
    (measurable_horizonIncrement active jump rate C x V j T).stronglyMeasurable
    (integrable_horizonIncrement_product active jump rate C x V j T)

end CarryingCapacity.FrozenCompensation
