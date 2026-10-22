import CarryingCapacity.TimeDependentInitial
import CarryingCapacity.TimeDependentIntensity
import CarryingCapacity.InitialPredictableIntegral

/-!
# Compensation for independently initialized time-dependent frozen increments

Finite active states and finite time-height support give deterministic
integrability bounds for the actual initialized predictable increment.
The arbitrary initial law requires no moment assumption for this frozen
increment. Signed compensation and integrability of the actual random
counting integral then follow from the proved initial-product theory.
-/

noncomputable section
open MeasureTheory Set

namespace CarryingCapacity.TimeDependentInitialCompensation
open CommonInitialNoise MarkedIntensity PredictableSets InitialPredictableCompensation
  TimeDependentInitial TimeDependentIntensity InitialPredictableIntegral

variable {A J E : Type*} [MeasurableSpace A] [Fintype J] [DecidableEq E]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ) (initial : A → E)

/-- The actual initialized accepted increment up to a deterministic horizon. -/
def horizonIncrement (C : ℝ) (e : E) (V : E → ℝ) (j : J) (T : ℝ) :
    SamplePoint A J → ℝ :=
  (rectangle univ 0 T (Iic C)).indicator (jumpIncrement active jump rate initial C e V j)

theorem measurable_horizonIncrement (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial)
    (C : ℝ) (e : E) (V : E → ℝ) (j : J) (T : ℝ) :
    Measurable[predictable (filtration A J)]
      (horizonIncrement active jump rate initial C e V j T) :=
  (measurable_jumpIncrement active jump rate initial hRate hinit C e V j).indicator
    (measurableSet_predictable_rectangle (filtration A J)
      0 T le_rfl univ MeasurableSet.univ (Iic C) measurableSet_Iic)

omit [MeasurableSpace A] [Fintype J] [Countable E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [PolishSpace E] [BorelSpace E] in
theorem horizonIncrement_eq_localizedIncrement (C : ℝ) (e : E)
    (V : E → ℝ) (j : J) (T : ℝ) :
    horizonIncrement active jump rate initial C e V j T =
      localizedIncrement active jump rate V j
        (fun p => preState active jump rate initial C e p.1 p.2.1) T C := by
  classical
  funext p
  simp only [horizonIncrement, rectangle, Set.indicator, mem_prod, mem_univ,
    true_and, mem_Ioc, mem_Iic, jumpIncrement, localizedIncrement]
  split_ifs <;> simp_all

/-- The actual initialized field satisfies the deterministic finite-region
bound, so product integrability is proved rather than assumed. -/
theorem integrable_horizonIncrement_product (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (j : J) (T : ℝ) :
    Integrable (horizonIncrement active jump rate initial C e V j T)
      (productIntensity μ J) := by
  rw [horizonIncrement_eq_localizedIncrement]
  exact integrable_localizedIncrement (law μ J) active jump rate hRate V j _
    ((measurable_preState active jump rate initial hRate hinit C e).mono (predictable_le _) le_rfl) T C

/-- The actual initial-product Campbell integral is integrable as well. -/
theorem integrable_horizonIncrement_campbell (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (j : J) (T : ℝ) :
    Integrable (horizonIncrement active jump rate initial C e V j T) (campbell μ j) :=
  (integrable_campbell_iff μ j _
    (measurable_horizonIncrement active jump rate initial hRate hinit C e V j T).stronglyMeasurable).mpr
      (integrable_horizonIncrement_product active jump rate initial μ hRate hinit C e V j T)

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

theorem ae_integrable_horizonIncrement_intensity (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (j : J) (T : ℝ) :
    ∀ᵐ p ∂law μ J, Integrable
      (fun q => horizonIncrement active jump rate initial C e V j T (p, q))
        (positiveVolume.prod positiveVolume) :=
  (integrable_horizonIncrement_product active jump rate initial μ hRate hinit C e V j T).prod_right_ae

theorem integrable_horizon_intensityIntegral (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (j : J) (T : ℝ) :
    Integrable
      (fun p => ∫ q, horizonIncrement active jump rate initial C e V j T (p, q)
        ∂positiveVolume.prod positiveVolume) (law μ J) :=
  (integrable_horizonIncrement_product active jump rate initial μ hRate hinit C e V j T).integral_prod_left

/-- Almost every actual sample has an integrable signed counting-measure section. -/
theorem ae_integrable_horizonIncrement_counting (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (j : J) (T : ℝ) :
    ∀ᵐ p ∂law μ J, Integrable
      (fun q => horizonIncrement active jump rate initial C e V j T (p, q))
        (MarkedNoise.countingMeasure j p.2) :=
  ae_integrable_counting μ j _
    (measurable_horizonIncrement active jump rate initial hRate hinit C e V j T).stronglyMeasurable
    (integrable_horizonIncrement_product active jump rate initial μ hRate hinit C e V j T)

/-- The actual random counting integral is integrable over initial record and noise. -/
theorem integrable_horizon_countingIntegral (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (j : J) (T : ℝ) :
    Integrable
      (fun p => ∫ q, horizonIncrement active jump rate initial C e V j T (p, q)
        ∂MarkedNoise.countingMeasure j p.2) (law μ J) :=
  integrable_counting_integral μ j _
    (measurable_horizonIncrement active jump rate initial hRate hinit C e V j T).stronglyMeasurable
    (integrable_horizonIncrement_product active jump rate initial μ hRate hinit C e V j T)

/-- Compensation for the actual initialized frozen increment, with every
integrability premise discharged by the finite-region support estimate. -/
theorem compensation_horizonIncrement (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (j : J) (T : ℝ) :
    (∫ p, ∫ q, horizonIncrement active jump rate initial C e V j T (p, q)
      ∂MarkedNoise.countingMeasure j p.2 ∂law μ J) =
    ∫ p, ∫ q, horizonIncrement active jump rate initial C e V j T (p, q)
      ∂positiveVolume.prod positiveVolume ∂law μ J :=
  compensation_integrable μ j _
    (measurable_horizonIncrement active jump rate initial hRate hinit C e V j T).stronglyMeasurable
    (integrable_horizonIncrement_product active jump rate initial μ hRate hinit C e V j T)

end CarryingCapacity.TimeDependentInitialCompensation
