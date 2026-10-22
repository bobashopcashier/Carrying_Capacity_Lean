import CarryingCapacity.CadlagRateRegularity
import CarryingCapacity.IndependentIncrementCompensation
import CarryingCapacity.SynchronousCompensation

/-!
# Arbitrary adapted random environments in synchronous compensation

The states and environments here are arbitrary adapted processes. Predictable
left versions are constructed from strict-past deterministic samples. On their
càdlàg events these versions are the actual left limits. The three-region
synchronous increment is then compensated through any common stopping time,
using only independent future counts and their unweighted intensity.

The final identity uses current states and current environments: scalar
càdlàg observables agree with their left limits almost everywhere in time.
No finite-activity assumption, deterministic-environment restriction, or
expected coupling inequality is an input. The pathwise positive-jump bound
from the separate thinning equations is a subsequent obligation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal BigOperators

namespace CarryingCapacity.RandomEnvironmentCompensation
open PredictableSets PredictableStepApproximation SynchronousPositiveIncrement
  MarkedIntensity IndependentIncrementCompensation

/-- Right continuity on nonnegative times and genuine left limits at positive
ones. This is a path property, with no probabilistic conclusion built in. -/
def CadlagNonnegative {V : Type*} [TopologicalSpace V] (X : ℝ → V) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt X (Ici t) t) ∧
  ∀ t : ℝ, 0 < t → ∃ y : V, Tendsto X (𝓝[<] t) (𝓝 y)

variable {Ω E M J : Type*} [mΩ : MeasurableSpace Ω]
  [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
  [Countable E] [MeasurableSingletonClass E] [DiscreteTopology E]
  [TopologicalSpace M] [PolishSpace M] [MeasurableSpace M] [BorelSpace M]
  (F : Filtration ℝ mΩ) (jump : J → E → E) (q : J → E → M → ℝ)
  (X Y : ℝ → Ω → E) (U W : ℝ → Ω → M) (e : E) (m : M)

/-- Genuine predictable left-state/environment versions give the actual
positive shared-height increment on a finite horizon. -/
def field (ρ : E → E → ℝ) (j : J) (T : ℝ) (p : Ω × (ℝ × ℝ)) : ℝ :=
  if p.2.1 ∈ Ioc 0 T then
    positiveIncrement ρ jump j
      (q j (pastLimit X e p.1 p.2.1) (pastLimit U m p.1 p.2.1))
      (q j (pastLimit Y e p.1 p.2.1) (pastLimit W m p.1 p.2.1))
      (pastLimit X e p.1 p.2.1) (pastLimit Y e p.1 p.2.1) p.2.2
  else 0

/-- The stopped field includes the possible jump at the stopping time. -/
def stoppedField (τ : Ω → ℝ≥0∞) (ρ : E → E → ℝ) (j : J) (T : ℝ) :=
  PredictableStoppingMask.mask τ (field jump q X Y U W e m ρ j T)

def preActivity (ρ : E → E → ℝ) (j : J) (ω : Ω) (t : ℝ) : ℝ :=
  heightActivity ρ jump j
    (q j (pastLimit X e ω t) (pastLimit U m ω t))
    (q j (pastLimit Y e ω t) (pastLimit W m ω t))
    (pastLimit X e ω t) (pastLimit Y e ω t)

def currentActivity (ρ : E → E → ℝ) (j : J) (ω : Ω) (t : ℝ) : ℝ :=
  heightActivity ρ jump j (q j (X t ω) (U t ω)) (q j (Y t ω) (W t ω)) (X t ω) (Y t ω)

variable (hq : ∀ j x, Continuous (q j x))
  (hX : ∀ s, 0 ≤ s → Measurable[F s] (X s))
  (hY : ∀ s, 0 ≤ s → Measurable[F s] (Y s))
  (hU : ∀ s, 0 ≤ s → Measurable[F s] (U s))
  (hW : ∀ s, 0 ≤ s → Measurable[F s] (W s))

omit F X Y U W e m hX hY hU hW jump [TopologicalSpace E] [PolishSpace E]
  [BorelSpace E] [DiscreteTopology E] [PolishSpace M] in
include hq in
/-- Only continuity in the environment is required; the state space is
countable, so no uniform rate bound is hidden in this measurability step. -/
theorem measurable_rate_comp {A : Type*} [MeasurableSpace A]
    (j : J) (x : A → E) (u : A → M) (hx : Measurable x) (hu : Measurable u) :
    Measurable (fun a => q j (x a) (u a)) := by
  have hm : Measurable (fun p : M × E => q j p.2 p.1) :=
    measurable_from_prod_countable (fun z => (hq j z).measurable)
  exact hm.comp (hu.prodMk hx)

include hq hX hY hU hW in
omit [DiscreteTopology E] in
theorem measurable_field (ρ : E → E → ℝ) (j : J) (T : ℝ) :
    Measurable[predictable F] (field jump q X Y U W e m ρ j T) := by
  letI : MeasurableSpace (Ω × (ℝ × ℝ)) := predictable F
  have hx := measurable_pastLimit F X hX e
  have hy := measurable_pastLimit F Y hY e
  have hu := measurable_pastLimit F U hU m
  have hw := measurable_pastLimit F W hW m
  have ha := measurable_rate_comp q hq j _ _ hx hu
  have hb := measurable_rate_comp q hq j _ _ hy hw
  have hm := (measurable_positiveIncrement_comp ρ jump j _ _ _ _ _ ha hb
    (measurable_positiveHeight F) hx hy).indicator
      (measurableSet_predictable_rectangle F 0 T le_rfl univ MeasurableSet.univ
        univ MeasurableSet.univ)
  convert hm using 1
  funext p
  by_cases ht : p.2.1 ∈ Ioc 0 T
  · simp [field, rectangle, ht, positiveHeight, ht.1]
  · simp [field, rectangle, ht]

include hq hX hY hU hW in
omit [DiscreteTopology E] in
theorem measurable_stoppedField (τ : Ω → ℝ≥0∞)
    (hτ : ∀ s : ℝ, 0 ≤ s → MeasurableSet[F s] {ω | τ ω ≤ ENNReal.ofReal s})
    (ρ : E → E → ℝ) (j : J) (T : ℝ) :
    Measurable[predictable F] (stoppedField jump q X Y U W e m τ ρ j T) :=
  PredictableStoppingMask.measurable_mask F τ hτ _
    (measurable_field F jump q X Y U W e m hq hX hY hU hW ρ j T)

omit F jump q Y W m hq hX hY hU hW U mΩ [MeasurableSpace E]
  [BorelSpace E] [Countable E] [MeasurableSingletonClass E] [DiscreteTopology E] in
/-- The predictable left version equals the actual left limit on every
càdlàg sample, simultaneously at all positive times. -/
theorem tendsto_pastLimit (ω : Ω) (hc : CadlagNonnegative (fun t => X t ω))
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 (pastLimit X e ω t)) := by
  obtain ⟨y, hy⟩ := hc.2 t ht
  rwa [pastLimit_eq_of_tendsto X e ω t ht y hy]

omit F jump q Y W m hq hX hY hU hW U mΩ [MeasurableSpace E]
  [BorelSpace E] [MeasurableSingletonClass E] in
theorem ae_pastLimit_eq (ω : Ω) (hc : CadlagNonnegative (fun t => X t ω)) :
    (pastLimit X e ω) =ᵐ[positiveVolume] (fun t => X t ω) :=
  CadlagRateRegularity.ae_left_eq_discrete _ _
    (tendsto_pastLimit X e ω hc) hc.1

omit F jump X Y W e hX hY hU hW mΩ [TopologicalSpace E] [PolishSpace E]
  [MeasurableSpace E] [BorelSpace E] [Countable E] [MeasurableSingletonClass E]
  [DiscreteTopology E] [MeasurableSpace M] [BorelSpace M] in
include hq in
/-- A random environment may have infinitely many jumps. Each continuous
rate observable still agrees with its left version almost everywhere. -/
theorem ae_rate_pastLimit_eq (ω : Ω) (hc : CadlagNonnegative (fun t => U t ω))
    (j : J) (x : E) :
    (fun t => q j x (pastLimit U m ω t)) =ᵐ[positiveVolume] (fun t => q j x (U t ω)) := by
  apply CadlagRateRegularity.ae_continuous_observable_left_eq _ _ _ (hq j x)
  · intro t ht
    obtain ⟨y, hy⟩ := hc.2 t ht
    rwa [pastLimit_eq_of_tendsto U m ω t ht y hy]
  · exact hc.1

omit F hX hY hU hW mΩ [MeasurableSpace E] [BorelSpace E]
  [MeasurableSingletonClass E] [MeasurableSpace M] [BorelSpace M] in
include hq in
theorem ae_preActivity_eq_currentActivity (ω : Ω)
    (hcX : CadlagNonnegative (fun t => X t ω)) (hcY : CadlagNonnegative (fun t => Y t ω))
    (hcU : CadlagNonnegative (fun t => U t ω)) (hcW : CadlagNonnegative (fun t => W t ω))
    (ρ : E → E → ℝ) (j : J) :
    preActivity jump q X Y U W e m ρ j ω =ᵐ[positiveVolume]
      currentActivity jump q X Y U W ρ j ω := by
  have hu := ae_all_iff.mpr (fun x : E => ae_rate_pastLimit_eq q U m hq ω hcU j x)
  have hw := ae_all_iff.mpr (fun x : E => ae_rate_pastLimit_eq q W m hq ω hcW j x)
  filter_upwards [ae_pastLimit_eq X e ω hcX, ae_pastLimit_eq Y e ω hcY, hu, hw]
    with t hx hy hu hw
  simp only [preActivity, currentActivity, hx, hy, hu, hw]

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

include hq hX hY hU hW in
omit [DiscreteTopology E] in
/-- Pointwise height integration retains all three synchronous terms and the
inclusive stopping endpoint. -/
theorem intensity_integral (τ : Ω → ℝ≥0∞)
    (hτ : ∀ s : ℝ, 0 ≤ s → MeasurableSet[F s] {ω | τ ω ≤ ENNReal.ofReal s})
    (hnonneg : ∀ j x u, 0 ≤ q j x u) (ρ : E → E → ℝ) (j : J) (T : ℝ) (ω : Ω) :
    (∫⁻ z, ENNReal.ofReal (stoppedField jump q X Y U W e m τ ρ j T (ω,z))
      ∂positiveVolume.prod positiveVolume) =
      ∫⁻ t in Ioc 0 T, if ENNReal.ofReal t ≤ τ ω then
        ENNReal.ofReal (preActivity jump q X Y U W e m ρ j ω t) else 0
        ∂positiveVolume := by
  have hm := ((measurable_stoppedField F jump q X Y U W e m hq hX hY hU hW
    τ hτ ρ j T).mono (predictable_le F) le_rfl).ennreal_ofReal
  have hs : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal
      (stoppedField jump q X Y U W e m τ ρ j T (ω,z))) :=
    hm.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod _ hs.aemeasurable, ← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ Ioc 0 T
  · by_cases hstop : ENNReal.ofReal t ≤ τ ω
    · simp only [stoppedField, PredictableStoppingMask.mask_apply, ht.1, hstop,
        and_self, if_true, field, ht, Set.indicator_of_mem ht]
      exact lintegral_positiveIncrement ρ jump j _ _ _ _ (hnonneg j _ _) (hnonneg j _ _)
    · simp [stoppedField, PredictableStoppingMask.mask_apply, ht.1, hstop, ht]
  · have he : ∀ u : ℝ, stoppedField jump q X Y U W e m τ ρ j T (ω,(t,u)) = 0 := by
      intro u
      simp [stoppedField, PredictableStoppingMask.mask_apply, field, ht]
    simp [he, ht]

include hq hX hY hU hW in
/-- Exact compensation for random adapted càdlàg environments, stopped at any
common stopping time. The primitive noise hypotheses do not contain a
compensator or a coupling estimate. Both sides may be infinite. -/
theorem expected_stoppedField_eq_currentActivity
    (P : Measure Ω) [IsProbabilityMeasure P] (K : Kernel Ω (ℝ × ℝ)) [IsSFiniteKernel K]
    (hmean : HasIntensity P K) (hind : FutureCountsIndependent F P K)
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ s : ℝ, 0 ≤ s → MeasurableSet[F s] {ω | τ ω ≤ ENNReal.ofReal s})
    (hnonneg : ∀ j x u, 0 ≤ q j x u)
    (hcX : ∀ᵐ ω ∂P, CadlagNonnegative (fun t => X t ω))
    (hcY : ∀ᵐ ω ∂P, CadlagNonnegative (fun t => Y t ω))
    (hcU : ∀ᵐ ω ∂P, CadlagNonnegative (fun t => U t ω))
    (hcW : ∀ᵐ ω ∂P, CadlagNonnegative (fun t => W t ω))
    (ρ : E → E → ℝ) (j : J) (T : ℝ) :
    (∫⁻ ω, ∫⁻ z, ENNReal.ofReal (stoppedField jump q X Y U W e m τ ρ j T (ω,z))
      ∂K ω ∂P) =
      ∫⁻ ω, ∫⁻ t in Ioc 0 T, if ENNReal.ofReal t ≤ τ ω then
        ENNReal.ofReal (currentActivity jump q X Y U W ρ j ω t) else 0
        ∂positiveVolume ∂P := by
  rw [compensation_nonnegative F P K hmean hind _
    (measurable_stoppedField F jump q X Y U W e m hq hX hY hU hW τ hτ ρ j T).ennreal_ofReal]
  simp_rw [intensity_integral F jump q X Y U W e m hq hX hY hU hW τ hτ hnonneg]
  apply lintegral_congr_ae
  filter_upwards [hcX, hcY, hcU, hcW] with ω hx hy hu hw
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae
    (ae_preActivity_eq_currentActivity jump q X Y U W e m hq ω hx hy hu hw ρ j)] with t ht
  simp only [ht]

end CarryingCapacity.RandomEnvironmentCompensation
