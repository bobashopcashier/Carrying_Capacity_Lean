import CarryingCapacity.RandomEnvironmentCompensation

/-!
# Scalar rate tables remove any extra Polish-space assumption on environments

A countable table of real rates is a Polish space even when no Polish instance
has been installed for the original environment space. Statewise continuous
rates send an arbitrary adapted càdlàg environment to an adapted càdlàg table.
Clipping the table evaluation below at zero gives a globally nonnegative rate
on the auxiliary space and agrees exactly with the original nonnegative rates.
The genuine predictable compensation theorem therefore applies without adding
any topological assumption to the manuscript's environment class.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal BigOperators

namespace CarryingCapacity.RateTableCompensation
open RandomEnvironmentCompensation PredictableStepApproximation MarkedIntensity
  IndependentIncrementCompensation

abbrev Table (J E : Type*) := J × E → ℝ

def table {J E M : Type*} (q : J → E → M → ℝ) (u : M) : Table J E :=
  fun p => q p.1 p.2 u

def evaluation {J E : Type*} (j : J) (x : E) (a : Table J E) : ℝ :=
  max 0 (a (j,x))

theorem continuous_evaluation {J E : Type*} (j : J) (x : E) :
    Continuous (evaluation j x) :=
  continuous_const.max (continuous_apply (j,x))

theorem evaluation_nonnegative {J E : Type*} (j : J) (x : E) (a : Table J E) :
    0 ≤ evaluation j x a := le_max_left _ _

theorem evaluation_table {J E M : Type*} (q : J → E → M → ℝ)
    (hq : ∀ j x u, 0 ≤ q j x u) (j : J) (x : E) (u : M) :
    evaluation j x (table q u) = q j x u := max_eq_right (hq j x u)

theorem continuous_table {J E M : Type*} [TopologicalSpace M]
    (q : J → E → M → ℝ) (hq : ∀ j x, Continuous (q j x)) :
    Continuous (table q) := continuous_pi (fun p => hq p.1 p.2)

theorem cadlag_comp {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : A → B) (hf : Continuous f) (X : ℝ → A) (hX : CadlagNonnegative X) :
    CadlagNonnegative (fun t => f (X t)) := by
  constructor
  · exact fun t ht => hf.continuousAt.comp_continuousWithinAt (hX.1 t ht)
  · intro t ht
    obtain ⟨x,hx⟩ := hX.2 t ht
    exact ⟨f x,hf.continuousAt.tendsto.comp hx⟩

variable {Ω E M J : Type*} [mΩ : MeasurableSpace Ω]
  [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
  [Countable E] [MeasurableSingletonClass E] [DiscreteTopology E]
  [Countable J] [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  (F : Filtration ℝ mΩ) (jump : J → E → E) (q : J → E → M → ℝ)
  (X Y : ℝ → Ω → E) (U W : ℝ → Ω → M) (e : E)

/-- The actual predictable field, implemented through the full scalar-rate
encoding rather than a new regularity assumption on the environment space. -/
def stoppedField (τ : Ω → ℝ≥0∞) (ρ : E → E → ℝ) (j : J) (T : ℝ) :=
  RandomEnvironmentCompensation.stoppedField jump evaluation X Y
    (fun s ω => table q (U s ω)) (fun s ω => table q (W s ω)) e (fun _ => 0) τ ρ j T

variable (hq : ∀ j x, Continuous (q j x))
  (hX : ∀ s, 0 ≤ s → Measurable[F s] (X s))
  (hY : ∀ s, 0 ≤ s → Measurable[F s] (Y s))
  (hU : ∀ s, 0 ≤ s → Measurable[F s] (U s))
  (hW : ∀ s, 0 ≤ s → Measurable[F s] (W s))

include hq hU in
omit jump X Y W e hX hY hW [TopologicalSpace E] [PolishSpace E]
  [MeasurableSpace E] [BorelSpace E] [Countable E] [MeasurableSingletonClass E]
  [DiscreteTopology E] [Countable J] in
theorem measurable_table_process (s : ℝ) (hs : 0 ≤ s) :
    Measurable[F s] (fun ω => table q (U s ω)) := by
  letI : MeasurableSpace Ω := F s
  exact measurable_pi_lambda _ (fun p => (hq p.1 p.2).measurable.comp (hU s hs))

include hq hX hY hU hW in
omit [DiscreteTopology E] in
theorem measurable_stoppedField (τ : Ω → ℝ≥0∞)
    (hτ : ∀ s : ℝ, 0 ≤ s → MeasurableSet[F s] {ω | τ ω ≤ ENNReal.ofReal s})
    (ρ : E → E → ℝ) (j : J) (T : ℝ) :
    Measurable[PredictableSets.predictable F]
      (stoppedField jump q X Y U W e τ ρ j T) :=
  RandomEnvironmentCompensation.measurable_stoppedField F jump evaluation X Y
    (fun s ω => table q (U s ω)) (fun s ω => table q (W s ω)) e (fun _ => 0)
    continuous_evaluation hX hY
    (measurable_table_process F q U hq hU) (measurable_table_process F q W hq hW)
    τ hτ ρ j T

include hq hX hY hU hW in
/-- Full arbitrary-environment compensation with no Polish-space premise on
`M`. The right side contains the original current rates, not auxiliary tables. -/
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
    (∫⁻ ω, ∫⁻ z, ENNReal.ofReal (stoppedField jump q X Y U W e τ ρ j T (ω,z))
      ∂K ω ∂P) =
      ∫⁻ ω, ∫⁻ t in Ioc 0 T, if ENNReal.ofReal t ≤ τ ω then
        ENNReal.ofReal (currentActivity jump q X Y U W ρ j ω t) else 0
        ∂positiveVolume ∂P := by
  have hu := hcU.mono (fun ω h => cadlag_comp (table q) (continuous_table q hq) _ h)
  have hw := hcW.mono (fun ω h => cadlag_comp (table q) (continuous_table q hq) _ h)
  have h := RandomEnvironmentCompensation.expected_stoppedField_eq_currentActivity
    F jump evaluation X Y (fun s ω => table q (U s ω)) (fun s ω => table q (W s ω))
    e (fun _ => 0) continuous_evaluation hX hY
    (measurable_table_process F q U hq hU) (measurable_table_process F q W hq hW)
    P K hmean hind τ hτ evaluation_nonnegative hcX hcY hu hw ρ j T
  simpa only [stoppedField, currentActivity, evaluation_table q hnonneg] using h

end CarryingCapacity.RateTableCompensation
