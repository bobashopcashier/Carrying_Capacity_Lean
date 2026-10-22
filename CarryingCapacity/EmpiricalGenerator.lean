import CarryingCapacity.Symmetrization
import Mathlib.Probability.Kernel.Basic

/-!
# The empirical state space and symmetrization kernel

The countable empirical state space consists of actual measures represented
by configurations of size `N`. The symmetrization kernel is independent of the
chosen representative. The labelled generator descends to this state space
and intertwines with the kernel. These generator identities do not on their
own assert the existence or Markov property of a stochastic process.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical

namespace CarryingCapacity

/-- Actual empirical measures, with a witness that a finite configuration
represents the measure. The discrete measurable structure is used below. -/
structure EmpiricalState (α : Type*) [MeasurableSpace α] (N : ℕ) where
  measure : Measure α
  represented : ∃ z : Fin N → α, empiricalMeasure z = measure

namespace EmpiricalState

variable {α H : Type*} [MeasurableSpace α] {N : ℕ}

@[ext] theorem ext {μ ν : EmpiricalState α N} (h : μ.measure = ν.measure) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

def ofConfig (z : Fin N → α) : EmpiricalState α N :=
  ⟨empiricalMeasure z, ⟨z, rfl⟩⟩

def representative (μ : EmpiricalState α N) : Fin N → α := μ.represented.choose

@[simp] theorem representative_measure (μ : EmpiricalState α N) :
    empiricalMeasure μ.representative = μ.measure := μ.represented.choose_spec

@[simp] theorem ofConfig_representative (μ : EmpiricalState α N) :
    ofConfig μ.representative = μ := ext μ.representative_measure

instance [Countable α] : Countable (EmpiricalState α N) :=
  Function.Injective.countable (f := representative) fun μ ν h => by
    apply ext
    rw [← representative_measure μ, ← representative_measure ν, h]

instance : MeasurableSpace (EmpiricalState α N) := ⊤

instance : MeasurableSingletonClass (EmpiricalState α N) := ⟨fun _ => trivial⟩

theorem measurable_ofConfig [Countable α] [MeasurableSingletonClass α] :
    Measurable (ofConfig : (Fin N → α) → EmpiricalState α N) := measurable_of_countable _

@[simp] theorem ofConfig_relabel (e : Equiv.Perm (Fin N)) (z : Fin N → α) :
    ofConfig (Symmetrization.relabel e z) = ofConfig z :=
  ext (empiricalMeasure_relabel z e)

def probability (hN : 0 < N) (μ : EmpiricalState α N) : ProbabilityMeasure α :=
  ⟨μ.measure, by rw [← μ.representative_measure]; exact empiricalMeasure_probability hN _⟩

@[simp] theorem probability_ofConfig (hN : 0 < N) (z : Fin N → α) :
    (ofConfig z).probability hN = Symmetrization.empiricalProbability hN z := rfl

variable [Countable α] [MeasurableSingletonClass α]

/-- The original paper's symmetrization kernel, defined by a uniformly
random permutation of any representative configuration. -/
def symmetrizationKernel : Kernel (EmpiricalState α N) (Fin N → α) :=
  Kernel.ofFunOfCountable fun μ => Symmetrization.symmetrizedMeasure μ.representative

instance : IsMarkovKernel (symmetrizationKernel (α := α) (N := N)) where
  isProbabilityMeasure _ := Symmetrization.symmetrizedMeasure_probability _

theorem symmetrizationKernel_ofConfig (hN : 0 < N) (z : Fin N → α) :
    symmetrizationKernel (ofConfig z) = Symmetrization.symmetrizedMeasure z := by
  apply Symmetrization.symmetrizedMeasure_eq_of_empirical_eq hN
  exact representative_measure (ofConfig z)

omit [MeasurableSingletonClass α] in
theorem symmetrizationKernel_exchangeable (μ : EmpiricalState α N)
    (e : Equiv.Perm (Fin N)) :
    Measure.map (Symmetrization.relabel e) (symmetrizationKernel μ) =
      symmetrizationKernel μ := Symmetrization.map_relabel_symmetrizedMeasure e _

theorem ae_ofConfig (μ : EmpiricalState α N) :
    ∀ᵐ z ∂symmetrizationKernel μ, ofConfig z = μ := by
  filter_upwards [Symmetrization.ae_empirical_eq μ.representative] with z hz
  apply ext
  exact hz.trans μ.representative_measure

/-- Symmetrizing preserves the given empirical state with probability one. -/
theorem map_ofConfig_symmetrizationKernel (μ : EmpiricalState α N) :
    Measure.map ofConfig (symmetrizationKernel μ) = Measure.dirac μ := by
  rw [Measure.map_congr (ae_ofConfig μ), Measure.map_const]
  simp

/-- Integration against the symmetrization kernel. -/
def average (F : (Fin N → α) → ℝ) (μ : EmpiricalState α N) : ℝ :=
  ∫ z, F z ∂symmetrizationKernel μ

theorem average_ofConfig (hN : 0 < N) (F : (Fin N → α) → ℝ) (z : Fin N → α) :
    average F (ofConfig z) = Symmetrization.symmetrize F z := by
  rw [average, symmetrizationKernel_ofConfig hN, Symmetrization.integral_symmetrizedMeasure]

theorem average_lift (F : EmpiricalState α N → ℝ) (μ : EmpiricalState α N) :
    average (fun z => F (ofConfig z)) μ = F μ := by
  unfold average
  calc
    _ = ∫ _z, F μ ∂symmetrizationKernel μ :=
      integral_congr_ae ((ae_ofConfig μ).mono fun z hz => congrArg F hz)
    _ = F μ := by simp

variable [Fintype H]

/-- The empirical generator, initially evaluated at a representative. Its
independence from that representative is proved by `generator_ofConfig`. -/
def generator (hN : 0 < N) (transition : H → α → α)
    (rate : H → α → ProbabilityMeasure α → ℝ)
    (F : EmpiricalState α N → ℝ) (μ : EmpiricalState α N) : ℝ :=
  FiniteGenerator.systemGenerator transition rate (Symmetrization.empiricalProbability hN)
    (fun z => F (ofConfig z)) μ.representative

omit [Countable α] in
theorem generator_ofConfig (hN : 0 < N) (transition : H → α → α)
    (rate : H → α → ProbabilityMeasure α → ℝ)
    (F : EmpiricalState α N → ℝ) (z : Fin N → α) :
    generator hN transition rate F (ofConfig z) =
      FiniteGenerator.systemGenerator transition rate (Symmetrization.empiricalProbability hN)
        (fun w => F (ofConfig w)) z := by
  obtain ⟨e, he⟩ := (Symmetrization.empiricalMeasure_eq_iff_relabel hN
    (ofConfig z).representative z).mp (representative_measure (ofConfig z))
  unfold generator
  rw [← he, Symmetrization.generator_relabel transition rate
    (Symmetrization.empiricalProbability hN) (Symmetrization.empiricalProbability_relabel hN)]
  simp only [ofConfig_relabel]

/-- The exact original-paper symmetrization intertwining identity
`B(α f) = α(A f)`, for the genuine kernel and empirical generator. -/
theorem generator_average (hN : 0 < N) (transition : H → α → α)
    (rate : H → α → ProbabilityMeasure α → ℝ)
    (F : (Fin N → α) → ℝ) (μ : EmpiricalState α N) :
    generator hN transition rate (average F) μ =
      average (FiniteGenerator.systemGenerator transition rate
        (Symmetrization.empiricalProbability hN) F) μ := by
  conv_rhs => rw [← ofConfig_representative μ, average_ofConfig hN]
  unfold generator
  simp only [average_ofConfig hN]
  exact Symmetrization.original_generator_symmetrize hN transition rate F μ.representative

end EmpiricalState
end CarryingCapacity
