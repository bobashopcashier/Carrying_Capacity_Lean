import CarryingCapacity.MomentGeometry

/-!
# Moment control by transport

The probability laws and couplings here are genuine mathlib measures. Finite
moment is an integrability condition, not a convention assigning a value to a
divergent integral. The transport distance is the infimum over all couplings.
This file proves the moment-control inequality from Section 2, but does not
claim completeness of the transport space or a stochastic mean-field theorem.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace CarryingCapacity

/-- Probability measures with a finite κ-moment. -/
structure MomentLaw (κ : MomentScale) (D : ℕ) where
  measure : Measure (State D)
  probability : IsProbabilityMeasure measure
  integrable_weight : Integrable (momentWeight κ) measure

variable {D : ℕ} {κ : MomentScale}

def moment (μ : MomentLaw κ D) : ℝ := ∫ x, momentWeight κ x ∂μ.measure

theorem moment_nonneg (μ : MomentLaw κ D) : 0 ≤ moment μ := by
  exact integral_nonneg fun x => momentWeight_nonneg κ x

/-- A transport plan specified by its two actual marginal measures. -/
structure Coupling (μ ν : MomentLaw κ D) where
  measure : Measure (State D × State D)
  first_marginal : Measure.map Prod.fst measure = μ.measure
  second_marginal : Measure.map Prod.snd measure = ν.measure

namespace Coupling

variable {μ ν : MomentLaw κ D} (c : Coupling μ ν)

instance probability : IsProbabilityMeasure c.measure where
  measure_univ := by
    have h : (Measure.map Prod.fst c.measure) Set.univ = 1 := by
      rw [c.first_marginal]
      exact μ.probability.measure_univ
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,
      Set.preimage_univ] using h

def diagonal (μ : MomentLaw κ D) : Coupling μ μ where
  measure := Measure.map (fun x => (x, x)) μ.measure
  first_marginal := by
    rw [Measure.map_map measurable_fst (measurable_of_countable (fun x : State D => (x,x)))]
    simp [Function.comp_def]
  second_marginal := by
    rw [Measure.map_map measurable_snd (measurable_of_countable (fun x : State D => (x,x)))]
    simp [Function.comp_def]

def swap : Coupling ν μ where
  measure := Measure.map Prod.swap c.measure
  first_marginal := by
    rw [Measure.map_map measurable_fst measurable_swap]
    exact c.second_marginal
  second_marginal := by
    rw [Measure.map_map measurable_snd measurable_swap]
    exact c.first_marginal

def independent (μ ν : MomentLaw κ D) : Coupling μ ν where
  measure := μ.measure.prod ν.measure
  first_marginal := by
    letI : IsProbabilityMeasure μ.measure := μ.probability
    letI : IsProbabilityMeasure ν.measure := ν.probability
    haveI : IsFiniteMeasure ν.measure := inferInstance
    haveI : SigmaFinite ν.measure := inferInstance
    change Measure.map Prod.fst (μ.measure.prod ν.measure) = μ.measure
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  second_marginal := by
    letI : IsProbabilityMeasure μ.measure := μ.probability
    letI : IsProbabilityMeasure ν.measure := ν.probability
    haveI : IsFiniteMeasure ν.measure := inferInstance
    haveI : SigmaFinite ν.measure := inferInstance
    change Measure.map Prod.snd (μ.measure.prod ν.measure) = ν.measure
    rw [Measure.map_snd_prod, measure_univ, one_smul]

instance : Nonempty (Coupling μ ν) := ⟨independent μ ν⟩

theorem integrable_first : Integrable (fun p => momentWeight κ p.1) c.measure := by
  have h : Integrable (momentWeight κ) (Measure.map Prod.fst c.measure) := by
    rw [c.first_marginal]
    exact μ.integrable_weight
  exact h.comp_measurable measurable_fst

theorem integrable_second : Integrable (fun p => momentWeight κ p.2) c.measure := by
  have h : Integrable (momentWeight κ) (Measure.map Prod.snd c.measure) := by
    rw [c.second_marginal]
    exact ν.integrable_weight
  exact h.comp_measurable measurable_snd

theorem integral_first : (∫ p, momentWeight κ p.1 ∂c.measure) = moment μ := by
  rw [← integral_map_of_stronglyMeasurable measurable_fst
    (measurable_of_countable (momentWeight κ)).stronglyMeasurable]
  rw [c.first_marginal]
  rfl

theorem integral_second : (∫ p, momentWeight κ p.2 ∂c.measure) = moment ν := by
  rw [← integral_map_of_stronglyMeasurable measurable_snd
    (measurable_of_countable (momentWeight κ)).stronglyMeasurable]
  rw [c.second_marginal]
  rfl

end Coupling

theorem adaptedDistance_le_weights (x y : State D) :
    adaptedDistance κ x y ≤ momentWeight κ x + momentWeight κ y := by
  unfold adaptedDistance momentWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [abs_le]
  constructor <;> linarith [κ.value_nonneg (x i), κ.value_nonneg (y i)]

namespace Coupling

variable {μ ν : MomentLaw κ D} (c : Coupling μ ν)

theorem integrable_distance :
    Integrable (fun p => adaptedDistance κ p.1 p.2) c.measure := by
  apply (c.integrable_first.add c.integrable_second).mono'
    (measurable_of_countable _).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (adaptedDistance_nonneg κ _ _)]
    exact adaptedDistance_le_weights _ _

def cost : ℝ := ∫ p, adaptedDistance κ p.1 p.2 ∂c.measure

@[simp] theorem cost_diagonal (μ : MomentLaw κ D) : (diagonal μ).cost = 0 := by
  change (∫ p, adaptedDistance κ p.1 p.2 ∂Measure.map (fun x => (x,x)) μ.measure) = 0
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable (fun x : State D => (x,x)))
    (measurable_of_countable _).stronglyMeasurable]
  simp

@[simp] theorem cost_swap : c.swap.cost = c.cost := by
  change (∫ p, adaptedDistance κ p.1 p.2 ∂Measure.map Prod.swap c.measure) = c.cost
  rw [integral_map_of_stronglyMeasurable measurable_swap
    (measurable_of_countable _).stronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall fun p => adaptedDistance_symm κ p.2 p.1)

theorem cost_nonneg : 0 ≤ c.cost :=
  integral_nonneg fun p => adaptedDistance_nonneg κ p.1 p.2

theorem cost_le_moments : c.cost ≤ moment μ + moment ν := by
  calc
    c.cost ≤ ∫ p, (momentWeight κ p.1 + momentWeight κ p.2) ∂c.measure :=
      integral_mono c.integrable_distance (c.integrable_first.add c.integrable_second)
        (fun p => adaptedDistance_le_weights _ _)
    _ = moment μ + moment ν := by
      rw [integral_add c.integrable_first c.integrable_second,
        c.integral_first, c.integral_second]

theorem moment_difference_le_cost : |moment μ - moment ν| ≤ c.cost := by
  rw [← c.integral_first, ← c.integral_second,
    ← integral_sub c.integrable_first c.integrable_second]
  calc
    |∫ p, (momentWeight κ p.1 - momentWeight κ p.2) ∂c.measure| ≤
        ∫ p, |momentWeight κ p.1 - momentWeight κ p.2| ∂c.measure :=
      abs_integral_le_integral_abs
    _ ≤ c.cost := integral_mono (c.integrable_first.sub c.integrable_second).abs
      c.integrable_distance (fun p => momentWeight_difference_le κ _ _)

end Coupling

/-- The real, finite adapted Wasserstein--1 cost of the manuscript. -/
def wasserstein (μ ν : MomentLaw κ D) : ℝ :=
  sInf (Set.range (fun c : Coupling μ ν => c.cost))

theorem couplingCosts_bddBelow (μ ν : MomentLaw κ D) :
    BddBelow (Set.range (fun c : Coupling μ ν => c.cost)) := by
  refine ⟨0, ?_⟩
  rintro r ⟨c, rfl⟩
  exact c.cost_nonneg

theorem wasserstein_nonneg (μ ν : MomentLaw κ D) : 0 ≤ wasserstein μ ν := by
  apply le_csInf (Set.range_nonempty _)
  rintro r ⟨c, rfl⟩
  exact c.cost_nonneg

theorem wasserstein_le_cost {μ ν : MomentLaw κ D} (c : Coupling μ ν) :
    wasserstein μ ν ≤ c.cost := by
  exact csInf_le (couplingCosts_bddBelow μ ν) (Set.mem_range_self c)

@[simp] theorem wasserstein_self (μ : MomentLaw κ D) : wasserstein μ μ = 0 := by
  apply le_antisymm _ (wasserstein_nonneg μ μ)
  simpa using wasserstein_le_cost (Coupling.diagonal μ)

theorem wasserstein_symm (μ ν : MomentLaw κ D) : wasserstein μ ν = wasserstein ν μ := by
  suffices h : ∀ (α β : MomentLaw κ D), wasserstein α β ≤ wasserstein β α from
    le_antisymm (h μ ν) (h ν μ)
  intro α β
  apply le_csInf (Set.range_nonempty _)
  rintro r ⟨c, rfl⟩
  exact (wasserstein_le_cost c.swap).trans_eq c.cost_swap

/-- Equation (2.4): the transport distance controls the generalized moment. -/
theorem moment_difference_le_wasserstein (μ ν : MomentLaw κ D) :
    |moment μ - moment ν| ≤ wasserstein μ ν := by
  apply le_csInf (Set.range_nonempty _)
  rintro r ⟨c, rfl⟩
  exact c.moment_difference_le_cost

theorem wasserstein_le_moments (μ ν : MomentLaw κ D) :
    wasserstein μ ν ≤ moment μ + moment ν :=
  (wasserstein_le_cost (Coupling.independent μ ν)).trans
    (Coupling.independent μ ν).cost_le_moments

/-- The moment-convergence consequence holds for arbitrary filters. The
Wasserstein convergence itself must be supplied by a separate argument. -/
theorem moment_tendsto_of_wasserstein {I : Type*} {l : Filter I}
    (μ : I → MomentLaw κ D) (ν : MomentLaw κ D)
    (h : Filter.Tendsto (fun i => wasserstein (μ i) ν) l (nhds 0)) :
    Filter.Tendsto (fun i => moment (μ i)) l (nhds (moment ν)) := by
  rw [Metric.tendsto_nhds] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with i hi
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (wasserstein_nonneg (μ i) ν)] at hi
  rw [Real.dist_eq]
  exact (moment_difference_le_wasserstein (μ i) ν).trans_lt hi

end CarryingCapacity
