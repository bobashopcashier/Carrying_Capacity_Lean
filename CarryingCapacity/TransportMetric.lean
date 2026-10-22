import CarryingCapacity.Transport

/-!
# The adapted transport metric

Gluing here uses mathlib's construction of regular conditional probability
kernels. No existence of a coupling or triangle inequality is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CarryingCapacity
variable {D : ℕ} {κ : MomentScale}

namespace Coupling
variable {μ ν η : MomentLaw κ D}

/-- The joint law of `(X,Y,Z)` obtained by drawing `(X,Y)` from the first plan
and then drawing `Z` from the second plan's conditional distribution given `Y`. -/
def glueMeasure (c : Coupling μ ν) (d : Coupling ν η) :
    Measure ((State D × State D) × State D) :=
  c.measure ⊗ₘ d.measure.condKernel.comap Prod.snd measurable_snd

@[simp] theorem glueMeasure_first (c : Coupling μ ν) (d : Coupling ν η) :
    Measure.map Prod.fst (c.glueMeasure d) = c.measure := by
  exact Measure.fst_compProd _ _

@[simp] theorem glueMeasure_last (c : Coupling μ ν) (d : Coupling ν η) :
    Measure.map (fun p : (State D × State D) × State D => (p.1.2, p.2))
      (c.glueMeasure d) = d.measure := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  haveI : IsFiniteMeasure ν.measure := inferInstance
  haveI : SigmaFinite ν.measure := inferInstance
  have hd : ν.measure ⊗ₘ d.measure.condKernel = d.measure := by
    have h := d.measure.disintegrate d.measure.condKernel
    change (Measure.map Prod.fst d.measure) ⊗ₘ d.measure.condKernel = d.measure at h
    rwa [d.first_marginal] at h
  rw [← hd]
  ext s hs
  rw [Measure.map_apply (measurable_of_countable _) hs,
    glueMeasure, Measure.compProd_apply ((measurable_of_countable _) hs),
    Measure.compProd_apply hs, ← c.second_marginal,
    lintegral_map (measurable_of_countable _) measurable_snd]
  rfl

/-- Gluing two plans yields a plan between their outside marginals. -/
def glue (c : Coupling μ ν) (d : Coupling ν η) : Coupling μ η where
  measure := Measure.map (fun p : (State D × State D) × State D => (p.1.1, p.2))
    (c.glueMeasure d)
  first_marginal := by
    rw [Measure.map_map measurable_fst (measurable_of_countable _)]
    have h := c.glueMeasure_first d
    have hh := congrArg (Measure.map Prod.fst) h
    rw [Measure.map_map measurable_fst measurable_fst] at hh
    exact hh.trans c.first_marginal
  second_marginal := by
    rw [Measure.map_map measurable_snd (measurable_of_countable _)]
    have h := c.glueMeasure_last d
    have hh := congrArg (Measure.map Prod.snd) h
    rw [Measure.map_map measurable_snd (measurable_of_countable _)] at hh
    exact hh.trans d.second_marginal

theorem cost_glue_le (c : Coupling μ ν) (d : Coupling ν η) :
    (c.glue d).cost ≤ c.cost + d.cost := by
  have hi₁ : Integrable (fun p : (State D × State D) × State D =>
      adaptedDistance κ p.1.1 p.1.2) (c.glueMeasure d) := by
    have h : Integrable (fun p : State D × State D => adaptedDistance κ p.1 p.2)
        (Measure.map Prod.fst (c.glueMeasure d)) := by
      rw [glueMeasure_first]
      exact c.integrable_distance
    exact h.comp_measurable measurable_fst
  have hi₂ : Integrable (fun p : (State D × State D) × State D =>
      adaptedDistance κ p.1.2 p.2) (c.glueMeasure d) := by
    have h : Integrable (fun p : State D × State D => adaptedDistance κ p.1 p.2)
        (Measure.map (fun p : (State D × State D) × State D => (p.1.2,p.2))
          (c.glueMeasure d)) := by
      rw [glueMeasure_last]
      exact d.integrable_distance
    exact h.comp_measurable (measurable_of_countable _)
  have hi₃ : Integrable (fun p : (State D × State D) × State D =>
      adaptedDistance κ p.1.1 p.2) (c.glueMeasure d) :=
    (c.glue d).integrable_distance.comp_measurable (measurable_of_countable _)
  change (∫ p : State D × State D, adaptedDistance κ p.1 p.2
    ∂Measure.map (fun p : (State D × State D) × State D => (p.1.1,p.2))
      (c.glueMeasure d)) ≤ _
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable _)
    (measurable_of_countable _).stronglyMeasurable]
  calc
    _ ≤ ∫ p, (adaptedDistance κ p.1.1 p.1.2 + adaptedDistance κ p.1.2 p.2)
        ∂c.glueMeasure d := integral_mono hi₃ (hi₁.add hi₂)
          (fun p => adaptedDistance_triangle κ p.1.1 p.1.2 p.2)
    _ = c.cost + d.cost := by
      rw [integral_add hi₁ hi₂]
      congr 1
      · rw [← integral_map_of_stronglyMeasurable measurable_fst
          (measurable_of_countable (fun p : State D × State D => adaptedDistance κ p.1 p.2)).stronglyMeasurable, glueMeasure_first]
        rfl
      · rw [← integral_map_of_stronglyMeasurable
          (measurable_of_countable (fun p : (State D × State D) × State D => (p.1.2,p.2)))
          (measurable_of_countable (fun p : State D × State D => adaptedDistance κ p.1 p.2)).stronglyMeasurable, glueMeasure_last]
        rfl

end Coupling

/-- The triangle inequality follows by genuine gluing and taking the two infima. -/
theorem wasserstein_triangle (μ ν η : MomentLaw κ D) :
    wasserstein μ η ≤ wasserstein μ ν + wasserstein ν η := by
  have hcost (c : Coupling μ ν) (d : Coupling ν η) :
      wasserstein μ η ≤ c.cost + d.cost :=
    (wasserstein_le_cost (c.glue d)).trans (c.cost_glue_le d)
  have hfirst : wasserstein μ η - wasserstein ν η ≤ wasserstein μ ν := by
    apply le_csInf (Set.range_nonempty _)
    rintro r ⟨c, rfl⟩
    have hsecond : wasserstein μ η - c.cost ≤ wasserstein ν η := by
      apply le_csInf (Set.range_nonempty _)
      rintro r ⟨d, rfl⟩
      linarith [hcost c d]
    linarith
  linarith

/-- The normalized scale makes distinct states at least one unit apart. -/
theorem one_le_adaptedDistance_of_ne (x y : State D) (h : x ≠ y) :
    1 ≤ adaptedDistance κ x y := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := not_forall.mp (fun hxy => h (funext hxy))
  have hn : 1 ≤ |(x i : ℝ) - y i| := by
    rcases lt_or_gt_of_ne hi with hlt | hlt
    · have hh : (x i : ℝ) + 1 ≤ y i := by exact_mod_cast Nat.succ_le_of_lt hlt
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hh : (y i : ℝ) + 1 ≤ x i := by exact_mod_cast Nat.succ_le_of_lt hlt
      rw [abs_of_nonneg (by linarith)]
      linarith
  exact hn.trans ((κ.abs_sub_lower_bound _ _).trans (coordinateDistance_le κ x y i))

namespace Coupling

/-- Every integrable one-Lipschitz observable has an expectation difference
bounded by each coupling cost. -/
theorem integral_difference_le_cost {μ ν : MomentLaw κ D} (c : Coupling μ ν)
    (f : State D → ℝ) (hμ : Integrable f μ.measure) (hν : Integrable f ν.measure)
    (hlip : ∀ x y, |f x - f y| ≤ adaptedDistance κ x y) :
    |(∫ x, f x ∂μ.measure) - ∫ x, f x ∂ν.measure| ≤ c.cost := by
  have hi₁ : Integrable (fun p : State D × State D => f p.1) c.measure := by
    have hh : Integrable f (Measure.map Prod.fst c.measure) := by
      rw [c.first_marginal]
      exact hμ
    exact hh.comp_measurable measurable_fst
  have hi₂ : Integrable (fun p : State D × State D => f p.2) c.measure := by
    have hh : Integrable f (Measure.map Prod.snd c.measure) := by
      rw [c.second_marginal]
      exact hν
    exact hh.comp_measurable measurable_snd
  have he₁ : (∫ p : State D × State D, f p.1 ∂c.measure) = ∫ x, f x ∂μ.measure := by
    rw [← integral_map_of_stronglyMeasurable measurable_fst
      (measurable_of_countable f).stronglyMeasurable, c.first_marginal]
  have he₂ : (∫ p : State D × State D, f p.2 ∂c.measure) = ∫ x, f x ∂ν.measure := by
    rw [← integral_map_of_stronglyMeasurable measurable_snd
      (measurable_of_countable f).stronglyMeasurable, c.second_marginal]
  rw [← he₁, ← he₂, ← integral_sub hi₁ hi₂]
  exact abs_integral_le_integral_abs.trans
    (integral_mono (hi₁.sub hi₂).abs c.integrable_distance (fun p => hlip p.1 p.2))

end Coupling

/-- The coupling bound passes to the infimum for any integrable one-Lipschitz
observable. This is the weak dual inequality, not a dual representation theorem. -/
theorem integral_difference_le_wasserstein (μ ν : MomentLaw κ D) (f : State D → ℝ)
    (hμ : Integrable f μ.measure) (hν : Integrable f ν.measure)
    (hlip : ∀ x y, |f x - f y| ≤ adaptedDistance κ x y) :
    |(∫ x, f x ∂μ.measure) - ∫ x, f x ∂ν.measure| ≤ wasserstein μ ν := by
  apply le_csInf (Set.range_nonempty _)
  rintro r ⟨c, rfl⟩
  exact c.integral_difference_le_cost f hμ hν hlip

/-- The adapted transport distance controls each event probability. -/
theorem measureReal_difference_le_wasserstein (μ ν : MomentLaw κ D) (s : Set (State D)) :
    |μ.measure.real s - ν.measure.real s| ≤ wasserstein μ ν := by
  classical
  letI : IsProbabilityMeasure μ.measure := μ.probability
  letI : IsProbabilityMeasure ν.measure := ν.probability
  haveI : IsFiniteMeasure μ.measure := inferInstance
  haveI : IsFiniteMeasure ν.measure := inferInstance
  have hs : MeasurableSet s := s.to_countable.measurableSet
  apply le_csInf (Set.range_nonempty _)
  rintro r ⟨c, rfl⟩
  have hh := c.integral_difference_le_cost (s.indicator (fun _ => (1 : ℝ)))
    ((integrable_const 1).indicator hs) ((integrable_const 1).indicator hs) (by
      intro x y
      by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
      · simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy, adaptedDistance_nonneg]
      · simpa [Set.indicator_of_mem hx, Set.indicator_of_not_mem hy] using
          one_le_adaptedDistance_of_ne (κ := κ) x y (fun h => hy (h ▸ hx))
      · simpa [Set.indicator_of_not_mem hx, Set.indicator_of_mem hy] using
          one_le_adaptedDistance_of_ne (κ := κ) x y (fun h => hx (h.symm ▸ hy))
      · simp [Set.indicator_of_not_mem hx, Set.indicator_of_not_mem hy,
          adaptedDistance_nonneg])
  simpa only [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one] using hh

@[ext] theorem MomentLaw.ext {μ ν : MomentLaw κ D} (h : μ.measure = ν.measure) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

/-- Zero transport distance identifies the laws themselves. -/
theorem wasserstein_eq_zero_iff (μ ν : MomentLaw κ D) : wasserstein μ ν = 0 ↔ μ = ν := by
  constructor
  · intro h
    apply MomentLaw.ext
    letI : IsProbabilityMeasure μ.measure := μ.probability
    letI : IsProbabilityMeasure ν.measure := ν.probability
    haveI : IsFiniteMeasure μ.measure := inferInstance
    haveI : IsFiniteMeasure ν.measure := inferInstance
    haveI : SigmaFinite μ.measure := inferInstance
    haveI : SigmaFinite ν.measure := inferInstance
    apply ext_iff_measureReal_singleton.mpr
    intro x
    have hh := measureReal_difference_le_wasserstein μ ν {x}
    rw [h] at hh
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))
  · rintro rfl
    exact wasserstein_self μ

/-- The genuine adapted Wasserstein distance gives the finite-moment laws a
metric-space structure. Completeness requires a separate proof. -/
instance momentLawMetricSpace : MetricSpace (MomentLaw κ D) where
  dist := wasserstein
  dist_self := wasserstein_self
  dist_comm := wasserstein_symm
  dist_triangle := wasserstein_triangle
  eq_of_dist_eq_zero := fun h => (wasserstein_eq_zero_iff _ _).mp h

@[simp] theorem momentLaw_dist (μ ν : MomentLaw κ D) : dist μ ν = wasserstein μ ν := rfl

/-- The generalized moment is a one-Lipschitz map on the actual metric space. -/
theorem moment_lipschitz : LipschitzWith 1 (fun μ : MomentLaw κ D => moment μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro μ ν
  simpa only [Real.dist_eq, momentLaw_dist, NNReal.coe_one, one_mul] using
    moment_difference_le_wasserstein μ ν

/-- Event probabilities are also one-Lipschitz for the normalized distance. -/
theorem event_probability_lipschitz (s : Set (State D)) :
    LipschitzWith 1 (fun μ : MomentLaw κ D => μ.measure.real s) := by
  apply LipschitzWith.of_dist_le_mul
  intro μ ν
  simpa only [Real.dist_eq, momentLaw_dist, NNReal.coe_one, one_mul] using
    measureReal_difference_le_wasserstein μ ν s

end CarryingCapacity
