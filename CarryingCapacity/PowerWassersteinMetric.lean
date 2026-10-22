import CarryingCapacity.PowerWasserstein

/-! # The genuine real-p transport metric

The triangle inequality is derived from the existing actual gluing measure and
Minkowski's inequality on that measure times coordinate counting measure.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators

namespace CarryingCapacity.PowerWasserstein
open RealPowerIntegrals

variable {D : ℕ} {p : ℝ} (hp : 1 < p)

include hp in
theorem coordinate_memLp {Ω : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] (M : Measure Ω) [SFinite M]
    (X Y : Ω → State D) (h : Integrable (fun z => groundCost p (X z) (Y z)) M) :
    MemLp (fun z : Ω × Fin D => (X z.1 z.2 : ℝ) - Y z.1 z.2)
      (ENNReal.ofReal p) (M.prod Measure.count) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  apply (integrable_norm_rpow_iff (measurable_of_countable _).aestronglyMeasurable
    (by positivity : ENNReal.ofReal p ≠ 0) ENNReal.ofReal_ne_top).mp
  simp only [ENNReal.toReal_ofReal (lt_trans zero_lt_one hp).le, Real.norm_eq_abs]
  apply integrable_prod_count
  intro i
  apply h.mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Finset.single_le_sum (fun j _ => Real.rpow_nonneg (abs_nonneg ((X z j : ℝ) - Y z j)) p)
    (Finset.mem_univ i)

include hp in
theorem coordinate_lpSize {Ω : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] (M : Measure Ω) [SFinite M]
    (X Y : Ω → State D) (h : Integrable (fun z => groundCost p (X z) (Y z)) M) :
    lpSize p (M.prod Measure.count) (fun z : Ω × Fin D => (X z.1 z.2 : ℝ) - Y z.1 z.2) =
      (∫ z, groundCost p (X z) (Y z) ∂M) ^ (1 / p) := by
  unfold lpSize
  congr 1
  apply integral_prod_count
  have hi := (coordinate_memLp hp M X Y h).integrable_norm_rpow
    (by positivity : ENNReal.ofReal p ≠ 0) ENNReal.ofReal_ne_top
  simpa only [ENNReal.toReal_ofReal (lt_trans zero_lt_one hp).le, Real.norm_eq_abs] using hi

variable {μ ν η : MomentLaw (MomentScale.realPower p hp.le) D}

theorem planRoot_glue_le (c : Coupling μ ν) (d : Coupling ν η) :
    planCost hp (c.glue d) ^ (1 / p) ≤ planCost hp c ^ (1 / p) + planCost hp d ^ (1 / p) := by
  let M := c.glueMeasure d
  letI : IsProbabilityMeasure M := ⟨by
    have h := congrArg (fun m : Measure (State D × State D) => m Set.univ) (c.glueMeasure_first d)
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ, measure_univ] using h⟩
  let X : (State D × State D) × State D → State D := fun z => z.1.1
  let Y : (State D × State D) × State D → State D := fun z => z.1.2
  let Z : (State D × State D) × State D → State D := Prod.snd
  have hXY : Integrable (fun z => groundCost p (X z) (Y z)) M := by
    have h : Integrable (fun z : State D × State D => groundCost p z.1 z.2)
        (Measure.map Prod.fst M) := by
      rw [show Measure.map Prod.fst M = c.measure from c.glueMeasure_first d]
      exact integrable_groundCost hp c
    exact h.comp_measurable measurable_fst
  have hYZ : Integrable (fun z => groundCost p (Y z) (Z z)) M := by
    have h : Integrable (fun z : State D × State D => groundCost p z.1 z.2)
        (Measure.map (fun z => (Y z, Z z)) M) := by
      rw [show Measure.map (fun z => (Y z, Z z)) M = d.measure from c.glueMeasure_last d]
      exact integrable_groundCost hp d
    exact h.comp_measurable (measurable_of_countable _)
  have hXZ : Integrable (fun z => groundCost p (X z) (Z z)) M :=
    (integrable_groundCost hp (c.glue d)).comp_measurable (measurable_of_countable _)
  have heqXY : (∫ z, groundCost p (X z) (Y z) ∂M) = planCost hp c := by
    rw [← integral_map_of_stronglyMeasurable measurable_fst
      (measurable_of_countable (fun z : State D × State D => groundCost p z.1 z.2)).stronglyMeasurable,
      show Measure.map Prod.fst M = c.measure from c.glueMeasure_first d]
    rfl
  have heqYZ : (∫ z, groundCost p (Y z) (Z z) ∂M) = planCost hp d := by
    rw [← integral_map_of_stronglyMeasurable (measurable_of_countable (fun z => (Y z, Z z)))
      (measurable_of_countable (fun z : State D × State D => groundCost p z.1 z.2)).stronglyMeasurable,
      show Measure.map (fun z => (Y z, Z z)) M = d.measure from c.glueMeasure_last d]
    rfl
  have heqXZ : (∫ z, groundCost p (X z) (Z z) ∂M) = planCost hp (c.glue d) := by
    exact (integral_map_of_stronglyMeasurable (measurable_of_countable (fun z => (X z, Z z)))
      (measurable_of_countable (fun z : State D × State D => groundCost p z.1 z.2)).stronglyMeasurable).symm
  have h := lpSize_add_le hp.le (coordinate_memLp hp M X Y hXY) (coordinate_memLp hp M Y Z hYZ)
  have heq : ((fun z : ((State D × State D) × State D) × Fin D => (X z.1 z.2 : ℝ) - Y z.1 z.2) +
      (fun z => (Y z.1 z.2 : ℝ) - Z z.1 z.2)) =
      (fun z => (X z.1 z.2 : ℝ) - Z z.1 z.2) := by
    funext z
    simp only [Pi.add_apply]
    ring
  rw [heq, coordinate_lpSize hp M X Z hXZ, coordinate_lpSize hp M X Y hXY,
    coordinate_lpSize hp M Y Z hYZ, heqXY, heqYZ, heqXZ] at h
  exact h

/-- Minkowski and genuine gluing give the transport triangle inequality. -/
theorem distance_triangle (μ ν η : MomentLaw (MomentScale.realPower p hp.le) D) :
    distance hp μ η ≤ distance hp μ ν + distance hp ν η := by
  have hcost (c : Coupling μ ν) (d : Coupling ν η) :
      distance hp μ η ≤ planCost hp c ^ (1 / p) + planCost hp d ^ (1 / p) :=
    (distance_le_plan hp (c.glue d)).trans (planRoot_glue_le hp c d)
  have hfirst : distance hp μ η - distance hp ν η ≤ distance hp μ ν := by
    rw [distance_eq_inf_roots hp μ ν]
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨c, rfl⟩
    have hsecond : distance hp μ η - planCost hp c ^ (1 / p) ≤ distance hp ν η := by
      rw [distance_eq_inf_roots hp ν η]
      apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨d, rfl⟩
      linarith [hcost c d]
    linarith
  linarith

theorem planCost_swap (c : Coupling μ ν) : planCost hp c.swap = planCost hp c := by
  unfold planCost Coupling.swap
  rw [integral_map_of_stronglyMeasurable measurable_swap (measurable_of_countable _).stronglyMeasurable]
  simp only [Prod.swap, groundCost, abs_sub_comm]

theorem distance_symm (μ ν : MomentLaw (MomentScale.realPower p hp.le) D) :
    distance hp μ ν = distance hp ν μ := by
  suffices h : ∀ (α β : MomentLaw (MomentScale.realPower p hp.le) D),
      distance hp α β ≤ distance hp β α from le_antisymm (h μ ν) (h ν μ)
  intro α β
  rw [distance_eq_inf_roots hp β α]
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨c, rfl⟩
  simpa only [planCost_swap] using distance_le_plan hp c.swap

/-- A separate metric structure on the same actual finite-p-moment laws.
It is not installed globally over the adapted transport metric. -/
def metricSpace : MetricSpace (MomentLaw (MomentScale.realPower p hp.le) D) where
  dist := distance hp
  dist_self := distance_self hp
  dist_comm := distance_symm hp
  dist_triangle := distance_triangle hp
  eq_of_dist_eq_zero := fun h => (distance_eq_zero_iff hp _ _).mp h

end CarryingCapacity.PowerWasserstein
