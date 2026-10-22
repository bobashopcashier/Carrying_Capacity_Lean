import CarryingCapacity.PowerWassersteinMetric

/-! # Equality of the power-adapted and ordinary Wasserstein topologies

No uniform moment bound is an extra hypothesis: ordinary Wasserstein--p
convergence itself controls the p-th moment, by Minkowski on genuine plans.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace CarryingCapacity.PowerWasserstein
open RealPowerIntegrals

variable {D : ℕ} {p : ℝ} (hp : 1 < p)
variable {μ ν : MomentLaw (MomentScale.realPower p hp.le) D}

theorem moment_root_le_plan (c : Coupling μ ν) :
    moment μ ^ (1 / p) ≤ planCost hp c ^ (1 / p) + moment ν ^ (1 / p) := by
  have hp0 := lt_trans zero_lt_one hp
  have hf := memLp_of_integrable_rpow hp0
    (measurable_of_countable firstCoordinate).aestronglyMeasurable
    (fun z => Nat.cast_nonneg (z.1.1 z.2)) (integrable_first_power hp c)
  have hg := memLp_of_integrable_rpow hp0
    (measurable_of_countable secondCoordinate).aestronglyMeasurable
    (fun z => Nat.cast_nonneg (z.1.2 z.2)) (integrable_second_power hp c)
  have hd : MemLp (fun z => firstCoordinate z - secondCoordinate z)
      (ENNReal.ofReal p) (coordinateMeasure hp c) := hf.sub hg
  have h := lpSize_add_le hp.le hd hg
  have heq : (fun z => firstCoordinate z - secondCoordinate z) + secondCoordinate =
      (firstCoordinate : (State D × State D) × Fin D → ℝ) := by
    funext z
    simp only [Pi.add_apply, sub_add_cancel]
  rw [heq] at h
  have hfirst : lpSize p (coordinateMeasure hp c) firstCoordinate = moment μ ^ (1 / p) := by
    unfold lpSize
    simp only [firstCoordinate, Nat.abs_cast]
    rw [show (∫ z, (z.1.1 z.2 : ℝ) ^ p ∂coordinateMeasure hp c) = moment μ from
      integral_first_power hp c]
  have hsecond : lpSize p (coordinateMeasure hp c) secondCoordinate = moment ν ^ (1 / p) := by
    unfold lpSize
    simp only [secondCoordinate, Nat.abs_cast]
    rw [show (∫ z, (z.1.2 z.2 : ℝ) ^ p ∂coordinateMeasure hp c) = moment ν from
      integral_second_power hp c]
  have hdiff : lpSize p (coordinateMeasure hp c) (fun z => firstCoordinate z - secondCoordinate z) =
      planCost hp c ^ (1 / p) := by
    unfold lpSize
    rw [show (∫ z, |firstCoordinate z - secondCoordinate z| ^ p ∂coordinateMeasure hp c) =
      planCost hp c from integral_displacement_power hp c]
  rwa [hfirst, hsecond, hdiff] at h

theorem moment_root_le_distance (μ ν : MomentLaw (MomentScale.realPower p hp.le) D) :
    moment μ ^ (1 / p) ≤ distance hp μ ν + moment ν ^ (1 / p) := by
  have h : moment μ ^ (1 / p) - moment ν ^ (1 / p) ≤ distance hp μ ν := by
    rw [distance_eq_inf_roots]
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨c, rfl⟩
    linarith [moment_root_le_plan hp c]
  linarith

theorem moment_root_difference_le (μ ν : MomentLaw (MomentScale.realPower p hp.le) D) :
    |moment μ ^ (1 / p) - moment ν ^ (1 / p)| ≤ distance hp μ ν := by
  rw [abs_le]
  have h₁ := moment_root_le_distance hp μ ν
  have h₂ := moment_root_le_distance hp ν μ
  rw [distance_symm hp ν μ] at h₂
  constructor <;> linarith

/-- Ordinary Wasserstein--p convergence supplies moment convergence itself. -/
theorem moment_tendsto_of_distance {I : Type*} {l : Filter I}
    (μ : I → MomentLaw (MomentScale.realPower p hp.le) D)
    (ν : MomentLaw (MomentScale.realPower p hp.le) D)
    (h : Tendsto (fun i => distance hp (μ i) ν) l (𝓝 0)) :
    Tendsto (fun i => moment (μ i)) l (𝓝 (moment ν)) := by
  have hr : Tendsto (fun i => moment (μ i) ^ (1 / p)) l (𝓝 (moment ν ^ (1 / p))) := by
    rw [Metric.tendsto_nhds] at h ⊢
    intro ε hε
    filter_upwards [h ε hε] with i hi
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (distance_nonneg hp _ _)] at hi
    rw [Real.dist_eq]
    exact (moment_root_difference_le hp _ _).trans_lt hi
  have hpow := (Real.continuous_rpow_const (lt_trans zero_lt_one hp).le).tendsto
    (moment ν ^ (1 / p)) |>.comp hr
  simpa only [Function.comp_def, one_div, Real.rpow_inv_rpow (moment_nonneg _) (ne_of_gt (lt_trans zero_lt_one hp))] using hpow

/-- The two distances have exactly the same convergence for every filter. -/
theorem tendsto_distance_zero_iff {I : Type*} {l : Filter I}
    (μ : I → MomentLaw (MomentScale.realPower p hp.le) D)
    (ν : MomentLaw (MomentScale.realPower p hp.le) D) :
    Tendsto (fun i => distance hp (μ i) ν) l (𝓝 0) ↔
      Tendsto (fun i => wasserstein (μ i) ν) l (𝓝 0) := by
  have hp0 := lt_trans zero_lt_one hp
  constructor
  · intro h
    have hm := moment_tendsto_of_distance hp μ ν h
    have hpow := (Real.continuous_rpow_const (div_nonneg (sub_nonneg.mpr hp.le) hp0.le)).tendsto
      (moment ν) |>.comp hm
    have hc := ((hpow.add_const (moment ν ^ ((p - 1) / p))).const_mul p).mul h
    apply squeeze_zero (fun i => wasserstein_nonneg _ _) (fun i => wasserstein_le_distance hp _ _) ?_
    simpa only [Function.comp_def, mul_zero] using hc
  · intro h
    have hr := (Real.continuous_rpow_const (one_div_nonneg.mpr hp0.le)).tendsto (0 : ℝ) |>.comp h
    have hupper (i : I) : distance hp (μ i) ν ≤ wasserstein (μ i) ν ^ (1 / p) := by
      rw [one_div, Real.le_rpow_inv_iff_of_pos (distance_nonneg hp _ _) (wasserstein_nonneg _ _) hp0]
      exact distance_rpow_le_wasserstein hp _ _
    exact squeeze_zero (fun i => distance_nonneg hp _ _) hupper
      (by simpa only [Function.comp_def, Real.zero_rpow (ne_of_gt (one_div_pos.mpr hp0))] using hr)

/-- A neighborhood characterization in the existing adapted transport topology. -/
theorem tendsto_nhds_iff {I : Type*} {l : Filter I}
    (μ : I → MomentLaw (MomentScale.realPower p hp.le) D)
    (ν : MomentLaw (MomentScale.realPower p hp.le) D) :
    Tendsto μ l (𝓝 ν) ↔ Tendsto (fun i => distance hp (μ i) ν) l (𝓝 0) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [momentLaw_dist]
  exact (tendsto_distance_zero_iff hp μ ν).symm

/-- The genuine ordinary Wasserstein--p metric and the manuscript's adapted
transport metric induce the same topology on finite-p-moment laws. -/
theorem topology_eq :
    (metricSpace (D := D) hp).toUniformSpace.toTopologicalSpace =
      (momentLawMetricSpace (κ := MomentScale.realPower p hp.le) (D := D)).toUniformSpace.toTopologicalSpace := by
  apply TopologicalSpace.ext_nhds
  intro ν
  let tp := (metricSpace (D := D) hp).toUniformSpace.toTopologicalSpace
  let tk := (momentLawMetricSpace (κ := MomentScale.realPower p hp.le) (D := D)).toUniformSpace.toTopologicalSpace
  change @nhds _ tp ν = @nhds _ tk ν
  have hwp : Tendsto (fun μ => distance hp μ ν) (@nhds _ tp ν) (𝓝 0) := by
    letI := metricSpace (D := D) hp
    exact tendsto_iff_dist_tendsto_zero.mp tendsto_id
  have hk : Tendsto (fun μ => distance hp μ ν) (@nhds _ tk ν) (𝓝 0) :=
    (tendsto_nhds_iff hp id ν).mp tendsto_id
  have hpk : Tendsto id (@nhds _ tp ν) (@nhds _ tk ν) :=
    (tendsto_nhds_iff hp id ν).mpr hwp
  have hkp : Tendsto id (@nhds _ tk ν) (@nhds _ tp ν) := by
    letI := metricSpace (D := D) hp
    exact tendsto_iff_dist_tendsto_zero.mpr hk
  exact le_antisymm hpk hkp

end CarryingCapacity.PowerWasserstein
