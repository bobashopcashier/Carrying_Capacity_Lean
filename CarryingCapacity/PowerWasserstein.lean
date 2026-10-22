import CarryingCapacity.RealPowerIntegrals
import CarryingCapacity.TransportMetric

/-!
# Ordinary Wasserstein--p for the real power moment scale

The distance is the p-th root of an infimum over genuine probability couplings.
Every coupling cost is integrable, as proved below from the finite power moments.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators

namespace CarryingCapacity.PowerWasserstein
open RealPowerIntegrals

variable {D : ℕ} {p : ℝ} (hp : 1 < p)

/-- The p-th power of the ordinary finite-dimensional ℓp ground distance. -/
def groundCost (p : ℝ) (x y : State D) : ℝ :=
  ∑ i, |(x i : ℝ) - y i| ^ p

theorem groundCost_nonneg (x y : State D) : 0 ≤ groundCost p x y :=
  Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _

theorem groundCost_le_adapted (x y : State D) :
    groundCost p x y ≤ adaptedDistance (MomentScale.realPower p hp.le) x y := by
  exact Finset.sum_le_sum fun i _ =>
    RealPowerMoment.abs_sub_rpow_le p hp.le (Nat.cast_nonneg (x i)) (Nat.cast_nonneg (y i))

theorem integrable_prod_count {Ω : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [SFinite μ]
    (f : Ω × Fin D → ℝ) (hf : ∀ i, Integrable (fun x => f (x, i)) μ) :
    Integrable f (μ.prod Measure.count) := by
  apply (integrable_prod_iff' (measurable_of_countable f).aestronglyMeasurable).mpr
  exact ⟨ae_of_all _ hf, integrable_count_iff.mpr (hasSum_fintype _).summable⟩

theorem integral_prod_count {Ω : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [SFinite μ]
    (f : Ω × Fin D → ℝ) (hf : Integrable f (μ.prod Measure.count)) :
    (∫ z, f z ∂μ.prod Measure.count) = ∫ x, ∑ i, f (x, i) ∂μ := by
  rw [integral_prod _ hf]
  simp only [integral_count]

variable {μ ν : MomentLaw (MomentScale.realPower p hp.le) D}

/-- The actual plan times counting measure on the coordinates. -/
def coordinateMeasure (c : Coupling μ ν) : Measure ((State D × State D) × Fin D) :=
  c.measure.prod Measure.count

def firstCoordinate (z : (State D × State D) × Fin D) : ℝ := z.1.1 z.2
def secondCoordinate (z : (State D × State D) × Fin D) : ℝ := z.1.2 z.2
def displacement (z : (State D × State D) × Fin D) : ℝ :=
  |firstCoordinate z - secondCoordinate z|

theorem integrable_first_power (c : Coupling μ ν) :
    Integrable (fun z => firstCoordinate z ^ p) (coordinateMeasure hp c) := by
  apply integrable_prod_count
  intro i
  apply c.integrable_first.mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [] with x
  dsimp only [firstCoordinate, secondCoordinate]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact Finset.single_le_sum (fun j _ => Real.rpow_nonneg (Nat.cast_nonneg (x.1 j)) p)
    (Finset.mem_univ i)

theorem integrable_second_power (c : Coupling μ ν) :
    Integrable (fun z => secondCoordinate z ^ p) (coordinateMeasure hp c) := by
  apply integrable_prod_count
  intro i
  apply c.integrable_second.mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [] with x
  dsimp only [firstCoordinate, secondCoordinate]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  exact Finset.single_le_sum (fun j _ => Real.rpow_nonneg (Nat.cast_nonneg (x.2 j)) p)
    (Finset.mem_univ i)

theorem integrable_groundCost (c : Coupling μ ν) :
    Integrable (fun z => groundCost p z.1 z.2) c.measure := by
  apply c.integrable_distance.mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (groundCost_nonneg _ _)]
  exact groundCost_le_adapted hp _ _

theorem integrable_displacement_power (c : Coupling μ ν) :
    Integrable (fun z => displacement z ^ p) (coordinateMeasure hp c) := by
  apply integrable_prod_count
  intro i
  apply (integrable_groundCost hp c).mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [] with x
  dsimp only [displacement, firstCoordinate, secondCoordinate]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Finset.single_le_sum (fun j _ => Real.rpow_nonneg (abs_nonneg ((x.1 j : ℝ) - x.2 j)) p)
    (Finset.mem_univ i)

/-- Integral of the p-th power ground cost under a genuine coupling. -/
def planCost (c : Coupling μ ν) : ℝ := ∫ z, groundCost p z.1 z.2 ∂c.measure

theorem planCost_nonneg (c : Coupling μ ν) : 0 ≤ planCost hp c :=
  integral_nonneg fun _ => groundCost_nonneg _ _

theorem integral_first_power (c : Coupling μ ν) :
    (∫ z, firstCoordinate z ^ p ∂coordinateMeasure hp c) = moment μ := by
  rw [coordinateMeasure, integral_prod_count _ _ (integrable_first_power hp c)]
  exact c.integral_first

theorem integral_second_power (c : Coupling μ ν) :
    (∫ z, secondCoordinate z ^ p ∂coordinateMeasure hp c) = moment ν := by
  rw [coordinateMeasure, integral_prod_count _ _ (integrable_second_power hp c)]
  exact c.integral_second

theorem integral_displacement_power (c : Coupling μ ν) :
    (∫ z, displacement z ^ p ∂coordinateMeasure hp c) = planCost hp c := by
  rw [coordinateMeasure, integral_prod_count _ _ (integrable_displacement_power hp c)]
  rfl

theorem planCost_le_cost (c : Coupling μ ν) : planCost hp c ≤ c.cost :=
  integral_mono (integrable_groundCost hp c) c.integrable_distance (fun _ => groundCost_le_adapted hp _ _)

theorem cost_le_planCost_root (c : Coupling μ ν) :
    c.cost ≤ p * (moment μ ^ ((p - 1) / p) + moment ν ^ ((p - 1) / p)) *
      planCost hp c ^ (1 / p) := by
  have hfirst := integrable_first_power hp c
  have hsecond := integrable_second_power hp c
  have hd := integrable_displacement_power hp c
  have hfi := integrable_rpow_mul hp (measurable_of_countable firstCoordinate).aestronglyMeasurable
    (measurable_of_countable displacement).aestronglyMeasurable
    (fun z => Nat.cast_nonneg (z.1.1 z.2)) (fun _ => abs_nonneg _) hfirst hd
  have hsi := integrable_rpow_mul hp (measurable_of_countable secondCoordinate).aestronglyMeasurable
    (measurable_of_countable displacement).aestronglyMeasurable
    (fun z => Nat.cast_nonneg (z.1.2 z.2)) (fun _ => abs_nonneg _) hsecond hd
  have hdi : Integrable (fun z => |firstCoordinate z ^ p - secondCoordinate z ^ p|)
      (coordinateMeasure hp c) := (hfirst.sub hsecond).abs
  have hleft : (∫ z, |firstCoordinate z ^ p - secondCoordinate z ^ p|
      ∂coordinateMeasure hp c) = c.cost := by
    rw [coordinateMeasure, integral_prod_count _ _ hdi]
    rfl
  have hupper := integral_mono hdi ((hfi.add hsi).const_mul p)
    (fun z => by
      simpa only [firstCoordinate, secondCoordinate, displacement, Pi.add_apply, mul_add, add_mul, mul_assoc] using RealPowerMoment.rpow_abs_sub_le p hp.le
        (Nat.cast_nonneg (z.1.1 z.2)) (Nat.cast_nonneg (z.1.2 z.2)))
  simp only [Pi.add_apply] at hupper
  rw [hleft, integral_const_mul, integral_add hfi hsi] at hupper
  have hf := integral_rpow_mul_le hp (measurable_of_countable firstCoordinate).aestronglyMeasurable
    (measurable_of_countable displacement).aestronglyMeasurable
    (fun z => Nat.cast_nonneg (z.1.1 z.2)) (fun _ => abs_nonneg _) hfirst hd
  have hs := integral_rpow_mul_le hp (measurable_of_countable secondCoordinate).aestronglyMeasurable
    (measurable_of_countable displacement).aestronglyMeasurable
    (fun z => Nat.cast_nonneg (z.1.2 z.2)) (fun _ => abs_nonneg _) hsecond hd
  rw [integral_first_power hp c, integral_displacement_power hp c] at hf
  rw [integral_second_power hp c, integral_displacement_power hp c] at hs
  calc
    c.cost ≤ p * ((∫ z, firstCoordinate z ^ (p - 1) * displacement z ∂coordinateMeasure hp c) +
        ∫ z, secondCoordinate z ^ (p - 1) * displacement z ∂coordinateMeasure hp c) := hupper
    _ ≤ p * (moment μ ^ ((p - 1) / p) * planCost hp c ^ (1 / p) +
        moment ν ^ ((p - 1) / p) * planCost hp c ^ (1 / p)) :=
      mul_le_mul_of_nonneg_left (add_le_add hf hs) (lt_trans zero_lt_one hp).le
    _ = _ := by ring


/-- The infimum of genuine p-th-power coupling costs. -/
def costInf (μ ν : MomentLaw (MomentScale.realPower p hp.le) D) : ℝ :=
  sInf (Set.range (fun c : Coupling μ ν => planCost hp c))

theorem costs_bddBelow (μ ν : MomentLaw (MomentScale.realPower p hp.le) D) :
    BddBelow (Set.range (fun c : Coupling μ ν => planCost hp c)) :=
  ⟨0, by rintro _ ⟨c, rfl⟩; exact planCost_nonneg hp c⟩

theorem costInf_nonneg (μ ν : MomentLaw (MomentScale.realPower p hp.le) D) :
    0 ≤ costInf hp μ ν := by
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨c, rfl⟩
  exact planCost_nonneg hp c

/-- Ordinary Wasserstein--p distance for the ℓp ground metric. -/
def distance (μ ν : MomentLaw (MomentScale.realPower p hp.le) D) : ℝ :=
  costInf hp μ ν ^ (1 / p)

theorem distance_nonneg (μ ν : MomentLaw (MomentScale.realPower p hp.le) D) :
    0 ≤ distance hp μ ν := Real.rpow_nonneg (costInf_nonneg hp μ ν) _

theorem distance_rpow (μ ν : MomentLaw (MomentScale.realPower p hp.le) D) :
    distance hp μ ν ^ p = costInf hp μ ν := by
  change (costInf hp μ ν ^ (1 / p)) ^ p = costInf hp μ ν
  rw [one_div, Real.rpow_inv_rpow (costInf_nonneg hp μ ν) (ne_of_gt (lt_trans zero_lt_one hp))]

/-- Taking the p-th root commutes with the infimum over all actual plans. -/
theorem distance_eq_inf_roots (μ ν : MomentLaw (MomentScale.realPower p hp.le) D) :
    distance hp μ ν = sInf (Set.range (fun c : Coupling μ ν => planCost hp c ^ (1 / p))) := by
  have h := MonotoneOn.map_csInf_of_continuousWithinAt
    (f := fun r : ℝ => r ^ (1 / p))
    (A := Set.range (fun c : Coupling μ ν => planCost hp c))
    (Real.continuous_rpow_const (by positivity : 0 ≤ 1 / p)).continuousAt.continuousWithinAt
    (by
      rintro a ⟨c, rfl⟩ b ⟨d, rfl⟩ hcd
      exact Real.rpow_le_rpow (planCost_nonneg hp c) hcd (by positivity))
    (Set.range_nonempty _) (costs_bddBelow hp μ ν)
  simpa only [distance, costInf, ← Set.range_comp, Function.comp_def] using h

theorem distance_le_plan (c : Coupling μ ν) : distance hp μ ν ≤ planCost hp c ^ (1 / p) :=
  Real.rpow_le_rpow (costInf_nonneg hp μ ν)
    (csInf_le (costs_bddBelow hp μ ν) (Set.mem_range_self c)) (by positivity)

/-- The first inequality in Remark 2.1, for every real p greater than one. -/
theorem distance_rpow_le_wasserstein (μ ν : MomentLaw (MomentScale.realPower p hp.le) D) :
    distance hp μ ν ^ p ≤ wasserstein μ ν := by
  rw [distance_rpow]
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨c, rfl⟩
  exact (csInf_le (costs_bddBelow hp μ ν) (Set.mem_range_self c)).trans (planCost_le_cost hp c)

/-- The exact second inequality in Remark 2.1. -/
theorem wasserstein_le_distance (μ ν : MomentLaw (MomentScale.realPower p hp.le) D) :
    wasserstein μ ν ≤
      p * (moment μ ^ ((p - 1) / p) + moment ν ^ ((p - 1) / p)) * distance hp μ ν := by
  let A := p * (moment μ ^ ((p - 1) / p) + moment ν ^ ((p - 1) / p))
  have hA : 0 ≤ A := mul_nonneg (lt_trans zero_lt_one hp).le
    (add_nonneg (Real.rpow_nonneg (moment_nonneg μ) _) (Real.rpow_nonneg (moment_nonneg ν) _))
  have hroot : BddBelow (Set.range (fun c : Coupling μ ν => planCost hp c ^ (1 / p))) :=
    ⟨0, by rintro _ ⟨c, rfl⟩; exact Real.rpow_nonneg (planCost_nonneg hp c) _⟩
  have heq := Monotone.map_csInf_of_continuousAt
    (f := fun r : ℝ => A * r) (continuous_const.mul continuous_id).continuousAt
    (fun _ _ h => mul_le_mul_of_nonneg_left h hA) (Set.range_nonempty _) hroot
  change wasserstein μ ν ≤ A * distance hp μ ν
  dsimp only at heq
  rw [distance_eq_inf_roots, heq]
  apply le_csInf (Set.range_nonempty _ |>.image _)
  rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
  exact (wasserstein_le_cost c).trans (cost_le_planCost_root hp c)

@[simp] theorem distance_self (μ : MomentLaw (MomentScale.realPower p hp.le) D) :
    distance hp μ μ = 0 := by
  apply le_antisymm _ (distance_nonneg hp μ μ)
  have h := distance_le_plan hp (Coupling.diagonal μ)
  have heq : planCost hp (Coupling.diagonal μ) = 0 := by
    apply le_antisymm _ (planCost_nonneg hp _)
    simpa using planCost_le_cost hp (Coupling.diagonal μ)
  rw [heq, Real.zero_rpow (ne_of_gt (one_div_pos.mpr (lt_trans zero_lt_one hp)))] at h
  exact h

theorem distance_eq_zero_iff (μ ν : MomentLaw (MomentScale.realPower p hp.le) D) :
    distance hp μ ν = 0 ↔ μ = ν := by
  constructor
  · intro h
    apply (wasserstein_eq_zero_iff μ ν).mp
    apply le_antisymm _ (wasserstein_nonneg μ ν)
    simpa [h] using wasserstein_le_distance hp μ ν
  · rintro rfl
    exact distance_self hp μ

end CarryingCapacity.PowerWasserstein
