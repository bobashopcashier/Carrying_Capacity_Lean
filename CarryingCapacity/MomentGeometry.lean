import Mathlib

/-!
# The moment-adapted geometry

Definitions and elementary geometry from Section 2 of Kenny Xie's manuscript.
Only the values of κ on the nonnegative integers enter the model. The linear
scale recovers the state-space geometry of DeWitt--Evans--Hiesmayr--Hummel.
This file does not assert a stochastic existence or mean-field limit theorem.
-/

noncomputable section
open scoped BigOperators

namespace CarryingCapacity

/-- The exact discrete normalization used in equation (2.1). -/
structure MomentScale where
  value : ℕ → ℝ
  at_zero : value 0 = 0
  step : ∀ n, 1 ≤ value (n + 1) - value n

namespace MomentScale

variable (κ : MomentScale)

theorem increment_lower_bound {n m : ℕ} (h : n ≤ m) :
    (m : ℝ) - n ≤ κ.value m - κ.value n := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m h ih =>
    have hs := κ.step m
    push_cast
    linarith

theorem nat_le_value (n : ℕ) : (n : ℝ) ≤ κ.value n := by
  have h := κ.increment_lower_bound (Nat.zero_le n)
  simpa [κ.at_zero] using h

theorem value_nonneg (n : ℕ) : 0 ≤ κ.value n :=
  le_trans (Nat.cast_nonneg n) (κ.nat_le_value n)

theorem strictMono : StrictMono κ.value := by
  intro n m h
  have hd := κ.increment_lower_bound (Nat.le_of_lt h)
  have hn : (n : ℝ) < m := by exact_mod_cast h
  linarith

theorem injective : Function.Injective κ.value := κ.strictMono.injective

theorem abs_sub_lower_bound (n m : ℕ) :
    |(n : ℝ) - m| ≤ |κ.value n - κ.value m| := by
  rcases le_total n m with h | h
  · have hc : (n : ℝ) ≤ m := by exact_mod_cast h
    have hk := κ.strictMono.monotone h
    rw [abs_of_nonpos (sub_nonpos.mpr hc), abs_of_nonpos (sub_nonpos.mpr hk)]
    have hd := κ.increment_lower_bound h
    linarith
  · have hc : (m : ℝ) ≤ n := by exact_mod_cast h
    have hk := κ.strictMono.monotone h
    rw [abs_of_nonneg (sub_nonneg.mpr hc), abs_of_nonneg (sub_nonneg.mpr hk)]
    exact κ.increment_lower_bound h

/-- The first-moment specialization. -/
def linear : MomentScale where
  value n := n
  at_zero := by norm_num
  step n := by push_cast; linarith

/-- The second-moment specialization used in the scalar application. -/
def quadratic : MomentScale where
  value n := (n : ℝ) ^ 2
  at_zero := by norm_num
  step n := by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) n]

end MomentScale

abbrev State (D : ℕ) := Fin D → ℕ

def populationSize {D : ℕ} (x : State D) : ℝ := ∑ i, (x i : ℝ)

def momentWeight (κ : MomentScale) {D : ℕ} (x : State D) : ℝ :=
  ∑ i, κ.value (x i)

def adaptedDistance (κ : MomentScale) {D : ℕ} (x y : State D) : ℝ :=
  ∑ i, |κ.value (x i) - κ.value (y i)|

variable {D : ℕ} (κ : MomentScale)

theorem momentWeight_nonneg (x : State D) : 0 ≤ momentWeight κ x := by
  exact Finset.sum_nonneg fun i _ => κ.value_nonneg (x i)

theorem size_le_momentWeight (x : State D) : populationSize x ≤ momentWeight κ x := by
  exact Finset.sum_le_sum fun i _ => κ.nat_le_value (x i)

theorem adaptedDistance_nonneg (x y : State D) : 0 ≤ adaptedDistance κ x y := by
  exact Finset.sum_nonneg fun i _ => abs_nonneg _

@[simp] theorem adaptedDistance_self (x : State D) : adaptedDistance κ x x = 0 := by
  simp [adaptedDistance]

theorem adaptedDistance_symm (x y : State D) :
    adaptedDistance κ x y = adaptedDistance κ y x := by
  simp only [adaptedDistance, abs_sub_comm]

theorem adaptedDistance_triangle (x y z : State D) :
    adaptedDistance κ x z ≤ adaptedDistance κ x y + adaptedDistance κ y z := by
  unfold adaptedDistance
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => abs_sub_le _ _ _

theorem coordinateDistance_le (x y : State D) (i : Fin D) :
    |κ.value (x i) - κ.value (y i)| ≤ adaptedDistance κ x y := by
  unfold adaptedDistance
  exact Finset.single_le_sum (fun j _ => abs_nonneg (κ.value (x j) - κ.value (y j)))
    (Finset.mem_univ i)

theorem adaptedDistance_eq_zero_iff (x y : State D) :
    adaptedDistance κ x y = 0 ↔ x = y := by
  constructor
  · intro h
    funext i
    apply κ.injective
    have hi := coordinateDistance_le κ x y i
    rw [h] at hi
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hi (abs_nonneg _)))
  · rintro rfl
    exact adaptedDistance_self κ x

@[simp] theorem adaptedDistance_zero (x : State D) :
    adaptedDistance κ x 0 = momentWeight κ x := by
  simp [adaptedDistance, momentWeight, κ.at_zero, abs_of_nonneg (κ.value_nonneg _)]

theorem momentWeight_difference_le (x y : State D) :
    |momentWeight κ x - momentWeight κ y| ≤ adaptedDistance κ x y := by
  unfold momentWeight adaptedDistance
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

theorem l1_le_adaptedDistance (x y : State D) :
    (∑ i, |(x i : ℝ) - y i|) ≤ adaptedDistance κ x y := by
  exact Finset.sum_le_sum fun i _ => κ.abs_sub_lower_bound _ _

/-- The manuscript's adapted distance is a metric, not merely a pseudometric. -/
def adaptedMetric : MetricSpace (State D) where
  dist := adaptedDistance κ
  dist_self := adaptedDistance_self κ
  dist_comm := adaptedDistance_symm κ
  dist_triangle := adaptedDistance_triangle κ
  eq_of_dist_eq_zero := fun h => (adaptedDistance_eq_zero_iff κ _ _).mp h

@[simp] theorem linear_weight (x : State D) :
    momentWeight MomentScale.linear x = populationSize x := rfl

@[simp] theorem linear_distance (x y : State D) :
    adaptedDistance MomentScale.linear x y = ∑ i, |(x i : ℝ) - y i| := rfl

/-- Finite sublevel sets are the deterministic starting point of freezing. -/
theorem finite_moment_sublevel (R : ℝ) :
    {x : State D | momentWeight κ x ≤ R}.Finite := by
  apply (Set.finite_Iic (fun _ : Fin D => Nat.ceil R)).subset
  intro x hx i
  have hi : (x i : ℝ) ≤ momentWeight κ x := by
    apply (κ.nat_le_value (x i)).trans
    exact Finset.single_le_sum (fun j _ => κ.value_nonneg (x j)) (Finset.mem_univ i)
  have h : (x i : ℝ) ≤ (Nat.ceil R : ℝ) := hi.trans (hx.trans (Nat.le_ceil R))
  exact_mod_cast h

theorem finite_lyapunov_sublevel (Ψ : State D → ℝ)
    (hΨ : ∀ x, momentWeight κ x ≤ Ψ x) (R : ℝ) :
    {x : State D | Ψ x < R}.Finite := by
  apply (finite_moment_sublevel κ R).subset
  intro x hx
  exact (hΨ x).trans (le_of_lt hx)

end CarryingCapacity
