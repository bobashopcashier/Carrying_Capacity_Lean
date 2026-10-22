import CarryingCapacity.Framework

/-!
# Linear-distance geometry of the actual admissible jumps

A common admissible jump preserves the l1 distance exactly. Every individual
boundary-aware jump has length at most two, including mutations. The resulting
positive-increment coupling bound applies to any genuine rate family satisfying
its invalid-jump convention.
-/

noncomputable section
open scoped BigOperators

namespace CarryingCapacity.LinearJumpGeometry
variable {D : ℕ}

/-- The real coordinate displacement of the nominal jump direction. -/
def displacement (h : Jump D) (k : Fin D) : ℝ := match h with
  | .inl (.inl i) => if k = i then 1 else 0
  | .inl (.inr i) => if k = i then -1 else 0
  | .inr p => (if k = p.1.2 then 1 else 0) - (if k = p.1.1 then 1 else 0)

theorem advance_coordinate (h : Jump D) (x : State D) (hx : Jump.Admissible h x)
    (k : Fin D) : (Jump.advance h x k : ℝ) = (x k : ℝ) + displacement h k := by
  rcases h with (i | i) | ⟨⟨i, j⟩, hij⟩
  · by_cases hk : k = i
    · subst k
      simp [Jump.advance, displacement]
    · simp [Jump.advance, displacement, Function.update_of_ne hk, hk]
  · change 0 < x i at hx
    have hcast : ((x i - 1 : ℕ) : ℝ) = (x i : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ x i)]
      simp
    by_cases hk : k = i
    · subst k
      simp [Jump.advance, hx, displacement, hcast]
      ring
    · simp [Jump.advance, hx, displacement, Function.update_of_ne hk, hk]
  · change 0 < x i at hx
    have hcast : ((x i - 1 : ℕ) : ℝ) = (x i : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ x i)]
      simp
    by_cases hkj : k = j
    · subst k
      simp [Jump.advance, hx, displacement, hij.symm]
    · by_cases hki : k = i
      · subst k
        simp [Jump.advance, hx, displacement, hij, hcast]
        ring
      · simp [Jump.advance, hx, displacement, Function.update_of_ne hkj,
          Function.update_of_ne hki, hkj, hki]

/-- Shared jumps retain the whole common-rate contribution correctly: their
positive increment is exactly zero whenever both rates can be nonzero. -/
theorem common_distance (h : Jump D) (x y : State D)
    (hx : Jump.Admissible h x) (hy : Jump.Admissible h y) :
    adaptedDistance MomentScale.linear (Jump.advance h x) (Jump.advance h y) =
      adaptedDistance MomentScale.linear x y := by
  simp only [linear_distance]
  apply Finset.sum_congr rfl
  intro k _
  rw [advance_coordinate h x hx, advance_coordinate h y hy]
  congr 1
  ring

theorem displacement_sum_le (h : Jump D) : ∑ k, |displacement h k| ≤ 2 := by
  rcases h with (i | i) | ⟨⟨i, j⟩, hij⟩
  · simp only [displacement]
    simp_rw [apply_ite abs]
    norm_num
  · simp only [displacement]
    simp_rw [apply_ite abs]
    norm_num
  · calc
      (∑ k, |displacement (Sum.inr ⟨(i,j),hij⟩) k|) ≤
          ∑ k : Fin D, (|if k = j then (1 : ℝ) else 0| + |if k = i then (1 : ℝ) else 0|) := by
        apply Finset.sum_le_sum
        intro k _
        simpa only [displacement, sub_zero, zero_sub, abs_neg] using
          abs_sub_le (if k = j then (1 : ℝ) else 0) 0 (if k = i then (1 : ℝ) else 0)
      _ = 2 := by
        simp_rw [apply_ite abs]
        norm_num [Finset.sum_add_distrib]

/-- Invalid jumps are identities; all other actual jumps have l1 length at most two. -/
theorem step_distance_le (h : Jump D) (x : State D) :
    adaptedDistance MomentScale.linear (Jump.advance h x) x ≤ 2 := by
  by_cases hx : Jump.Admissible h x
  · calc
      adaptedDistance MomentScale.linear (Jump.advance h x) x = ∑ k, |displacement h k| := by
        simp only [linear_distance]
        apply Finset.sum_congr rfl
        intro k _
        rw [advance_coordinate h x hx]
        simp
      _ ≤ 2 := displacement_sum_le h
  · rw [Jump.advance_of_invalid h x hx, adaptedDistance_self]
    norm_num

variable {Law : Type*} (q : Rates D Law)

theorem common_positive_zero (h : Jump D) (x y : State D) (μ ν : Law) :
    min (q.rate h x μ) (q.rate h y ν) *
      max (adaptedDistance MomentScale.linear (Jump.advance h x) (Jump.advance h y) -
        adaptedDistance MomentScale.linear x y) 0 = 0 := by
  by_cases hx : Jump.Admissible h x
  · by_cases hy : Jump.Admissible h y
    · rw [common_distance h x y hx hy, sub_self, max_self, mul_zero]
    · rw [q.invalid_zero h y ν hy, min_eq_right (q.nonnegative h x μ), zero_mul]
  · rw [q.invalid_zero h x μ hx, min_eq_left (q.nonnegative h y ν), zero_mul]

/-- Every unmatched positive distance increase is at most two. -/
theorem left_positive_le (h : Jump D) (x y : State D) :
    max (adaptedDistance MomentScale.linear (Jump.advance h x) y -
      adaptedDistance MomentScale.linear x y) 0 ≤ 2 := by
  apply max_le _ (by norm_num)
  have ht := adaptedDistance_triangle MomentScale.linear (Jump.advance h x) x y
  have hs := step_distance_le h x
  linarith

theorem right_positive_le (h : Jump D) (x y : State D) :
    max (adaptedDistance MomentScale.linear x (Jump.advance h y) -
      adaptedDistance MomentScale.linear x y) 0 ≤ 2 := by
  rw [adaptedDistance_symm MomentScale.linear x (Jump.advance h y),
    adaptedDistance_symm MomentScale.linear x y]
  exact left_positive_le h y x

/-- The real positive-increment coupling bound, including the common term. -/
theorem couplingActivity_le (q : Rates D (MomentLaw MomentScale.linear D))
    (x y : State D) (μ ν : MomentLaw MomentScale.linear D) :
    couplingActivity MomentScale.linear q x y μ ν ≤
      2 * ∑ h, |q.rate h x μ - q.rate h y ν| := by
  rw [couplingActivity, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  dsimp only
  rw [common_positive_zero q h x y μ ν, zero_add]
  have h₁ := mul_le_mul_of_nonneg_left (left_positive_le h x y)
    (le_max_right (q.rate h x μ - q.rate h y ν) 0)
  have h₂ := mul_le_mul_of_nonneg_left (right_positive_le h x y)
    (le_max_right (q.rate h y ν - q.rate h x μ) 0)
  have he : max (q.rate h x μ - q.rate h y ν) 0 + max (q.rate h y ν - q.rate h x μ) 0 =
      |q.rate h x μ - q.rate h y ν| := by
    by_cases hh : q.rate h x μ ≤ q.rate h y ν
    · rw [max_eq_right (sub_nonpos.mpr hh), max_eq_left (sub_nonneg.mpr hh),
        abs_of_nonpos (sub_nonpos.mpr hh)]
      ring
    · have hh' := le_of_not_ge hh
      rw [max_eq_left (sub_nonneg.mpr hh'), max_eq_right (sub_nonpos.mpr hh'),
        abs_of_nonneg (sub_nonneg.mpr hh')]
      ring
  nlinarith

/-- Weighted activity is bounded by twice the actual total jump rate. -/
theorem weightedActivity_le (q : Rates D (MomentLaw MomentScale.linear D))
    (x : State D) (μ : MomentLaw MomentScale.linear D) :
    weightedActivity MomentScale.linear q x μ ≤ 2 * q.totalRate x μ := by
  rw [weightedActivity, Rates.totalRate, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  have hh := mul_le_mul_of_nonneg_left (step_distance_le h x) (q.nonnegative h x μ)
  nlinarith

end CarryingCapacity.LinearJumpGeometry
