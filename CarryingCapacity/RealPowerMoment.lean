import CarryingCapacity.MomentGeometry

/-!
# Real power moment scales

The scalar estimates used in the manuscript's comparison with ordinary
Wasserstein--p distance. The exponent is real, and need not be an integer.
-/

noncomputable section
open Set

namespace CarryingCapacity.RealPowerMoment

/-- The mean-value estimate on a nonnegative interval, for any real exponent
at least one. -/
theorem rpow_sub_le (p : ℝ) (hp : 1 ≤ p) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    b ^ p - a ^ p ≤ p * b ^ (p - 1) * (b - a) := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hderiv : ∀ x ∈ Icc a b,
      HasDerivWithinAt (fun x : ℝ => x ^ p) (p * x ^ (p - 1)) (Icc a b) x :=
    fun _ _ => (Real.hasDerivAt_rpow_const (Or.inr hp)).hasDerivWithinAt
  have hbound : ∀ x ∈ Ico a b, ‖p * x ^ (p - 1)‖ ≤ p * b ^ (p - 1) := by
    intro x hx
    have hx0 := ha.trans hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp0 (Real.rpow_nonneg hx0 _))]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hx0 hx.2.le (sub_nonneg.mpr hp)) hp0
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound b ⟨hab, le_rfl⟩
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using h)

/-- Symmetric secant estimate used before applying Hölder's inequality. -/
theorem rpow_abs_sub_le (p : ℝ) (hp : 1 ≤ p) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a ^ p - b ^ p| ≤ p * (a ^ (p - 1) + b ^ (p - 1)) * |a - b| := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have ordered : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b →
      |a ^ p - b ^ p| ≤ p * (a ^ (p - 1) + b ^ (p - 1)) * |a - b| := by
    intro a b ha hab
    have hpow := Real.rpow_le_rpow ha hab hp0
    rw [abs_of_nonpos (sub_nonpos.mpr hpow), abs_of_nonpos (sub_nonpos.mpr hab)]
    have h := rpow_sub_le p hp ha hab
    have hmore : 0 ≤ p * a ^ (p - 1) * (b - a) :=
      mul_nonneg (mul_nonneg hp0 (Real.rpow_nonneg ha _)) (sub_nonneg.mpr hab)
    nlinarith
  rcases le_total a b with hab | hba
  · exact ordered ha hab
  · simpa only [abs_sub_comm, add_comm] using ordered hb hba

/-- The power of the displacement is bounded by the power-coordinate
displacement. -/
theorem abs_sub_rpow_le (p : ℝ) (hp : 1 ≤ p) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a - b| ^ p ≤ |a ^ p - b ^ p| := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have ordered : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b →
      |a - b| ^ p ≤ |a ^ p - b ^ p| := by
    intro a b ha hab
    have hpow := Real.rpow_le_rpow ha hab hp0
    rw [abs_of_nonpos (sub_nonpos.mpr hab), abs_of_nonpos (sub_nonpos.mpr hpow)]
    have h := Real.add_rpow_le_rpow_add ha (sub_nonneg.mpr hab) hp
    rw [add_sub_cancel] at h
    simpa only [neg_sub] using (show (b - a) ^ p ≤ b ^ p - a ^ p by linarith)
  rcases le_total a b with hab | hba
  · exact ordered ha hab
  · simpa only [abs_sub_comm] using ordered hb hba

end CarryingCapacity.RealPowerMoment

namespace CarryingCapacity.MomentScale

/-- The real power scale in Remark 2.1, including the linear endpoint. -/
def realPower (p : ℝ) (hp : 1 ≤ p) : MomentScale where
  value n := (n : ℝ) ^ p
  at_zero := by simp [ne_of_gt (lt_of_lt_of_le zero_lt_one hp)]
  step n := by
    have h := Real.add_rpow_le_rpow_add (Nat.cast_nonneg n) (show (0 : ℝ) ≤ 1 by norm_num) hp
    simp only [Real.one_rpow] at h
    simp only [Nat.cast_add, Nat.cast_one]
    linarith

@[simp] theorem realPower_value (p : ℝ) (hp : 1 ≤ p) (n : ℕ) :
    (realPower p hp).value n = (n : ℝ) ^ p := rfl

end CarryingCapacity.MomentScale
