import CarryingCapacity.Models
import CarryingCapacity.RealPowerMoment

/-!
# Real-power Lyapunov estimates

These are actual real-exponent estimates for the polynomial Lyapunov functions
in Section 7. In particular no integer rounding of the exponent is used.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace CarryingCapacity.RealPowerLyapunov

/-- Higher positive real powers dominate lower powers at integer states. -/
theorem nat_rpow_le (n : ℕ) {p r : ℝ} (hp : 0 < p) (hpr : p ≤ r) :
    (n : ℝ) ^ p ≤ (n : ℝ) ^ r := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [Real.zero_rpow hp.ne', Real.zero_rpow (hp.trans_le hpr).ne']
  · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hpr

/-- An explicit superlinear lower bound, valid for every real state at least one. -/
theorem ratio_lower {p r x : ℝ} (hp : 0 ≤ p) (hx : 1 ≤ x) :
    x ^ (r - p) / 2 ≤ (1 + x ^ r) / (1 + x ^ p) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hpone := Real.one_le_rpow hx hp
  have hnonneg := Real.rpow_nonneg hxpos.le (r - p)
  have hmul : x ^ (r - p) * x ^ p = x ^ r := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by positivity)).mpr
  nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hpone)]

/-- The ratio of higher and lower real-power Lyapunov scales diverges. -/
theorem tendsto_ratio {p r : ℝ} (hp : 0 ≤ p) (hpr : p < r) :
    Tendsto (fun x : ℝ => (1 + x ^ r) / (1 + x ^ p)) atTop atTop := by
  apply tendsto_atTop_mono' atTop (f₁ := fun x : ℝ => x ^ (r - p) / 2) _
    ((tendsto_rpow_atTop (sub_pos.mpr hpr)).atTop_div_const (by norm_num : (0 : ℝ) < 2))
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact ratio_lower hp hx

/-- The one-step derivative growth stays of order `n^r`, including the zero boundary. -/
theorem nat_mul_succ_rpow_le (n : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    (n : ℝ) * ((n : ℝ) + 1) ^ (r - 1) ≤
      (2 : ℝ) ^ (r - 1) * (n : ℝ) ^ r := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [Real.zero_rpow (lt_of_lt_of_le zero_lt_one hr).ne']
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)
    (show (n : ℝ) + 1 ≤ 2 * (n : ℝ) by linarith) (sub_nonneg.mpr hr)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hnpos.le] at hpow
  have hcancel : (n : ℝ) * (n : ℝ) ^ (r - 1) = (n : ℝ) ^ r := by
    rw [Real.rpow_sub_one hnpos.ne']
    field_simp
  calc
    (n : ℝ) * ((n : ℝ) + 1) ^ (r - 1) ≤
        (n : ℝ) * ((2 : ℝ) ^ (r - 1) * (n : ℝ) ^ (r - 1)) :=
      mul_le_mul_of_nonneg_left hpow hnpos.le
    _ = (2 : ℝ) ^ (r - 1) * (n : ℝ) ^ r := by rw [mul_left_comm, hcancel]

/-- A genuine one-step birth estimate for every real exponent at least one. -/
theorem birth_increment_le (n : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    (n : ℝ) * (((n : ℝ) + 1) ^ r - (n : ℝ) ^ r) ≤
      (r * (2 : ℝ) ^ (r - 1)) * (n : ℝ) ^ r := by
  have hsec := RealPowerMoment.rpow_sub_le r hr (Nat.cast_nonneg n)
    (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith)
  have hsec' : ((n : ℝ) + 1) ^ r - (n : ℝ) ^ r ≤
      r * ((n : ℝ) + 1) ^ (r - 1) := by simpa using hsec
  calc
    (n : ℝ) * (((n : ℝ) + 1) ^ r - (n : ℝ) ^ r) ≤
        (n : ℝ) * (r * ((n : ℝ) + 1) ^ (r - 1)) :=
      mul_le_mul_of_nonneg_left hsec' (Nat.cast_nonneg n)
    _ = r * ((n : ℝ) * ((n : ℝ) + 1) ^ (r - 1)) := by ring
    _ ≤ r * ((2 : ℝ) ^ (r - 1) * (n : ℝ) ^ r) :=
      mul_le_mul_of_nonneg_left (nat_mul_succ_rpow_le n hr) (by linarith)
    _ = _ := by ring

/-- Boundary-aware deaths never increase a nonnegative real power. -/
theorem death_increment_nonpositive (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ((n - 1 : ℕ) : ℝ) ^ r - (n : ℝ) ^ r ≤ 0 := by
  apply sub_nonpos.mpr
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le n 1) hr

/-- The actual scalar generator satisfies the real-power Lyapunov drift bound.
The mortality coefficient is arbitrary nonnegative and need not be bounded. -/
theorem generator_realPower_le (birth death : ℝ) (hbirth : 0 ≤ birth)
    (hdeath : 0 ≤ death) (n : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    Models.generator birth death (fun k => 1 + (k : ℝ) ^ r) n ≤
      (birth * (r * (2 : ℝ) ^ (r - 1))) * (1 + (n : ℝ) ^ r) := by
  have hb := mul_le_mul_of_nonneg_left (birth_increment_le n hr) hbirth
  have hd := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg hdeath (Nat.cast_nonneg n))
    (death_increment_nonpositive n (by linarith : 0 ≤ r))
  have hC : 0 ≤ birth * (r * (2 : ℝ) ^ (r - 1)) := by positivity
  simp only [Models.generator, Nat.cast_add, Nat.cast_one]
  nlinarith

end CarryingCapacity.RealPowerLyapunov
