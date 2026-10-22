import CarryingCapacity.LinearMeanGenerator

/-!
# Local Lipschitz control of the closed carrying-capacity vector field

The prescribed mortality Lipschitz assumption gives an explicit finite
Lipschitz bound on every bounded nonnegative box. The bound is derived from
the actual birth, mortality and mutation coefficients, including zero types.
-/

noncomputable section
open Set
open scoped BigOperators NNReal

namespace CarryingCapacity.LinearMeanLipschitz
open LinearCarryingCapacity LinearCarryingCapacityBounds LinearMeanGenerator LinearJumpGeometry
variable {D : ℕ}

/-- A coordinatewise bounded part of the nonnegative orthant. -/
def nonnegativeBox (B : ℝ) : Set (Fin D → ℝ) := {z | ∀ i, 0 ≤ z i ∧ z i ≤ B}

theorem l1_difference_le_sup (z w : Fin D → ℝ) :
    (∑ i, |z i - w i|) ≤ (D : ℝ) * dist z w := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => dist_le_pi_dist z w i)
  simpa only [Real.dist_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] using h

theorem sum_le_of_mem_box {B : ℝ} {z : Fin D → ℝ} (hz : z ∈ nonnegativeBox B) :
    (∑ i, z i) ≤ (D : ℝ) * B := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hz i).2)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h

variable (c : Coefficients D)

theorem perCapita_nonnegative (h : Jump D) {B : ℝ} {z : Fin D → ℝ}
    (hz : z ∈ nonnegativeBox B) : 0 ≤ perCapitaVector c h z := by
  rcases h with (i | i) | p
  · exact c.birth_nonnegative i
  · exact c.mortality_nonnegative i z (fun i => (hz i).1)
  · exact c.mutation_nonnegative p

theorem perCapita_le (h : Jump D) {B : ℝ} (hB : 0 ≤ B) {z : Fin D → ℝ}
    (hz : z ∈ nonnegativeBox B) :
    perCapitaVector c h z ≤ coefficientBound c * (1 + (D : ℝ) * B) := by
  have hC := coefficientBound_nonnegative c
  have hDB : 0 ≤ (D : ℝ) * B := mul_nonneg (Nat.cast_nonneg _) hB
  obtain ⟨hb, hm, hd, hL⟩ := coefficient_bounds c
  rcases h with (i | i) | p
  · exact (hb i).trans (by nlinarith)
  · have hl := c.mortality_lipschitz i z 0 (fun i => (hz i).1) (fun _ => le_rfl)
    simp only [Pi.zero_apply, sub_zero, abs_of_nonneg (hz _).1] at hl
    have he : c.mortality i z ≤ c.mortality i 0 + c.lipschitzConstant * ∑ j, z j := by
      have h := (le_abs_self (c.mortality i z - c.mortality i 0)).trans hl
      linarith
    have hs := sum_le_of_mem_box hz
    have hm := mul_le_mul_of_nonneg_left hs c.lipschitzConstant_nonnegative
    have hLC := mul_le_mul_of_nonneg_right hL hDB
    have h0 := hd i
    change c.mortality i z ≤ _
    nlinarith
  · exact (hm p).trans (by nlinarith)

theorem perCapita_difference_le (h : Jump D) {B : ℝ} {z w : Fin D → ℝ}
    (hz : z ∈ nonnegativeBox B) (hw : w ∈ nonnegativeBox B) :
    |perCapitaVector c h z - perCapitaVector c h w| ≤
      (c.lipschitzConstant * (D : ℝ)) * dist z w := by
  have hL := c.lipschitzConstant_nonnegative
  rcases h with (i | i) | p
  · simp only [perCapitaVector, sub_self, abs_zero]
    positivity
  · exact (c.mortality_lipschitz i z w (fun i => (hz i).1) (fun i => (hw i).1)).trans
      (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left
        (l1_difference_le_sup z w) c.lipschitzConstant_nonnegative))
  · simp only [perCapitaVector, sub_self, abs_zero]
    positivity

theorem displacement_abs_le_one (h : Jump D) (i : Fin D) : |displacement h i| ≤ 1 := by
  rcases h with (j | j) | ⟨⟨j,k⟩,hjk⟩
  · simp only [displacement]
    split_ifs <;> norm_num
  · simp only [displacement]
    split_ifs <;> norm_num
  · simp only [displacement]
    split_ifs <;> norm_num

/-- A per-label polynomial coefficient is Lipschitz on each nonnegative box. -/
theorem perLabel_difference_le (B : ℝ) (hB : 0 ≤ B) (h : Jump D)
    {z w : Fin D → ℝ} (hz : z ∈ nonnegativeBox B) (hw : w ∈ nonnegativeBox B) :
    |perCapitaVector c h z * z (Jump.source h) - perCapitaVector c h w * w (Jump.source h)| ≤
      (coefficientBound c * (1 + (D : ℝ) * B) + c.lipschitzConstant * (D : ℝ) * B) * dist z w := by
  have hC := coefficientBound_nonnegative c
  have hL := c.lipschitzConstant_nonnegative
  have he : perCapitaVector c h z * z (Jump.source h) - perCapitaVector c h w * w (Jump.source h) =
      perCapitaVector c h z * (z (Jump.source h) - w (Jump.source h)) +
        (perCapitaVector c h z - perCapitaVector c h w) * w (Jump.source h) := by ring
  rw [he]
  calc
    _ ≤ perCapitaVector c h z * |z (Jump.source h) - w (Jump.source h)| +
        |perCapitaVector c h z - perCapitaVector c h w| * w (Jump.source h) := by
      simpa only [abs_mul, abs_of_nonneg (perCapita_nonnegative c h hz),
        abs_of_nonneg (hw (Jump.source h)).1] using abs_add_le
          (perCapitaVector c h z * (z (Jump.source h) - w (Jump.source h)))
          ((perCapitaVector c h z - perCapitaVector c h w) * w (Jump.source h))
    _ ≤ (coefficientBound c * (1 + (D : ℝ) * B)) * dist z w +
        ((c.lipschitzConstant * (D : ℝ)) * dist z w) * B :=
      add_le_add
        (mul_le_mul (perCapita_le c h hB hz) (by simpa only [Real.dist_eq] using dist_le_pi_dist z w (Jump.source h))
          (abs_nonneg _) (by positivity))
        (mul_le_mul (perCapita_difference_le c h hz hw) (hw (Jump.source h)).2
          (hw (Jump.source h)).1 (by positivity))
    _ = _ := by ring

/-- The local Lipschitz property needed for ODE uniqueness is a theorem of
the coefficient assumptions, rather than an additional model hypothesis. -/
theorem exists_lipschitzOn_box (B : ℝ) (hB : 0 ≤ B) :
    ∃ K : ℝ≥0, LipschitzOnWith K (vectorField c) (nonnegativeBox B) := by
  let C := coefficientBound c * (1 + (D : ℝ) * B) + c.lipschitzConstant * (D : ℝ) * B
  have hC : 0 ≤ C := by
    dsimp [C]
    have hc := coefficientBound_nonnegative c
    have hL := c.lipschitzConstant_nonnegative
    positivity
  refine ⟨⟨(Fintype.card (Jump D) : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC⟩, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz w hw
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  rw [Real.dist_eq]
  change |(∑ h, perCapitaVector c h z * z (Jump.source h) * displacement h i) -
    (∑ h, perCapitaVector c h w * w (Jump.source h) * displacement h i)| ≤ _
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ h : Jump D, C * dist z w := by
      apply Finset.sum_le_sum
      intro h _
      rw [← sub_mul, abs_mul]
      exact (mul_le_mul (perLabel_difference_le c B hB h hz hw) (displacement_abs_le_one h i)
        (abs_nonneg _) (mul_nonneg hC dist_nonneg)).trans_eq (mul_one _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NNReal.coe_mk, mul_assoc]

end CarryingCapacity.LinearMeanLipschitz
