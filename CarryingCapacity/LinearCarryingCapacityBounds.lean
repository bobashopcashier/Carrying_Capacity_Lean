import CarryingCapacity.LinearCarryingCapacity

/-!
# Genuine rate bounds for the untruncated multitype model

Both the total-rate growth and the weighted rate-difference condition are
derived from the actual vector-feedback coefficient assumptions. Constants
are allowed to depend on the fixed number of types, never on the state or law.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace CarryingCapacity.LinearCarryingCapacityBounds
open LinearCarryingCapacity

variable {D : ℕ} (c : Coefficients D)

/-- A single finite nonnegative coefficient bound. -/
def coefficientBound : ℝ :=
  (∑ i, c.birth i) + (∑ p, c.mutation p) +
    (∑ i, c.mortality i 0) + c.lipschitzConstant

theorem coefficientBound_nonnegative : 0 ≤ coefficientBound c := by
  have hb := c.birth_nonnegative
  have hm := c.mutation_nonnegative
  have hd : ∀ i, 0 ≤ c.mortality i 0 := fun i =>
    c.mortality_nonnegative i 0 (fun _ => le_rfl)
  have hL := c.lipschitzConstant_nonnegative
  exact add_nonneg (add_nonneg (add_nonneg
    (Finset.sum_nonneg (fun i _ => hb i)) (Finset.sum_nonneg (fun p _ => hm p)))
    (Finset.sum_nonneg (fun i _ => hd i))) hL

theorem coefficient_bounds :
    (∀ i, c.birth i ≤ coefficientBound c) ∧
    (∀ p, c.mutation p ≤ coefficientBound c) ∧
    (∀ i, c.mortality i 0 ≤ coefficientBound c) ∧
    c.lipschitzConstant ≤ coefficientBound c := by
  have hb : 0 ≤ ∑ i, c.birth i := Finset.sum_nonneg (fun i _ => c.birth_nonnegative i)
  have hm : 0 ≤ ∑ p, c.mutation p := Finset.sum_nonneg (fun p _ => c.mutation_nonnegative p)
  have hd0 : ∀ i, 0 ≤ c.mortality i 0 := fun i => c.mortality_nonnegative i _ (fun _ => le_rfl)
  have hd : 0 ≤ ∑ i, c.mortality i 0 := Finset.sum_nonneg (fun i _ => hd0 i)
  have hL := c.lipschitzConstant_nonnegative
  dsimp [coefficientBound]
  refine ⟨?_, ?_, ?_, by linarith⟩
  · intro i
    have h := Finset.single_le_sum (fun j _ => c.birth_nonnegative j) (Finset.mem_univ i)
    linarith
  · intro p
    have h := Finset.single_le_sum (fun j _ => c.mutation_nonnegative j) (Finset.mem_univ p)
    linarith
  · intro i
    have h := Finset.single_le_sum (fun j _ => hd0 j) (Finset.mem_univ i)
    linarith

def perCapita (h : Jump D) (μ : MomentLaw MomentScale.linear D) : ℝ := match h with
  | .inl (.inl i) => c.birth i
  | .inl (.inr i) => c.mortality i (CoordinateMoments.vector μ)
  | .inr p => c.mutation p

theorem rate_eq (h : Jump D) (x : State D) (μ : MomentLaw MomentScale.linear D) :
    (rates c).rate h x μ = perCapita c h μ * x (Jump.source h) := by
  rcases h with (i | i) | p <;> rfl

theorem perCapita_nonnegative (h : Jump D) (μ : MomentLaw MomentScale.linear D) :
    0 ≤ perCapita c h μ := by
  rcases h with (i | i) | p
  · exact c.birth_nonnegative i
  · exact c.mortality_nonnegative i _ (CoordinateMoments.vector_nonneg μ)
  · exact c.mutation_nonnegative p

theorem perCapita_le (h : Jump D) (μ : MomentLaw MomentScale.linear D) :
    perCapita c h μ ≤ coefficientBound c * (1 + moment μ) := by
  have hC := coefficientBound_nonnegative c
  have hM := moment_nonneg μ
  obtain ⟨hb, hm, hd, hL⟩ := coefficient_bounds c
  rcases h with (i | i) | p
  · exact (hb i).trans (by nlinarith)
  · exact (mortality_growth c i μ).trans (by
      have hd' := hd i
      have hh := mul_le_mul_of_nonneg_right hL hM
      nlinarith)
  · exact (hm p).trans (by nlinarith)

theorem perCapita_difference_le (h : Jump D) (μ ν : MomentLaw MomentScale.linear D) :
    |perCapita c h μ - perCapita c h ν| ≤ coefficientBound c * wasserstein μ ν := by
  rcases h with (i | i) | p
  · simp only [perCapita, sub_self, abs_zero]
    exact mul_nonneg (coefficientBound_nonnegative c) (wasserstein_nonneg μ ν)
  · exact (mortality_difference_le c i μ ν).trans
      (mul_le_mul_of_nonneg_right (coefficient_bounds c).2.2.2 (wasserstein_nonneg μ ν))
  · simp only [perCapita, sub_self, abs_zero]
    exact mul_nonneg (coefficientBound_nonnegative c) (wasserstein_nonneg μ ν)

theorem coordinate_le_population (x : State D) (i : Fin D) : (x i : ℝ) ≤ populationSize x :=
  Finset.single_le_sum (fun j _ => Nat.cast_nonneg (x j)) (Finset.mem_univ i)

theorem coordinate_difference_le_distance (x y : State D) (i : Fin D) :
    |(x i : ℝ) - y i| ≤ adaptedDistance MomentScale.linear x y :=
  Finset.single_le_sum (fun j _ => abs_nonneg ((x j : ℝ) - y j)) (Finset.mem_univ i)

/-- The stronger per-label estimate before the symmetric framework enlargement. -/
theorem rate_difference_le (h : Jump D) (x y : State D)
    (μ ν : MomentLaw MomentScale.linear D) :
    |(rates c).rate h x μ - (rates c).rate h y ν| ≤
      coefficientBound c * ((1 + moment μ) * adaptedDistance MomentScale.linear x y +
        populationSize y * wasserstein μ ν) := by
  let i := Jump.source h
  have hc := perCapita_nonnegative c h μ
  have hd := perCapita_difference_le c h μ ν
  have hx := coordinate_difference_le_distance x y i
  have hy := coordinate_le_population y i
  have hC := coefficientBound_nonnegative c
  have hM := moment_nonneg μ
  have hW := wasserstein_nonneg μ ν
  have hρ := adaptedDistance_nonneg MomentScale.linear x y
  rw [rate_eq, rate_eq]
  have halg : perCapita c h μ * (x i : ℝ) - perCapita c h ν * (y i : ℝ) =
      perCapita c h μ * ((x i : ℝ) - y i) +
        (perCapita c h μ - perCapita c h ν) * (y i : ℝ) := by ring
  change |perCapita c h μ * (x i : ℝ) - perCapita c h ν * (y i : ℝ)| ≤ _
  rw [halg]
  calc
    |perCapita c h μ * ((x i : ℝ) - y i) +
        (perCapita c h μ - perCapita c h ν) * (y i : ℝ)| ≤
        perCapita c h μ * |(x i : ℝ) - y i| +
          |perCapita c h μ - perCapita c h ν| * (y i : ℝ) := by
      simpa only [abs_mul, abs_of_nonneg hc, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (y i))] using
        abs_add_le (perCapita c h μ * ((x i : ℝ) - y i))
          ((perCapita c h μ - perCapita c h ν) * (y i : ℝ))
    _ ≤ (coefficientBound c * (1 + moment μ)) * adaptedDistance MomentScale.linear x y +
        (coefficientBound c * wasserstein μ ν) * populationSize y :=
      add_le_add (mul_le_mul (perCapita_le c h μ) hx (abs_nonneg _) (by positivity))
        (mul_le_mul hd hy (Nat.cast_nonneg _) (mul_nonneg hC hW))
    _ = _ := by ring

/-- The exact symmetric weighted expression in Proposition 7.3(2). -/
theorem rate_difference_le_standard (h : Jump D) (x y : State D)
    (μ ν : MomentLaw MomentScale.linear D) :
    |(rates c).rate h x μ - (rates c).rate h y ν| ≤ coefficientBound c *
      ((1 + moment μ + moment ν) * adaptedDistance MomentScale.linear x y +
        (1 + populationSize x + populationSize y) * wasserstein μ ν) := by
  apply (rate_difference_le c h x y μ ν).trans
  apply mul_le_mul_of_nonneg_left _ (coefficientBound_nonnegative c)
  have hx := OriginalParticleSystem.population_nonnegative x
  have hM := moment_nonneg ν
  have hρ := adaptedDistance_nonneg MomentScale.linear x y
  have hW := wasserstein_nonneg μ ν
  nlinarith [mul_nonneg hM hρ, mul_nonneg (by linarith : 0 ≤ 1 + populationSize x) hW]

/-- Proposition 7.3's sufficient summed rate-difference condition. -/
theorem sum_rate_difference_le (x y : State D) (μ ν : MomentLaw MomentScale.linear D) :
    (∑ h, |(rates c).rate h x μ - (rates c).rate h y ν|) ≤
      ((Fintype.card (Jump D) : ℝ) * coefficientBound c) *
        ((1 + moment μ + moment ν) * adaptedDistance MomentScale.linear x y +
          (1 + populationSize x + populationSize y) * wasserstein μ ν) := by
  have h := Finset.sum_le_sum (fun h (_ : h ∈ Finset.univ) =>
    rate_difference_le_standard c h x y μ ν)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using h

/-- Actual total-rate growth, Proposition 7.3(3). -/
theorem totalRate_le (x : State D) (μ : MomentLaw MomentScale.linear D) :
    (rates c).totalRate x μ ≤ ((Fintype.card (Jump D) : ℝ) * coefficientBound c) *
      (1 + populationSize x) * (1 + moment μ) := by
  have hC := coefficientBound_nonnegative c
  have hM := moment_nonneg μ
  have hpop := OriginalParticleSystem.population_nonnegative x
  have h (j : Jump D) : (rates c).rate j x μ ≤
      coefficientBound c * (1 + populationSize x) * (1 + moment μ) := by
    rw [rate_eq]
    have hh := mul_le_mul (perCapita_le c j μ) (coordinate_le_population x (Jump.source j))
      (Nat.cast_nonneg _) (mul_nonneg hC (by linarith : 0 ≤ 1 + moment μ))
    nlinarith [mul_nonneg hC (by linarith : 0 ≤ 1 + moment μ)]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => h j)
  simpa only [Rates.totalRate, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hs

end CarryingCapacity.LinearCarryingCapacityBounds
