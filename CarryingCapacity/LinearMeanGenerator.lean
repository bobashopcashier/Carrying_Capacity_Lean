import CarryingCapacity.LinearCarryingCapacityHypotheses

/-!
# The exact multitype coordinate generator and its genuine expectation

This identifies the vector field of Proposition 7.5 from the actual rates.
Every state-coordinate generator is integrable under every first-moment law;
there is no ODE or forward-equation hypothesis in these algebraic identities.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace CarryingCapacity.LinearMeanGenerator
open LinearCarryingCapacity LinearJumpGeometry
variable {D : ℕ} (c : Coefficients D)

def perCapitaVector (h : Jump D) (z : Fin D → ℝ) : ℝ := match h with
  | .inl (.inl i) => c.birth i
  | .inl (.inr i) => c.mortality i z
  | .inr p => c.mutation p

def vectorField (z : Fin D → ℝ) (k : Fin D) : ℝ :=
  ∑ h, perCapitaVector c h z * z (Jump.source h) * displacement h k

/-- The nominal coordinate displacement remains correct after multiplying by
actual rates, including inadmissible jumps at an empty source coordinate. -/
theorem rate_coordinate_increment (h : Jump D) (μ : MomentLaw MomentScale.linear D)
    (x : State D) (k : Fin D) :
    (rates c).rate h x μ * ((Jump.advance h x k : ℝ) - (x k : ℝ)) =
      (rates c).rate h x μ * displacement h k := by
  by_cases hx : Jump.Admissible h x
  · rw [advance_coordinate h x hx]
    ring
  · rw [(rates c).invalid_zero h x μ hx]
    simp

theorem generator_coordinate (μ : MomentLaw MomentScale.linear D) (x : State D) (k : Fin D) :
    (rates c).generator μ (fun y => (y k : ℝ)) x =
      ∑ h, perCapitaVector c h (CoordinateMoments.vector μ) *
        (x (Jump.source h) : ℝ) * displacement h k := by
  unfold Rates.generator
  apply Finset.sum_congr rfl
  intro h _
  rw [rate_coordinate_increment]
  rcases h with (i | i) | p <;> rfl

/-- The unbounded coordinate generator has a genuine finite integral. -/
theorem integrable_generator_coordinate (μ : MomentLaw MomentScale.linear D) (k : Fin D) :
    Integrable (fun x => (rates c).generator μ (fun y => (y k : ℝ)) x) μ.measure := by
  simp_rw [generator_coordinate]
  apply integrable_finset_sum
  intro h _
  exact ((CoordinateMoments.integrable_coordinate μ (Jump.source h)).const_mul _).mul_const _

/-- Its expectation closes exactly in the full vector of type means. -/
theorem integral_generator_coordinate (μ : MomentLaw MomentScale.linear D) (k : Fin D) :
    (∫ x, (rates c).generator μ (fun y => (y k : ℝ)) x ∂μ.measure) =
      vectorField c (CoordinateMoments.vector μ) k := by
  simp_rw [generator_coordinate]
  have hi (h : Jump D) : Integrable (fun x : State D =>
      perCapitaVector c h (CoordinateMoments.vector μ) * (x (Jump.source h) : ℝ) *
        displacement h k) μ.measure :=
    ((CoordinateMoments.integrable_coordinate μ (Jump.source h)).const_mul _).mul_const _
  rw [integral_finset_sum _ (fun h _ => hi h)]
  simp only [integral_mul_const, integral_const_mul, vectorField, CoordinateMoments.linear_vector]

/-- Births, deaths, incoming mutations and outgoing mutations, with exact
source and target coordinates in the mutation sum. -/
theorem vectorField_eq (z : Fin D → ℝ) (k : Fin D) :
    vectorField c z k = (c.birth k - c.mortality k z) * z k +
      ∑ p : {p : Fin D × Fin D // p.1 ≠ p.2},
        c.mutation p * z p.1.1 *
          ((if k = p.1.2 then 1 else 0) - (if k = p.1.1 then 1 else 0)) := by
  simp only [vectorField, Fintype.sum_sum_type, perCapitaVector, Jump.source, displacement]
  have hb : (∑ i, c.birth i * z i * (if k = i then (1 : ℝ) else 0)) = c.birth k * z k := by
    simp [mul_ite, eq_comm]
  have hd : (∑ i, c.mortality i z * z i * (if k = i then (-1 : ℝ) else 0)) =
      -(c.mortality k z * z k) := by
    simp [mul_ite, eq_comm]
  rw [hb, hd]
  ring

/-- Mutations conserve total mass in the closed vector field. -/
theorem sum_vectorField (z : Fin D → ℝ) :
    (∑ k, vectorField c z k) = ∑ k, (c.birth k - c.mortality k z) * z k := by
  simp_rw [vectorField_eq]
  rw [Finset.sum_add_distrib]
  have hm : (∑ k : Fin D, ∑ p : {p : Fin D × Fin D // p.1 ≠ p.2},
      c.mutation p * z p.1.1 *
        ((if k = p.1.2 then (1 : ℝ) else 0) - (if k = p.1.1 then 1 else 0))) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro p _
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp
  rw [hm, add_zero]

end CarryingCapacity.LinearMeanGenerator
