import CarryingCapacity.LinearCarryingCapacityBounds
import CarryingCapacity.LinearJumpGeometry

/-!
# All dynamic hypotheses for multitype carrying capacity

This assembles Proposition 7.3 for the exact globally Lipschitz vector-mortality
model. The coupling uses the full shared-jump term, invalid jumps are handled,
and the Lyapunov exponent is any real `p > 1`.
-/

noncomputable section
open scoped BigOperators

namespace CarryingCapacity.LinearCarryingCapacityHypotheses
open LinearCarryingCapacity LinearCarryingCapacityBounds
variable {D : ℕ} (c : Coefficients D)

theorem couplingBound : MomentCouplingBound MomentScale.linear (rates c) := by
  refine ⟨2 * ((Fintype.card (Jump D) : ℝ) * coefficientBound c), ?_, ?_⟩
  · have hC := coefficientBound_nonnegative c
    positivity
  · intro x y μ ν
    have h := (LinearJumpGeometry.couplingActivity_le (rates c) x y μ ν).trans
      (mul_le_mul_of_nonneg_left (sum_rate_difference_le c x y μ ν) (by norm_num : (0 : ℝ) ≤ 2))
    simpa only [linear_weight, mul_assoc] using h

theorem activityBound : MomentActivityBound MomentScale.linear (rates c) := by
  refine ⟨2 * ((Fintype.card (Jump D) : ℝ) * coefficientBound c), ?_, ?_⟩
  · have hC := coefficientBound_nonnegative c
    positivity
  · intro x μ
    have h := (LinearJumpGeometry.weightedActivity_le (rates c) x μ).trans
      (mul_le_mul_of_nonneg_left (totalRate_le c x μ) (by norm_num : (0 : ℝ) ≤ 2))
    simpa only [linear_weight, mul_assoc] using h

/-- Proposition 7.3's complete dynamic assumption verification. -/
theorem dynamic_assumptions (p : ℝ) (hp : 1 < p) :
    MomentCouplingBound MomentScale.linear (rates c) ∧
    MomentActivityBound MomentScale.linear (rates c) ∧
    ∃ control : LyapunovControl MomentScale.linear (rates c),
      ∀ x, control.function x = 1 + populationSize x ^ p :=
  ⟨couplingBound c, activityBound c, lyapunovControl c p hp, fun _ => rfl⟩

end CarryingCapacity.LinearCarryingCapacityHypotheses
