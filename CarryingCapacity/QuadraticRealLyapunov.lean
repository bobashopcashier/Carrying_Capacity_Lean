import CarryingCapacity.QuadraticModel
import CarryingCapacity.RealPowerLyapunov

/-!
# The full real-exponent quadratic-feedback Lyapunov family

This verifies every exponent `r > 2` in manuscript Proposition 7.7 for the
actual rates `birth * x` and `x * a(M₂(μ))`. Together with the existing
quadratic coupling and activity checks, all three dynamic assumptions hold.
The exponent is real; no integer-exponent or cubic restriction is imposed.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace CarryingCapacity.QuadraticRealLyapunov

/-- The exact Lyapunov function of Proposition 7.7. -/
def function (r : ℝ) (x : State 1) : ℝ := 1 + (x 0 : ℝ) ^ r

theorem function_nonnegative (r : ℝ) (x : State 1) : 0 ≤ function r x := by
  exact add_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem dominates {r : ℝ} (hr : 2 < r) (x : State 1) :
    1 + momentWeight MomentScale.quadratic x ≤ function r x := by
  rw [quadratic_one_weight]
  have h := RealPowerLyapunov.nat_rpow_le (x 0) (by norm_num : (0 : ℝ) < 2) hr.le
  simpa [function, Real.rpow_two] using add_le_add_left h 1

theorem superlinear {r : ℝ} (hr : 2 < r) :
    Tendsto (fun x : State 1 => function r x / (1 + momentWeight MomentScale.quadratic x))
      (comap populationSize atTop) atTop := by
  have h := (RealPowerLyapunov.tendsto_ratio (by norm_num : (0 : ℝ) ≤ 2) hr).comp
    (tendsto_comap : Tendsto (populationSize : State 1 → ℝ)
      (comap populationSize atTop) atTop)
  simpa [Function.comp_def, function, quadratic_one_weight, populationSize, Real.rpow_two] using h

/-- An explicit drift constant, independent of the mortality coefficient. -/
theorem generator_le (birth : ℝ) (hbirth : 0 ≤ birth) (a : MomentMortality)
    {r : ℝ} (hr : 2 < r) (μ : MomentLaw MomentScale.quadratic 1) (x : State 1) :
    (QuadraticModel.rates birth hbirth a).generator μ (function r) x ≤
      (birth * (r * (2 : ℝ) ^ (r - 1))) * function r x := by
  exact (QuadraticModel.generator_eq birth hbirth a μ (fun n => 1 + (n : ℝ) ^ r) x).trans_le
    (RealPowerLyapunov.generator_realPower_le birth (a.rate (moment μ)) hbirth
      (a.nonneg _ (moment_nonneg μ)) (x 0) (by linarith))

/-- Assumption 2.5, with the exact real exponent requested by Proposition 7.7. -/
def lyapunovControl (birth : ℝ) (hbirth : 0 ≤ birth) (a : MomentMortality)
    (r : ℝ) (hr : 2 < r) :
    LyapunovControl MomentScale.quadratic (QuadraticModel.rates birth hbirth a) where
  function := function r
  dominates := dominates hr
  superlinear := superlinear hr
  drift := by
    refine ⟨birth * (r * (2 : ℝ) ^ (r - 1)), by positivity, ?_⟩
    intro x μ _
    have hi : 0 ≤ ∫ y, function r y ∂μ.measure := integral_nonneg (function_nonnegative r)
    have h := generator_le birth hbirth a hr μ x
    have hC : 0 ≤ birth * (r * (2 : ℝ) ^ (r - 1)) := by positivity
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith) hC)

@[simp] theorem lyapunovControl_function (birth : ℝ) (hbirth : 0 ≤ birth)
    (a : MomentMortality) (r : ℝ) (hr : 2 < r) (x : State 1) :
    (lyapunovControl birth hbirth a r hr).function x = 1 + (x 0 : ℝ) ^ r := rfl

/-- Proposition 7.7: the coupling and activity assumptions, and an actual
Lyapunov control with exactly `1 + x^r`, hold for every real `r > 2`. -/
theorem dynamic_assumptions (birth : ℝ) (hbirth : 0 ≤ birth) (a : MomentMortality)
    (r : ℝ) (hr : 2 < r) :
    MomentCouplingBound MomentScale.quadratic (QuadraticModel.rates birth hbirth a) ∧
    MomentActivityBound MomentScale.quadratic (QuadraticModel.rates birth hbirth a) ∧
    ∃ control : LyapunovControl MomentScale.quadratic (QuadraticModel.rates birth hbirth a),
      ∀ x, control.function x = 1 + (x 0 : ℝ) ^ r :=
  ⟨QuadraticModel.couplingBound birth hbirth a, QuadraticModel.activityBound birth hbirth a,
    lyapunovControl birth hbirth a r hr, fun _ => rfl⟩

end CarryingCapacity.QuadraticRealLyapunov
