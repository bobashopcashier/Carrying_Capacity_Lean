import CarryingCapacity.LinearCarryingCapacityBounds
import CarryingCapacity.NonlinearActivityBound

/-!
# Finite-support approximations of the unbounded coordinate tests

The compact tent cutoff is exactly one-Lipschitz for l1 distance and eventually
equals each coordinate at every state. Its actual generator is dominated by
the weighted activity, so genuine first moments and activity bounds justify
passing to the unbounded coordinate in state integrals.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace CarryingCapacity.LinearCoordinateApproximation
variable {D : ℕ}

def test (i : Fin D) (n : ℕ) (x : State D) : ℝ :=
  min (x i : ℝ) (max ((n : ℝ) - populationSize x) 0)

theorem test_nonnegative (i : Fin D) (n : ℕ) (x : State D) : 0 ≤ test i n x :=
  le_min (Nat.cast_nonneg _) (le_max_right _ _)

theorem test_le_coordinate (i : Fin D) (n : ℕ) (x : State D) : test i n x ≤ (x i : ℝ) :=
  min_le_left _ _

theorem finite_support (i : Fin D) (n : ℕ) : (Function.support (test i n)).Finite := by
  apply (finite_moment_sublevel (D := D) MomentScale.linear (n : ℝ)).subset
  intro x hx
  change populationSize x ≤ n
  by_contra hn
  have hzero : test i n x = 0 := by
    rw [test, max_eq_right (by linarith), min_eq_right (Nat.cast_nonneg _)]
  exact hx hzero

theorem population_difference_le (x y : State D) :
    |populationSize x - populationSize y| ≤ adaptedDistance MomentScale.linear x y := by
  rw [populationSize, populationSize, ← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

theorem test_difference_le (i : Fin D) (n : ℕ) (x y : State D) :
    |test i n x - test i n y| ≤ adaptedDistance MomentScale.linear x y := by
  apply (abs_min_sub_min_le_max _ _ _ _).trans
  apply max_le
  · exact LinearCarryingCapacityBounds.coordinate_difference_le_distance x y i
  · have h := abs_max_sub_max_le_abs ((n : ℝ) - populationSize x)
      ((n : ℝ) - populationSize y) 0
    have he : ((n : ℝ) - populationSize x) - ((n : ℝ) - populationSize y) =
        -(populationSize x - populationSize y) := by ring
    rw [he, abs_neg] at h
    exact h.trans (population_difference_le x y)

theorem eventually_test_eq (i : Fin D) (x : State D) :
    ∀ᶠ n : ℕ in atTop, test i n x = (x i : ℝ) := by
  have h : ∀ᶠ n : ℕ in atTop, populationSize x + (x i : ℝ) ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [h] with n hn
  apply min_eq_left
  exact (show (x i : ℝ) ≤ (n : ℝ) - populationSize x by linarith).trans (le_max_left _ _)

theorem test_tendsto (i : Fin D) (x : State D) :
    Tendsto (fun n => test i n x) atTop (𝓝 (x i : ℝ)) :=
  tendsto_const_nhds.congr' ((eventually_test_eq i x).mono (fun _ h => h.symm))

variable (q : Rates D (MomentLaw MomentScale.linear D))

theorem norm_generator_le (i : Fin D) (n : ℕ) (μ : MomentLaw MomentScale.linear D)
    (x : State D) :
    ‖q.generator μ (test i n) x‖ ≤ weightedActivity MomentScale.linear q x μ := by
  rw [Real.norm_eq_abs]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro h _
  rw [abs_mul, abs_of_nonneg (q.nonnegative h x μ)]
  exact mul_le_mul_of_nonneg_left (test_difference_le i n (Jump.advance h x) x)
    (q.nonnegative h x μ)

/-- Every approximating generator is genuinely integrable. -/
theorem integrable_generator_test (hActivity : MomentActivityBound MomentScale.linear q)
    (i : Fin D) (n : ℕ) (μ : MomentLaw MomentScale.linear D) :
    Integrable (fun x => q.generator μ (test i n) x) μ.measure :=
  (NonlinearActivityBound.integrable_weightedActivity hActivity μ).mono'
    (measurable_of_countable _).aestronglyMeasurable
    (Eventually.of_forall (norm_generator_le q i n μ))

theorem norm_integral_generator_le (hActivity : MomentActivityBound MomentScale.linear q)
    (i : Fin D) (n : ℕ) (μ : MomentLaw MomentScale.linear D) :
    ‖∫ x, q.generator μ (test i n) x ∂μ.measure‖ ≤
      DeterministicEnvironmentRates.activityConstant MomentScale.linear q hActivity *
        (1 + moment μ) ^ 2 := by
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono
    (integrable_generator_test q hActivity i n μ).norm
    (NonlinearActivityBound.integrable_weightedActivity hActivity μ)
    (norm_generator_le q i n μ)).trans
  exact NonlinearActivityBound.integral_weightedActivity_le hActivity μ

theorem generator_tendsto (i : Fin D) (μ : MomentLaw MomentScale.linear D) (x : State D) :
    Tendsto (fun n => q.generator μ (test i n) x) atTop
      (𝓝 (q.generator μ (fun y => (y i : ℝ)) x)) := by
  apply tendsto_finset_sum
  intro h _
  exact tendsto_const_nhds.mul ((test_tendsto i (Jump.advance h x)).sub (test_tendsto i x))

theorem integral_test_tendsto (i : Fin D) (μ : MomentLaw MomentScale.linear D) :
    Tendsto (fun n => ∫ x, test i n x ∂μ.measure) atTop
      (𝓝 (CoordinateMoments.vector μ i)) := by
  apply tendsto_integral_of_dominated_convergence (fun x : State D => (x i : ℝ))
    (fun _ => (measurable_of_countable _).aestronglyMeasurable)
    (CoordinateMoments.integrable_coordinate μ i)
  · intro n
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (test_nonnegative i n x)]
      exact test_le_coordinate i n x)
  · exact Eventually.of_forall (test_tendsto i)

/-- Generator convergence is dominated by actual integrable activity. -/
theorem integral_generator_tendsto (hActivity : MomentActivityBound MomentScale.linear q)
    (i : Fin D) (μ : MomentLaw MomentScale.linear D) :
    Tendsto (fun n => ∫ x, q.generator μ (test i n) x ∂μ.measure) atTop
      (𝓝 (∫ x, q.generator μ (fun y => (y i : ℝ)) x ∂μ.measure)) :=
  tendsto_integral_of_dominated_convergence (fun x => weightedActivity MomentScale.linear q x μ)
    (fun _ => (measurable_of_countable _).aestronglyMeasurable)
    (NonlinearActivityBound.integrable_weightedActivity hActivity μ)
    (fun n => Eventually.of_forall (norm_generator_le q i n μ))
    (Eventually.of_forall (generator_tendsto q i μ))

end CarryingCapacity.LinearCoordinateApproximation
