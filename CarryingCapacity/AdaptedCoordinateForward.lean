import CarryingCapacity.LinearCoordinateForward

/-!
# Genuine first-coordinate equations for arbitrary adapted moments

The original state coordinates remain one-Lipschitz for every normalized
adapted distance, even when the feedback moment is nonlinear. The finite tent
cutoffs therefore extend finite-support weak equations to first coordinates
using actual weighted activity, without renaming the nonlinear moment.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace CarryingCapacity.AdaptedCoordinateForward
open LinearCoordinateApproximation DeterministicEnvironmentRates
variable {D : ℕ} {κ : MomentScale}

/-- The ordinary first coordinate moment, distinct from the κ coordinate moment. -/
def mean (μ : MomentLaw κ D) (i : Fin D) : ℝ := ∫ x, (x i : ℝ) ∂μ.measure

theorem integrable_coordinate (μ : MomentLaw κ D) (i : Fin D) :
    Integrable (fun x => (x i : ℝ)) μ.measure :=
  (CoordinateMoments.integrable_coordinate μ i).mono'
    (measurable_of_countable _).aestronglyMeasurable (Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
      exact κ.nat_le_value _))

theorem mean_nonnegative (μ : MomentLaw κ D) (i : Fin D) : 0 ≤ mean μ i :=
  integral_nonneg (fun _ => Nat.cast_nonneg _)

theorem coordinate_difference_le (i : Fin D) (x y : State D) :
    |(x i : ℝ) - y i| ≤ adaptedDistance κ x y :=
  (κ.abs_sub_lower_bound _ _).trans (coordinateDistance_le κ x y i)

theorem mean_lipschitz (i : Fin D) : LipschitzWith 1 (fun μ : MomentLaw κ D => mean μ i) := by
  apply LipschitzWith.of_dist_le_mul
  intro μ ν
  simpa only [Real.dist_eq, momentLaw_dist, NNReal.coe_one, one_mul] using
    integral_difference_le_wasserstein μ ν (fun x => (x i : ℝ))
      (integrable_coordinate μ i) (integrable_coordinate ν i) (coordinate_difference_le i)

theorem test_difference_le_adapted (i : Fin D) (n : ℕ) (x y : State D) :
    |test i n x - test i n y| ≤ adaptedDistance κ x y :=
  (test_difference_le i n x y).trans (l1_le_adaptedDistance κ x y)

theorem integral_test_tendsto (i : Fin D) (μ : MomentLaw κ D) :
    Tendsto (fun n => ∫ x, test i n x ∂μ.measure) atTop (𝓝 (mean μ i)) :=
  tendsto_integral_of_dominated_convergence (fun x : State D => (x i : ℝ))
    (fun _ => (measurable_of_countable _).aestronglyMeasurable)
    (integrable_coordinate μ i)
    (fun n => Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (test_nonnegative i n x)]
      exact test_le_coordinate i n x))
    (Eventually.of_forall (test_tendsto i))

variable (q : Rates D (MomentLaw κ D)) (hActivity : MomentActivityBound κ q)

theorem norm_generator_le (i : Fin D) (n : ℕ) (μ : MomentLaw κ D) (x : State D) :
    ‖q.generator μ (test i n) x‖ ≤ weightedActivity κ q x μ := by
  rw [Real.norm_eq_abs]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro h _
  rw [abs_mul, abs_of_nonneg (q.nonnegative h x μ)]
  exact mul_le_mul_of_nonneg_left (test_difference_le_adapted i n (Jump.advance h x) x)
    (q.nonnegative h x μ)

include hActivity in
theorem integrable_generator_test (i : Fin D) (n : ℕ) (μ : MomentLaw κ D) :
    Integrable (fun x => q.generator μ (test i n) x) μ.measure :=
  (NonlinearActivityBound.integrable_weightedActivity hActivity μ).mono'
    (measurable_of_countable _).aestronglyMeasurable
    (Eventually.of_forall (norm_generator_le q i n μ))

theorem norm_integral_generator_le (i : Fin D) (n : ℕ) (μ : MomentLaw κ D) :
    ‖∫ x, q.generator μ (test i n) x ∂μ.measure‖ ≤
      activityConstant κ q hActivity * (1 + moment μ) ^ 2 := by
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono
    (integrable_generator_test q hActivity i n μ).norm
    (NonlinearActivityBound.integrable_weightedActivity hActivity μ)
    (norm_generator_le q i n μ)).trans
  exact NonlinearActivityBound.integral_weightedActivity_le hActivity μ

theorem generator_tendsto (i : Fin D) (μ : MomentLaw κ D) (x : State D) :
    Tendsto (fun n => q.generator μ (test i n) x) atTop
      (𝓝 (q.generator μ (fun y => (y i : ℝ)) x)) := by
  apply tendsto_finset_sum
  intro h _
  exact tendsto_const_nhds.mul ((test_tendsto i (Jump.advance h x)).sub (test_tendsto i x))

include hActivity in
theorem integral_generator_tendsto (i : Fin D) (μ : MomentLaw κ D) :
    Tendsto (fun n => ∫ x, q.generator μ (test i n) x ∂μ.measure) atTop
      (𝓝 (∫ x, q.generator μ (fun y => (y i : ℝ)) x ∂μ.measure)) :=
  tendsto_integral_of_dominated_convergence (fun x => weightedActivity κ q x μ)
    (fun _ => (measurable_of_countable _).aestronglyMeasurable)
    (NonlinearActivityBound.integrable_weightedActivity hActivity μ)
    (fun n => Eventually.of_forall (norm_generator_le q i n μ))
    (Eventually.of_forall (generator_tendsto q i μ))

variable (ν : MomentLaw κ D) (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T)
  (hp : FiniteJumpForward.IsSolution Jump.advance (fun j s x => q.rate j x (v s))
    ν.measure (fun s => (v s).measure) T)
  (M : ℝ) (hbound : ∀ s ∈ Icc 0 T, moment (v s) ≤ M)

include hActivity hT hp hbound

theorem integral_generator_test_tendsto (i : Fin D) (t : ℝ) (ht : t ∈ Icc 0 T) :
    Tendsto (fun n => ∫ s in (0 : ℝ)..t,
      ∫ x, q.generator (v s) (test i n) x ∂(v s).measure) atTop
      (𝓝 (∫ s in (0 : ℝ)..t,
        ∫ x, q.generator (v s) (fun y => (y i : ℝ)) x ∂(v s).measure)) := by
  simp only [intervalIntegral.integral_of_le ht.1]
  have hi (n : ℕ) : IntegrableOn
      (fun s => ∫ x, q.generator (v s) (test i n) x ∂(v s).measure) (Ioc 0 t) := by
    have hh := hp.integrable (test i n) (finite_support i n)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT] at hh
    exact hh.mono_set (Ioc_subset_Ioc_right ht.2)
  apply tendsto_integral_of_dominated_convergence
    (fun _ : ℝ => activityConstant κ q hActivity * (1 + M) ^ 2)
    (fun n => (hi n).aestronglyMeasurable) (integrable_const _)
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    apply (norm_integral_generator_le q hActivity i n (v s)).trans
    apply mul_le_mul_of_nonneg_left _ (activityConstant_nonnegative _ _ _)
    exact pow_le_pow_left₀ (by linarith [moment_nonneg (v s)])
      (add_le_add_left (hbound s ⟨hs.1.le, hs.2.trans ht.2⟩) 1) 2
  · exact Eventually.of_forall (fun s => integral_generator_tendsto q hActivity i (v s))

/-- Ordinary first-coordinate expectations satisfy the actual generator
identity even for nonlinear moment feedback. -/
theorem coordinate_equation (i : Fin D) (t : ℝ) (ht : t ∈ Icc 0 T) :
    mean (v t) i = mean ν i + ∫ s in (0 : ℝ)..t,
      ∫ x, q.generator (v s) (fun y => (y i : ℝ)) x ∂(v s).measure := by
  have he (n : ℕ) : (∫ x, test i n x ∂(v t).measure) =
      (∫ x, test i n x ∂ν.measure) +
        ∫ s in (0 : ℝ)..t, ∫ x, q.generator (v s) (test i n) x ∂(v s).measure :=
    hp.equation (test i n) (finite_support i n) t ht
  exact tendsto_nhds_unique (integral_test_tendsto i (v t))
    (((integral_test_tendsto i ν).add
      (integral_generator_test_tendsto q hActivity ν v T hT hp M hbound i t ht)).congr
      (fun n => (he n).symm))

end CarryingCapacity.AdaptedCoordinateForward
