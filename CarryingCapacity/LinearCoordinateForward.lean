import CarryingCapacity.LinearCoordinateApproximation
import CarryingCapacity.FiniteJumpForward

/-!
# Extending the actual weak equation to coordinate expectations

The finite-support tent tests converge at every state and every neighboring
state. Their generators are dominated by genuine weighted activity. A second
dominated-convergence argument in time extends any genuine finite-support
forward equation with bounded first moments to the unbounded coordinate tests.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace CarryingCapacity.LinearCoordinateForward
open LinearCoordinateApproximation DeterministicEnvironmentRates

variable {D : ℕ} (q : Rates D (MomentLaw MomentScale.linear D))
  (hActivity : MomentActivityBound MomentScale.linear q)
  (ν : MomentLaw MomentScale.linear D) (v : ℝ → MomentLaw MomentScale.linear D)
  (T : ℝ) (hT : 0 ≤ T)
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
    (fun _ : ℝ => activityConstant MomentScale.linear q hActivity * (1 + M) ^ 2)
    (fun n => (hi n).aestronglyMeasurable) (integrable_const _)
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    apply (norm_integral_generator_le q hActivity i n (v s)).trans
    apply mul_le_mul_of_nonneg_left _ (activityConstant_nonnegative _ _ _)
    exact pow_le_pow_left₀ (by linarith [moment_nonneg (v s)])
      (add_le_add_left (hbound s ⟨hs.1.le, hs.2.trans ht.2⟩) 1) 2
  · exact Eventually.of_forall (fun s => integral_generator_tendsto q hActivity i (v s))

/-- The unbounded coordinate equation is a conclusion of the finite-support
weak equation and the genuine activity/moment bounds. -/
theorem coordinate_equation (i : Fin D) (t : ℝ) (ht : t ∈ Icc 0 T) :
    CoordinateMoments.vector (v t) i = CoordinateMoments.vector ν i +
      ∫ s in (0 : ℝ)..t, ∫ x,
        q.generator (v s) (fun y => (y i : ℝ)) x ∂(v s).measure := by
  have he (n : ℕ) : (∫ x, test i n x ∂(v t).measure) =
      (∫ x, test i n x ∂ν.measure) +
        ∫ s in (0 : ℝ)..t, ∫ x, q.generator (v s) (test i n) x ∂(v s).measure :=
    hp.equation (test i n) (finite_support i n) t ht
  exact tendsto_nhds_unique (integral_test_tendsto i (v t))
    (((integral_test_tendsto i ν).add
      (integral_generator_test_tendsto q hActivity ν v T hT hp M hbound i t ht)).congr
      (fun n => (he n).symm))

end CarryingCapacity.LinearCoordinateForward
