import CarryingCapacity.LinearCoordinateForward
import CarryingCapacity.LinearMeanGenerator
import CarryingCapacity.LinearCarryingCapacityApplication
import CarryingCapacity.NonlinearGlobalProcess

/-!
# The genuine closed mean equation

The nonlinear law supplies the finite-support weak equation. Weighted activity
justifies passing to unbounded coordinate tests, giving the closed multitype
mean equation. Consistency of actual finite-horizon laws gives one global
nonnegative mean curve, with the indicated right derivative at time zero.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace CarryingCapacity.LinearMeanEquation
open LinearCarryingCapacity LinearMeanGenerator
variable {D : ℕ} (c : Coefficients D)

theorem continuous_mortality_moment (i : Fin D) :
    Continuous (fun μ : MomentLaw MomentScale.linear D => c.mortality i (CoordinateMoments.vector μ)) := by
  apply (show LipschitzWith ⟨c.lipschitzConstant, c.lipschitzConstant_nonnegative⟩
      (fun μ : MomentLaw MomentScale.linear D => c.mortality i (CoordinateMoments.vector μ)) from ?_).continuous
  apply LipschitzWith.of_dist_le_mul
  intro μ ν
  simpa only [Real.dist_eq, momentLaw_dist] using mortality_difference_le c i μ ν

theorem continuous_vectorField_moment (i : Fin D) :
    Continuous (fun μ : MomentLaw MomentScale.linear D => vectorField c (CoordinateMoments.vector μ) i) := by
  apply continuous_finset_sum
  intro h _
  have hc : Continuous (fun μ : MomentLaw MomentScale.linear D => perCapitaVector c h (CoordinateMoments.vector μ)) := by
    rcases h with (j | j) | p
    · exact continuous_const
    · exact continuous_mortality_moment c j
    · exact continuous_const
  exact (hc.mul (CoordinateMoments.coordinate_lipschitz (Jump.source h)).continuous).mul continuous_const

variable (r : ℝ) (hr : 1 < r) (ν : MomentLaw MomentScale.linear D)
  (hMoment : Integrable (fun x : State D => 1 + populationSize x ^ r) ν.measure)

local notation "control" => LinearCarryingCapacity.lyapunovControl c r hr
local notation "hActivity" => LinearCarryingCapacityHypotheses.activityBound c
local notation "hCoupling" => LinearCarryingCapacityHypotheses.couplingBound c

/-- The finite-horizon mean equation, derived from actual nonlinear laws. -/
theorem coordinate_equation (T : ℝ) (hT : 0 ≤ T) (i : Fin D)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    CoordinateMoments.vector (LinearCarryingCapacityApplication.environment c r hr ν T hT hMoment t) i =
      CoordinateMoments.vector ν i + ∫ s in (0 : ℝ)..t,
        vectorField c (CoordinateMoments.vector
          (LinearCarryingCapacityApplication.environment c r hr ν T hT hMoment s)) i := by
  have hh := LinearCoordinateForward.coordinate_equation (rates c) hActivity ν
    (LinearCarryingCapacityApplication.environment c r hr ν T hT hMoment) T hT
    (LinearCarryingCapacityApplication.environment_isSolution c r hr ν T hT hMoment).1
    (DeterministicEnvironmentLyapunov.manuscriptBound control ν
      (DeterministicEnvironmentLyapunov.driftConstant control) T)
    (fun s _ => NonlinearActivityBound.environment_moment_le hActivity control ν T hT hCoupling hMoment s)
    i t ht
  simpa only [integral_generator_coordinate] using hh

/-- Actual type means of the single all-time nonlinear law. -/
def mean (t : ℝ) : Fin D → ℝ :=
  CoordinateMoments.vector (NonlinearGlobalProcess.environment control hActivity ν hCoupling hMoment t)

theorem mean_nonnegative (t : ℝ) (i : Fin D) : 0 ≤ mean c r hr ν hMoment t i :=
  CoordinateMoments.vector_nonneg _ _

theorem continuousOn_mean : ContinuousOn (mean c r hr ν hMoment) (Ici 0) :=
  CoordinateMoments.continuous_vector.comp_continuousOn
    (NonlinearGlobalProcess.continuousOn_environment control hActivity ν hCoupling hMoment)

/-- The closed drift of the actual mean is continuous on the whole half-line. -/
theorem continuousOn_vectorField_mean (i : Fin D) :
    ContinuousOn (fun t => vectorField c (mean c r hr ν hMoment t) i) (Ici 0) :=
  (continuous_vectorField_moment c i).comp_continuousOn
    (NonlinearGlobalProcess.continuousOn_environment control hActivity ν hCoupling hMoment)

/-- The unbounded coordinate drift has a genuine finite time integral on every
compact horizon; no convention for a nonintegrable integral is used. -/
theorem intervalIntegrable_vectorField_mean (i : Fin D) (t : ℝ) (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => vectorField c (mean c r hr ν hMoment s) i) volume 0 t :=
  ((continuousOn_vectorField_mean c r hr ν hMoment i).mono Icc_subset_Ici_self).intervalIntegrable_of_Icc ht

/-- Global consistency transfers the genuine closed equation to every finite time. -/
theorem mean_equation (i : Fin D) (t : ℝ) (ht : 0 ≤ t) :
    mean c r hr ν hMoment t i = CoordinateMoments.vector ν i +
      ∫ s in (0 : ℝ)..t, vectorField c (mean c r hr ν hMoment s) i := by
  have he := NonlinearGlobalProcess.environment_eq_horizon control hActivity ν hCoupling hMoment t ht
  have hi := coordinate_equation c r hr ν hMoment t ht i t ⟨ht, le_rfl⟩
  change CoordinateMoments.vector (NonlinearGlobalProcess.environment control hActivity ν hCoupling hMoment t) i = _
  rw [he ⟨ht, le_rfl⟩]
  apply hi.trans
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  change vectorField c (CoordinateMoments.vector (NonlinearFixedPoint.environment control hActivity ν t ht hCoupling hMoment s)) i =
    vectorField c (CoordinateMoments.vector (NonlinearGlobalProcess.environment control hActivity ν hCoupling hMoment s)) i
  rw [he hs]

theorem mean_zero : mean c r hr ν hMoment 0 = CoordinateMoments.vector ν := by
  funext i
  simpa only [intervalIntegral.integral_same, add_zero] using mean_equation c r hr ν hMoment i 0 le_rfl

/-- The actual all-time mean solves the ODE, with a right derivative at zero.
The derivative is derived by FTC from the proved unbounded-test equation. -/
theorem hasDerivWithinAt_mean (i : Fin D) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => mean c r hr ν hMoment s i)
      (vectorField c (mean c r hr ν hMoment t) i) (Ici 0) t := by
  let T := t + 1
  have hT : 0 ≤ T := by dsimp [T]; linarith
  let v := LinearCarryingCapacityApplication.environment c r hr ν T hT hMoment
  have hv : Continuous v := NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment
  have hc : Continuous (fun s => vectorField c (CoordinateMoments.vector (v s)) i) :=
    (continuous_vectorField_moment c i).comp hv
  have hd := ((hc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (CoordinateMoments.vector ν i)).hasDerivWithinAt (s := Ici 0)
  have he := NonlinearGlobalProcess.environment_eq_horizon control hActivity ν hCoupling hMoment T hT
  have htt : t ∈ Icc 0 T := ⟨ht, by dsimp [T]; linarith⟩
  have hvalue : vectorField c (CoordinateMoments.vector (v t)) i =
      vectorField c (mean c r hr ν hMoment t) i := by
    dsimp [mean, v]
    rw [he htt]
    rfl
  rw [hvalue] at hd
  apply hd.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t < T by dsimp [T]; linarith))] with s hs hsT
    have hst : s ∈ Icc 0 T := ⟨hs, hsT.le⟩
    change CoordinateMoments.vector (NonlinearGlobalProcess.environment control hActivity ν hCoupling hMoment s) i = _
    rw [he hst]
    exact coordinate_equation c r hr ν hMoment T hT i s hst
  · change CoordinateMoments.vector (NonlinearGlobalProcess.environment control hActivity ν hCoupling hMoment t) i = _
    rw [he htt]
    exact coordinate_equation c r hr ν hMoment T hT i t htt

/-- Ordinary differentiability holds at every strictly positive time. -/
theorem hasDerivAt_mean (i : Fin D) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => mean c r hr ν hMoment s i)
      (vectorField c (mean c r hr ν hMoment t) i) t :=
  (hasDerivWithinAt_mean c r hr ν hMoment i t ht.le).hasDerivAt (Ici_mem_nhds ht)

end CarryingCapacity.LinearMeanEquation
