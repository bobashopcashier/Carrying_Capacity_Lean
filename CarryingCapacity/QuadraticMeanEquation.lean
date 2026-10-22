import CarryingCapacity.AdaptedCoordinateForward
import CarryingCapacity.QuadraticFeedbackApplication
import CarryingCapacity.NonlinearGlobalProcess

/-!
# The first mean under second-moment mortality

The final displayed equation of Section 7 is derived from the genuine nonlinear
law's finite-support equation, with activity-dominated unbounded coordinate
approximation. The first mean has drift `(birth - a(secondMoment)) * firstMean`.
This is not an autonomous equation in the first mean alone.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace CarryingCapacity.QuadraticMeanEquation
variable (birth : ℝ) (hbirth : 0 ≤ birth) (a : MomentMortality)

/-- The actual expected coordinate drift, depending on the second moment. -/
def lawDrift (μ : MomentLaw MomentScale.quadratic 1) : ℝ :=
  (birth - a.rate (moment μ)) * AdaptedCoordinateForward.mean μ 0

theorem generator_coordinate (μ : MomentLaw MomentScale.quadratic 1) (x : State 1) :
    (QuadraticModel.rates birth hbirth a).generator μ (fun y => (y 0 : ℝ)) x =
      (birth - a.rate (moment μ)) * (x 0 : ℝ) := by
  rw [QuadraticModel.generator_eq, Models.generator_first_moment]

theorem integrable_generator_coordinate (μ : MomentLaw MomentScale.quadratic 1) :
    Integrable (fun x => (QuadraticModel.rates birth hbirth a).generator μ
      (fun y => (y 0 : ℝ)) x) μ.measure := by
  simp_rw [generator_coordinate]
  exact (AdaptedCoordinateForward.integrable_coordinate μ 0).const_mul _

theorem integral_generator_coordinate (μ : MomentLaw MomentScale.quadratic 1) :
    (∫ x, (QuadraticModel.rates birth hbirth a).generator μ
      (fun y => (y 0 : ℝ)) x ∂μ.measure) = lawDrift birth a μ := by
  simp_rw [generator_coordinate]
  rw [integral_const_mul]
  rfl

theorem continuous_lawDrift : Continuous (lawDrift birth a) := by
  have ha : Continuous (fun μ : MomentLaw MomentScale.quadratic 1 => a.rate (moment μ)) := by
    apply (show LipschitzWith ⟨a.constant, a.constant_nonneg⟩
        (fun μ : MomentLaw MomentScale.quadratic 1 => a.rate (moment μ)) from ?_).continuous
    apply LipschitzWith.of_dist_le_mul
    intro μ ν
    simpa only [Real.dist_eq, momentLaw_dist] using a.difference_le_transport μ ν
  exact (continuous_const.sub ha).mul (AdaptedCoordinateForward.mean_lipschitz 0).continuous

variable (r : ℝ) (hr : 2 < r) (ν : MomentLaw MomentScale.quadratic 1)
  (hMoment : Integrable (fun x : State 1 => 1 + (x 0 : ℝ) ^ r) ν.measure)
local notation "control" => QuadraticRealLyapunov.lyapunovControl birth hbirth a r hr
local notation "hActivity" => QuadraticModel.activityBound birth hbirth a
local notation "hCoupling" => QuadraticModel.couplingBound birth hbirth a

theorem coordinate_equation (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Icc 0 T) :
    AdaptedCoordinateForward.mean (QuadraticFeedbackApplication.environment birth hbirth a r hr ν T hT hMoment t) 0 =
      AdaptedCoordinateForward.mean ν 0 + ∫ s in (0 : ℝ)..t,
        lawDrift birth a (QuadraticFeedbackApplication.environment birth hbirth a r hr ν T hT hMoment s) := by
  have hh := AdaptedCoordinateForward.coordinate_equation (QuadraticModel.rates birth hbirth a) hActivity ν
    (QuadraticFeedbackApplication.environment birth hbirth a r hr ν T hT hMoment) T hT
    (QuadraticFeedbackApplication.environment_isSolution birth hbirth a r hr ν T hT hMoment).1
    (DeterministicEnvironmentLyapunov.manuscriptBound control ν
      (DeterministicEnvironmentLyapunov.driftConstant control) T)
    (fun s _ => NonlinearActivityBound.environment_moment_le hActivity control ν T hT hCoupling hMoment s)
    0 t ht
  simpa only [integral_generator_coordinate] using hh

/-- One actual all-time nonlinear law with quadratic feedback. -/
def environment : ℝ → MomentLaw MomentScale.quadratic 1 :=
  NonlinearGlobalProcess.environment control hActivity ν hCoupling hMoment

def firstMean (t : ℝ) : ℝ := AdaptedCoordinateForward.mean
  (environment birth hbirth a r hr ν hMoment t) 0

def secondMoment (t : ℝ) : ℝ := moment (environment birth hbirth a r hr ν hMoment t)

theorem firstMean_eq_integral (t : ℝ) : firstMean birth hbirth a r hr ν hMoment t =
    ∫ x, (x 0 : ℝ) ∂(environment birth hbirth a r hr ν hMoment t).measure := rfl

theorem secondMoment_eq_integral (t : ℝ) : secondMoment birth hbirth a r hr ν hMoment t =
    ∫ x, (x 0 : ℝ) ^ 2 ∂(environment birth hbirth a r hr ν hMoment t).measure :=
  quadratic_one_moment _

theorem firstMean_nonnegative (t : ℝ) : 0 ≤ firstMean birth hbirth a r hr ν hMoment t :=
  AdaptedCoordinateForward.mean_nonnegative _ _

theorem continuousOn_firstMean : ContinuousOn (firstMean birth hbirth a r hr ν hMoment) (Ici 0) :=
  (AdaptedCoordinateForward.mean_lipschitz 0).continuous.comp_continuousOn
    (NonlinearGlobalProcess.continuousOn_environment control hActivity ν hCoupling hMoment)

theorem continuousOn_secondMoment : ContinuousOn (secondMoment birth hbirth a r hr ν hMoment) (Ici 0) :=
  moment_lipschitz.continuous.comp_continuousOn
    (NonlinearGlobalProcess.continuousOn_environment control hActivity ν hCoupling hMoment)

theorem intervalIntegrable_drift (t : ℝ) (ht : 0 ≤ t) : IntervalIntegrable
    (fun s => (birth - a.rate (secondMoment birth hbirth a r hr ν hMoment s)) *
      firstMean birth hbirth a r hr ν hMoment s) volume 0 t :=
  (((continuous_lawDrift birth a).comp_continuousOn
    (NonlinearGlobalProcess.continuousOn_environment control hActivity ν hCoupling hMoment)).mono
      Icc_subset_Ici_self).intervalIntegrable_of_Icc ht

/-- The closed expectation identity retains the second moment in the coefficient. -/
theorem firstMean_equation (t : ℝ) (ht : 0 ≤ t) :
    firstMean birth hbirth a r hr ν hMoment t = AdaptedCoordinateForward.mean ν 0 +
      ∫ s in (0 : ℝ)..t, (birth - a.rate (secondMoment birth hbirth a r hr ν hMoment s)) *
        firstMean birth hbirth a r hr ν hMoment s := by
  have he := NonlinearGlobalProcess.environment_eq_horizon control hActivity ν hCoupling hMoment t ht
  have hi := coordinate_equation birth hbirth a r hr ν hMoment t ht t ⟨ht, le_rfl⟩
  change AdaptedCoordinateForward.mean (NonlinearGlobalProcess.environment control hActivity ν hCoupling hMoment t) 0 = _
  rw [he ⟨ht, le_rfl⟩]
  apply hi.trans
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  change lawDrift birth a (NonlinearFixedPoint.environment control hActivity ν t ht hCoupling hMoment s) =
    lawDrift birth a (NonlinearGlobalProcess.environment control hActivity ν hCoupling hMoment s)
  rw [he hs]

theorem firstMean_zero : firstMean birth hbirth a r hr ν hMoment 0 = AdaptedCoordinateForward.mean ν 0 := by
  simpa only [intervalIntegral.integral_same, add_zero] using
    firstMean_equation birth hbirth a r hr ν hMoment 0 le_rfl

/-- The displayed Section 7 first-mean equation, including a right derivative at zero. -/
theorem hasDerivWithinAt_firstMean (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (firstMean birth hbirth a r hr ν hMoment)
      ((birth - a.rate (secondMoment birth hbirth a r hr ν hMoment t)) *
        firstMean birth hbirth a r hr ν hMoment t) (Ici 0) t := by
  let T := t + 1
  have hT : 0 ≤ T := by dsimp [T]; linarith
  let v := QuadraticFeedbackApplication.environment birth hbirth a r hr ν T hT hMoment
  have hv : Continuous v := NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment
  have hc : Continuous (fun s => lawDrift birth a (v s)) := (continuous_lawDrift birth a).comp hv
  have hd := ((hc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (AdaptedCoordinateForward.mean ν 0)).hasDerivWithinAt (s := Ici 0)
  have he := NonlinearGlobalProcess.environment_eq_horizon control hActivity ν hCoupling hMoment T hT
  have htt : t ∈ Icc 0 T := ⟨ht, by dsimp [T]; linarith⟩
  have hvalue : lawDrift birth a (v t) =
      (birth - a.rate (secondMoment birth hbirth a r hr ν hMoment t)) *
        firstMean birth hbirth a r hr ν hMoment t := by
    change lawDrift birth a (v t) = lawDrift birth a (NonlinearGlobalProcess.environment control hActivity ν hCoupling hMoment t)
    rw [he htt]
    rfl
  rw [hvalue] at hd
  apply hd.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t < T by dsimp [T]; linarith))] with s hs hsT
    have hst : s ∈ Icc 0 T := ⟨hs, hsT.le⟩
    change AdaptedCoordinateForward.mean (NonlinearGlobalProcess.environment control hActivity ν hCoupling hMoment s) 0 = _
    rw [he hst]
    exact coordinate_equation birth hbirth a r hr ν hMoment T hT s hst
  · change AdaptedCoordinateForward.mean (NonlinearGlobalProcess.environment control hActivity ν hCoupling hMoment t) 0 = _
    rw [he htt]
    exact coordinate_equation birth hbirth a r hr ν hMoment T hT t htt

theorem hasDerivAt_firstMean (t : ℝ) (ht : 0 < t) :
    HasDerivAt (firstMean birth hbirth a r hr ν hMoment)
      ((birth - a.rate (secondMoment birth hbirth a r hr ν hMoment t)) *
        firstMean birth hbirth a r hr ν hMoment t) t :=
  (hasDerivWithinAt_firstMean birth hbirth a r hr ν hMoment t ht.le).hasDerivAt (Ici_mem_nhds ht)

end CarryingCapacity.QuadraticMeanEquation
