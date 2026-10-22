import CarryingCapacity.NonlinearParticleEmpirical
import CarryingCapacity.RightContinuousSupremum

/-!
# The actual independent empirical error has a measurable running supremum

The finite array of constructed particle paths is right continuous on one
probability-one event. Its empirical law is right continuous because the
configuration space of finitely many particles is discrete; the nonlinear law
curve is continuous. Thus the genuine all-real supremum of their transport
error is almost-everywhere measurable. No uniform empirical convergence or
expected-variation estimate is asserted here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace CarryingCapacity.NonlinearEmpiricalSupremum
open CommonInitialNoise NonlinearParticleEmpirical SynchronousRunningSupremum

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)
  {A : Type*} [MeasurableSpace A] (n : ℕ)
  (initial : A → Fin (n + 1) → State D)

/-- The transport error supremum over every real time in the construction
interval, retaining the terminal value even when the horizon is irrational. -/
def runningError (p : Sample A (Fin (n + 1) × Jump D)) : ℝ≥0∞ :=
  intervalSup (fun t => ENNReal.ofReal
    (error control hActivity ν T hT hCoupling hMoment n initial t p)) T

variable (γ : Measure A) [IsProbabilityMeasure γ]
  (hInitial : Measurable initial)
  (hright : γ.map initial = Measure.pi (fun _ : Fin (n + 1) => ν.measure))
include hInitial hright

/-- The actual real transport error is right continuous simultaneously at
every nonnegative time. Its particles use the endpoint-held continuation
after the construction horizon. -/
theorem ae_error_rightContinuous :
    ∀ᵐ p ∂law γ (Fin (n + 1) × Jump D), ∀ t : ℝ, 0 ≤ t →
      ContinuousWithinAt
        (fun s => error control hActivity ν T hT hCoupling hMoment n initial s p) (Ici t) t := by
  filter_upwards [NonlinearParticleArray.ae_cadlag control hActivity ν T hT hCoupling
    hMoment initial hInitial γ hright] with p hp
  intro t ht
  have hx : ContinuousWithinAt
      (fun s i => NonlinearParticleArray.process control hActivity ν T hT hCoupling hMoment
        initial i p s) (Ici t) t :=
    continuousWithinAt_pi.mpr (fun i => (hp i).1 t ht)
  have he : Continuous (empiricalLaw κ (Nat.succ_pos n) :
      (Fin (n + 1) → State D) → MomentLaw κ D) := continuous_of_discreteTopology
  have hv : ContinuousWithinAt
      (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment) (Ici t) t :=
    (NonlinearFixedPoint.continuous_environment control hActivity ν T hT
      hCoupling hMoment).continuousAt.continuousWithinAt
  have hd := (he.continuousAt.comp_continuousWithinAt hx).dist hv
  simpa only [Function.comp_def, momentLaw_dist, error] using hd

/-- On one full-probability event the all-real supremum equals the countable
rational-observation supremum with the explicit terminal observation. -/
theorem ae_runningError_eq_observedSup :
    ∀ᵐ p ∂law γ (Fin (n + 1) × Jump D),
      runningError control hActivity ν T hT hCoupling hMoment n initial p =
        observedSup (fun t => ENNReal.ofReal
          (error control hActivity ν T hT hCoupling hMoment n initial t p)) T := by
  filter_upwards [ae_error_rightContinuous control hActivity ν T hT hCoupling hMoment
    n initial γ hInitial hright] with p hp
  apply RightContinuousSupremum.intervalSup_eq_observedSup_of_rightContinuous _ T hT
  intro t ht
  exact ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt (hp t ht.1)

/-- AE measurability of the genuine independent empirical running error,
derived from actual path regularity and measurable evaluations. -/
theorem aemeasurable_runningError :
    AEMeasurable (runningError control hActivity ν T hT hCoupling hMoment n initial)
      (law γ (Fin (n + 1) × Jump D)) := by
  apply RightContinuousSupremum.aemeasurable_intervalSup_of_rightContinuous
    (law γ (Fin (n + 1) × Jump D)) _ T hT
  · intro t _
    exact ((measurable_error control hActivity ν T hT hCoupling hMoment n initial hInitial).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal.aemeasurable
  · filter_upwards [ae_error_rightContinuous control hActivity ν T hT hCoupling hMoment
      n initial γ hInitial hright] with p hp
    intro t ht
    exact ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt (hp t ht.1)

end CarryingCapacity.NonlinearEmpiricalSupremum
