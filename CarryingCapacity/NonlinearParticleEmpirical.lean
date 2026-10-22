import CarryingCapacity.NonlinearParticleArray
import CarryingCapacity.CompactIntervalIntegration

/-!
# Empirical error of the actual independent nonlinear particle array

The particles are the constructed processes on projected initial/noise records.
Their genuine iid laws, joint measurability and the proved Lyapunov envelope
discharge the independent-array empirical-error theorems. Both each error and
its time expectation are integrable before the actual time-integrated limit is
stated. Initial-record spaces may vary with the row size.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace CarryingCapacity.NonlinearParticleEmpirical
open CommonInitialNoise LyapunovFlowSpace DeterministicEnvironmentLyapunov

private theorem measurable_swap_uncurry {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (f : A → B → C) (hf : Measurable (Function.uncurry f)) :
    Measurable (Function.uncurry (fun b a => f a b)) :=
  hf.comp measurable_swap

private theorem measurable_interval_uncurry {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (f : A → ℝ → B)
    (hf : Measurable (Function.uncurry f)) (T : ℝ) :
    Measurable (Function.uncurry (fun (t : Icc (0 : ℝ) T) a => f a t)) :=
  hf.comp (measurable_snd.prodMk (measurable_subtype_coe.comp measurable_fst))

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)

private theorem environment_eq_curve (t : Icc (0 : ℝ) T) :
    NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment t =
      (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hMoment).val t :=
  manuscriptExtension_eq control ν (driftConstant control) T hT _ t

section Row
variable {A : Type*} [MeasurableSpace A] (n : ℕ)
  (initial : A → Fin (n + 1) → State D)

/-- Transport error of the actual independent nonlinear particles. The
environment is held at its endpoint after `T`; limit claims are on `[0,T]`. -/
def error (t : ℝ) (p : Sample A (Fin (n + 1) × Jump D)) : ℝ :=
  wasserstein (empiricalLaw κ (Nat.succ_pos n) (fun i =>
    NonlinearParticleArray.process control hActivity ν T hT hCoupling hMoment initial i p t))
    (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment t)

omit [MeasurableSpace A] in
theorem error_nonnegative (t : ℝ) (p : Sample A (Fin (n + 1) × Jump D)) :
    0 ≤ error control hActivity ν T hT hCoupling hMoment n initial t p :=
  wasserstein_nonneg _ _

/-- Joint measurability includes the actual sample and real time. -/
theorem measurable_error (hInitial : Measurable initial) :
    Measurable (Function.uncurry (error control hActivity ν T hT hCoupling hMoment n initial)) := by
  have h := EmpiricalArrayError.measurable_joint_error
    (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment)
    (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment) n
    (fun i t p => NonlinearParticleArray.process control hActivity ν T hT hCoupling hMoment initial i p t)
    (fun i => measurable_swap_uncurry
      (NonlinearParticleArray.process control hActivity ν T hT hCoupling hMoment initial i)
      (NonlinearParticleArray.measurable_process control hActivity ν T hT hCoupling hMoment
        initial hInitial i))
  exact h

variable (γ : Measure A) [IsProbabilityMeasure γ]

/-- The actual expected independent empirical discrepancy. -/
def beta (t : ℝ) : ℝ :=
  ∫ p, error control hActivity ν T hT hCoupling hMoment n initial t p
    ∂law γ (Fin (n + 1) × Jump D)

omit [IsProbabilityMeasure γ] in
theorem beta_nonnegative (t : ℝ) :
    0 ≤ beta control hActivity ν T hT hCoupling hMoment n initial γ t :=
  integral_nonneg (error_nonnegative control hActivity ν T hT hCoupling hMoment n initial t)

theorem stronglyMeasurable_beta (hInitial : Measurable initial) :
    StronglyMeasurable (beta control hActivity ν T hT hCoupling hMoment n initial γ) :=
  (measurable_error control hActivity ν T hT hCoupling hMoment n initial hInitial).stronglyMeasurable.integral_prod_right

variable (hInitial : Measurable initial)
  (hright : γ.map initial = Measure.pi (fun _ : Fin (n + 1) => ν.measure))
include hInitial hright

/-- Error integrability is derived from the actual iid marginals. -/
theorem integrable_error (t : Icc (0 : ℝ) T) :
    Integrable (error control hActivity ν T hT hCoupling hMoment n initial t)
      (law γ (Fin (n + 1) × Jump D)) := by
  unfold error
  rw [environment_eq_curve]
  exact EmpiricalArrayError.integrable_error (law γ (Fin (n + 1) × Jump D))
    ((NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hMoment).val t) n
    (fun i p => NonlinearParticleArray.process control hActivity ν T hT hCoupling hMoment initial i p t)
    (fun i => NonlinearParticleArray.measurable_process_at control hActivity ν T hT hCoupling hMoment initial hInitial i t)
    (NonlinearParticleArray.independent_at control hActivity ν T hT hCoupling hMoment initial hInitial γ hright t)
    (fun i => NonlinearParticleArray.process_marginal control hActivity ν T hT hCoupling hMoment initial hInitial γ hright i t)

/-- The actual expected discrepancy has the manuscript's `2 Mκ(v_t)` bound. -/
theorem beta_le_twice_moment (t : Icc (0 : ℝ) T) :
    beta control hActivity ν T hT hCoupling hMoment n initial γ t ≤
      2 * moment (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment t) := by
  unfold beta error
  rw [environment_eq_curve]
  exact EmpiricalArrayError.integral_error_le (law γ (Fin (n + 1) × Jump D))
    ((NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hMoment).val t) n
    (fun i p => NonlinearParticleArray.process control hActivity ν T hT hCoupling hMoment initial i p t)
    (fun i => NonlinearParticleArray.measurable_process_at control hActivity ν T hT hCoupling hMoment initial hInitial i t)
    (NonlinearParticleArray.independent_at control hActivity ν T hT hCoupling hMoment initial hInitial γ hright t)
    (fun i => NonlinearParticleArray.process_marginal control hActivity ν T hT hCoupling hMoment initial hInitial γ hright i t)

/-- The terminal Lyapunov envelope is a uniform deterministic bound. -/
theorem beta_le_envelope (t : Icc (0 : ℝ) T) :
    beta control hActivity ν T hT hCoupling hMoment n initial γ t ≤
      2 * manuscriptBound control ν (driftConstant control) T := by
  have hb := manuscriptExtension_integrable_and_bound control ν (driftConstant control) T
    (driftConstant_nonnegative control) hT
    (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hMoment) t
  have hm : moment (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment t) ≤
      manuscriptBound control ν (driftConstant control) T := by
    apply (integral_mono (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment t).integrable_weight
      hb.1 (fun x => by linarith [control.dominates x])).trans hb.2
  exact (beta_le_twice_moment control hActivity ν T hT hCoupling hMoment n initial γ hInitial hright t).trans
    (mul_le_mul_of_nonneg_left hm (by norm_num))

/-- The real time expectation is genuinely integrable on the full horizon. -/
theorem integrableOn_beta :
    IntegrableOn (beta control hActivity ν T hT hCoupling hMoment n initial γ) (Icc 0 T) volume := by
  apply (integrable_const (2 * manuscriptBound control ν (driftConstant control) T)).mono'
    (stronglyMeasurable_beta control hActivity ν T hT hCoupling hMoment n initial γ hInitial).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_of_nonneg (beta_nonnegative control hActivity ν T hT hCoupling hMoment n initial γ t)]
  exact beta_le_envelope control hActivity ν T hT hCoupling hMoment n initial γ hInitial hright ⟨t, ht⟩

/-- The usual oriented time integral is also genuinely integrable. -/
theorem intervalIntegrable_beta :
    IntervalIntegrable (beta control hActivity ν T hT hCoupling hMoment n initial γ) volume 0 T :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr
    (integrableOn_beta control hActivity ν T hT hCoupling hMoment n initial γ hInitial hright)

end Row

section Arrays
variable {A : ℕ → Type*} [∀ n, MeasurableSpace (A n)]
  (initial : ∀ n, A n → Fin (n + 1) → State D) (hInitial : ∀ n, Measurable (initial n))
  (γ : ∀ n, Measure (A n)) [∀ n, IsProbabilityMeasure (γ n)]
  (hright : ∀ n, (γ n).map (initial n) = Measure.pi (fun _ : Fin (n + 1) => ν.measure))
include hInitial hright

/-- Fixed-time expected error converges for the actual constructed arrays,
even when their initial-record spaces change with the row size. -/
theorem beta_tendsto_zero (t : Icc (0 : ℝ) T) :
    Tendsto (fun n => beta control hActivity ν T hT hCoupling hMoment n (initial n) (γ n) t)
      atTop (𝓝 0) := by
  have hi := manuscriptCurve_integrable_and_bound (function_nonnegative control)
    (driftConstant_nonnegative control)
    (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hMoment) t
  have h := EmpiricalArrayError.integral_arrayError_tendsto_zero
    (fun n => law (γ n) (Fin (n + 1) × Jump D))
    ((NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hMoment).val t)
    control.function control.dominates control.superlinear hi.1
    (fun n i p => NonlinearParticleArray.process control hActivity ν T hT hCoupling hMoment (initial n) i p t)
    (fun n i => NonlinearParticleArray.measurable_process_at control hActivity ν T hT hCoupling hMoment (initial n) (hInitial n) i t)
    (fun n => NonlinearParticleArray.independent_at control hActivity ν T hT hCoupling hMoment (initial n) (hInitial n) (γ n) (hright n) t)
    (fun n i => NonlinearParticleArray.process_marginal control hActivity ν T hT hCoupling hMoment (initial n) (hInitial n) (γ n) (hright n) i t)
  simpa only [beta, error, environment_eq_curve] using h

set_option maxHeartbeats 800000 in
/-- Actual empirical error integrated against any finite measure on the
interval time type tends to zero. Bounds outside the horizon are not assumed. -/
theorem integral_subtype_beta_tendsto_zero (τ : Measure (Icc (0 : ℝ) T)) [IsFiniteMeasure τ] :
    Tendsto (fun n => ∫ t : Icc (0 : ℝ) T,
      beta control hActivity ν T hT hCoupling hMoment n (initial n) (γ n) t ∂τ) atTop (𝓝 0) := by
  let v := NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hMoment
  have hi (t : Icc (0 : ℝ) T) := manuscriptCurve_integrable_and_bound
    (function_nonnegative control) (driftConstant_nonnegative control) v t
  have hb (t : Icc (0 : ℝ) T) : (∫ x, control.function x ∂(v.val t).measure) ≤
      manuscriptBound control ν (driftConstant control) T := by
    exact (hi t).2.trans (exponentialEnvelope_mono_time
      (integral_nonneg (function_nonnegative control)) (driftConstant_nonnegative control) t.property.2)
  have h := EmpiricalArrayError.integral_time_arrayError_tendsto_zero τ
    (fun n => law (γ n) (Fin (n + 1) × Jump D)) v.val v.val.continuous
    control.function control.dominates control.superlinear (fun t => (hi t).1)
    (manuscriptBound control ν (driftConstant control) T) hb
    (fun n i t p => NonlinearParticleArray.process control hActivity ν T hT hCoupling hMoment (initial n) i p t)
    (fun n i => measurable_interval_uncurry
      (NonlinearParticleArray.process control hActivity ν T hT hCoupling hMoment (initial n) i)
      (NonlinearParticleArray.measurable_process control hActivity ν T hT hCoupling hMoment (initial n) (hInitial n) i) T)
    (fun n t => NonlinearParticleArray.independent_at control hActivity ν T hT hCoupling hMoment (initial n) (hInitial n) (γ n) (hright n) t)
    (fun n t i => NonlinearParticleArray.process_marginal control hActivity ν T hT hCoupling hMoment (initial n) (hInitial n) (γ n) (hright n) i t)
  simpa only [beta, error, environment_eq_curve, v] using h

/-- The genuine real Lebesgue time integral of the actual expected errors
tends to zero, including a zero construction horizon. -/
theorem integral_Icc_beta_tendsto_zero :
    Tendsto (fun n => ∫ t in Icc (0 : ℝ) T,
      beta control hActivity ν T hT hCoupling hMoment n (initial n) (γ n) t) atTop (𝓝 0) := by
  have h := integral_subtype_beta_tendsto_zero control hActivity ν T hT hCoupling hMoment
    initial hInitial γ hright (CompactIntervalIntegration.timeMeasure T)
  simpa only [CompactIntervalIntegration.integral_eq_setIntegral] using h

/-- Removing the null initial endpoint gives the usual `(0,T]` form. -/
theorem integral_Ioc_beta_tendsto_zero :
    Tendsto (fun n => ∫ t in Ioc (0 : ℝ) T,
      beta control hActivity ν T hT hCoupling hMoment n (initial n) (γ n) t) atTop (𝓝 0) := by
  simpa only [integral_Icc_eq_integral_Ioc] using
    integral_Icc_beta_tendsto_zero control hActivity ν T hT hCoupling hMoment initial hInitial γ hright

/-- The paper's ordinary real time-integrated empirical-error limit. -/
theorem intervalIntegral_beta_tendsto_zero :
    Tendsto (fun n => ∫ t in (0 : ℝ)..T,
      beta control hActivity ν T hT hCoupling hMoment n (initial n) (γ n) t) atTop (𝓝 0) := by
  simpa only [intervalIntegral.integral_of_le hT] using
    integral_Ioc_beta_tendsto_zero control hActivity ν T hT hCoupling hMoment initial hInitial γ hright

end Arrays
end CarryingCapacity.NonlinearParticleEmpirical
