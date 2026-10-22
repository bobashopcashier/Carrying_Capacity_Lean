import CarryingCapacity.DeterministicEnvironmentForwardUniqueness
import CarryingCapacity.CoupledDistanceContinuity
import CarryingCapacity.SynchronousCompensation
import CarryingCapacity.TimeDependentStochasticContinuity

/-!
# Synchronous comparison for general moment-bounded nonlinear solutions

Linear forward-law uniqueness identifies the existing prescribed-environment
process with each nonlinear weak solution. Uniform genuine Lyapunov moments
then control the actual coupled endpoint moments, without imposing the sharper
manuscript envelope. Predictable compensation and the original coupling
assumption yield the expected-distance integral inequality.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

namespace CarryingCapacity.DeterministicEnvironmentGeneralCoupling
open CommonInitialNoise LyapunovFlowSpace DeterministicEnvironmentLyapunov
open DeterministicEnvironmentFrozen DeterministicEnvironmentRates MarkedIntensity

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}

/-- The existing actual global process, with the identity initial record. -/
abbrev path (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
    (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T)) :=
  DeterministicEnvironmentProcess.process control hActivity v T hT hv (id : State D → State D)

theorem measurable_path_at (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
    (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))
    (hCoupling : MomentCouplingBound κ q) (s : ℝ) :
    Measurable (fun p => path control hActivity v T hT hv p s) := by
  have h := (DeterministicEnvironmentProcess.measurable_process control hActivity v T hT hv id
    hCoupling measurable_id).comp (measurable_id.prodMk (measurable_const (a := s)))
  simpa only [Function.comp_def] using h

/-- A genuine extended Lyapunov bound controls the adapted first moment. -/
theorem moment_le_of_lyapunov_bound (control : LyapunovControl κ q)
    (μ : MomentLaw κ D) (B : ℝ) (hB : 0 ≤ B)
    (hμ : lyapunovIntegral control.function μ ≤ ENNReal.ofReal B) : moment μ ≤ B := by
  obtain ⟨hi, hb⟩ := (lyapunovIntegral_le_iff (function_nonnegative control) μ hB).mp hμ
  exact (integral_mono μ.integrable_weight hi (fun x => by linarith [control.dominates x])).trans hb

section OneEnvironment
variable (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T)
  (hv : ContinuousOn v (Icc 0 T)) (hCoupling : MomentCouplingBound κ q)
  (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ s ∈ Icc 0 T, lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
  (hInitial : Integrable control.function ν.measure)
include hCoupling hB hEnv hInitial

theorem integrable_lyapunov_at (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun p => control.function (path control hActivity v T hT hv p s))
      (law ν.measure (Jump D)) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact DeterministicEnvironmentProcess.integrable_lyapunov control hActivity v T hT hv id ν.measure
    hCoupling measurable_id B hB hEnv hInitial s hs

theorem integrable_weight_at (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun p => momentWeight κ (path control hActivity v T hT hv p s))
      (law ν.measure (Jump D)) :=
  CoupledDistanceContinuity.integrable_weight_of_lyapunov (law ν.measure (Jump D))
    control.function control.dominates _ (measurable_path_at control hActivity v T hT hv hCoupling s)
    (integrable_lyapunov_at control hActivity ν v T hT hv hCoupling B hB hEnv hInitial s hs)

/-- Fixed-time path continuity is derived from genuine exit exhaustion. -/
theorem ae_continuousAt_intervalPath (t : Icc (0 : ℝ) T) :
    ∀ᵐ p ∂law ν.measure (Jump D), ContinuousAt
      (fun s : Icc (0 : ℝ) T => path control hActivity v T hT hv p s) t := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  have he := DeterministicEnvironmentProcess.ae_exhaustive control hActivity v T hT hv id ν.measure
    hCoupling measurable_id B hB hEnv hInitial
  filter_upwards [TimeDependentStochasticContinuity.ae_continuousWithinAt control.function
    (finite_sublevels control) Jump.advance (timeRate κ q v T)
    (exists_uniform_rate_bounds control v T hT hActivity hv) id 0 ν.measure he t t.property.1] with p hp
  exact (continuousWithinAt_iff_continuousAt_restrict _ t.property).mp
    (hp.mono (fun _ hs => hs.1))

variable (hsol : FiniteJumpForward.IsSolution Jump.advance (fun j s x => q.rate j x (v s))
  ν.measure (fun s => (v s).measure) T)
include hsol

/-- The candidate is the actual marginal, by proved linear law uniqueness. -/
theorem marginal_eq (s : ℝ) (hs : s ∈ Icc 0 T) :
    (law ν.measure (Jump D)).map (fun p => path control hActivity v T hT hv p s) = (v s).measure :=
  DeterministicEnvironmentForwardUniqueness.law_eq_solution control hActivity ν v T hT hv
    hCoupling B hB hEnv hInitial (fun r => (v r).measure) hsol s hs

theorem integral_at (f : State D → ℝ) (s : ℝ) (hs : s ∈ Icc 0 T) :
    (∫ p, f (path control hActivity v T hT hv p s) ∂law ν.measure (Jump D)) =
      ∫ x, f x ∂(v s).measure := by
  have h := DeterministicEnvironmentGeneralForward.integral_actualLaw
    control hActivity v T hT hv ν hCoupling f s
  have he := marginal_eq control hActivity ν v T hT hv hCoupling B hB hEnv hInitial hsol s hs
  change DeterministicEnvironmentGeneralForward.actualLaw control hActivity v T hT hv ν s = _ at he
  rw [he] at h
  exact h.symm

theorem mean_lyapunov_le (s : ℝ) (hs : s ∈ Icc 0 T) :
    (∫ p, control.function (path control hActivity v T hT hv p s) ∂law ν.measure (Jump D)) ≤ B := by
  rw [integral_at control hActivity ν v T hT hv hCoupling B hB hEnv hInitial hsol]
  · exact ((lyapunovIntegral_le_iff (function_nonnegative control) (v s) hB).mp (hEnv s hs)).2
  · exact hs

theorem mean_weight_le (s : ℝ) (hs : s ∈ Icc 0 T) :
    (∫ p, momentWeight κ (path control hActivity v T hT hv p s) ∂law ν.measure (Jump D)) ≤ B := by
  rw [integral_at control hActivity ν v T hT hv hCoupling B hB hEnv hInitial hsol]
  · exact moment_le_of_lyapunov_bound control (v s) B hB (hEnv s hs)
  · exact hs

end OneEnvironment

section Pair
variable (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (v w : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T)
  (hv : ContinuousOn v (Icc 0 T)) (hw : ContinuousOn w (Icc 0 T))

/-- Expected distance of the two actual processes on the same initial/noise space. -/
def meanDistance (s : ℝ) : ℝ :=
  ∫ p, adaptedDistance κ (path control hActivity v T hT hv p s)
    (path control hActivity w T hT hw p s) ∂law ν.measure (Jump D)

/-- The expected original positive-increment activity at current states. -/
def meanActivity (s : ℝ) : ℝ :=
  ∫ p, couplingActivity κ q (path control hActivity v T hT hv p s)
    (path control hActivity w T hT hw p s) (v s) (w s) ∂law ν.measure (Jump D)

/-- The exact current-state synchronous height activity. -/
def activityAt (j : Jump D) (p : Sample (State D) (Jump D) × ℝ) : ℝ :=
  SynchronousCompensation.currentActivity control.function (finite_sublevels control) Jump.advance
    (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv)
    (timeRate κ q w T) (exists_uniform_rate_bounds control w T hT hActivity hw)
    id id 0 (adaptedDistance κ) j p

theorem sum_activityAt (s : ℝ) (hs : s ∈ Icc 0 T) (p : Sample (State D) (Jump D)) :
    (∑ j, activityAt control hActivity v w T hT hv hw j (p,s)) =
      couplingActivity κ q (path control hActivity v T hT hv p s)
        (path control hActivity w T hT hw p s) (v s) (w s) := by
  unfold activityAt SynchronousCompensation.currentActivity
  simp_rw [timeRate_eq κ q _ T _ s hs]
  rfl

theorem activityAt_nonnegative (j : Jump D) (p : Sample (State D) (Jump D) × ℝ) :
    0 ≤ activityAt control hActivity v w T hT hv hw j p :=
  SynchronousPositiveIncrement.heightActivity_nonnegative _ _ _ _ _ _ _
    (timeRate_nonnegative κ q _ T _ _ _) (timeRate_nonnegative κ q _ T _ _ _)

theorem sum_ofReal_activityAt (s : ℝ) (hs : s ∈ Icc 0 T) (p : Sample (State D) (Jump D)) :
    (∑ j, ENNReal.ofReal (activityAt control hActivity v w T hT hv hw j (p,s))) =
      ENNReal.ofReal (couplingActivity κ q (path control hActivity v T hT hv p s)
        (path control hActivity w T hT hw p s) (v s) (w s)) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
    activityAt_nonnegative control hActivity v w T hT hv hw j (p,s)),
    sum_activityAt control hActivity v w T hT hv hw s hs p]

theorem meanDistance_nonnegative (s : ℝ) : 0 ≤ meanDistance control hActivity ν v w T hT hv hw s :=
  integral_nonneg (fun _ => adaptedDistance_nonneg κ _ _)

variable (hCoupling : MomentCouplingBound κ q) (B : ℝ)

/-- Uniform input and coupled-state moment bounds give this finite coefficient. -/
def coefficient : ℝ := couplingConstant κ q hCoupling * (1 + 2 * B)

omit control hActivity ν v w T hT hv hw in
theorem coefficient_nonnegative (hB : 0 ≤ B) : 0 ≤ coefficient hCoupling B :=
  mul_nonneg (couplingConstant_nonnegative κ q hCoupling) (by linarith)

variable (hB : 0 ≤ B)
  (hEnvV : ∀ s ∈ Icc 0 T, lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
  (hEnvW : ∀ s ∈ Icc 0 T, lyapunovIntegral control.function (w s) ≤ ENNReal.ofReal B)
  (hInitial : Integrable control.function ν.measure)
  (hsolV : FiniteJumpForward.IsSolution Jump.advance (fun j s x => q.rate j x (v s))
    ν.measure (fun s => (v s).measure) T)
  (hsolW : FiniteJumpForward.IsSolution Jump.advance (fun j s x => q.rate j x (w s))
    ν.measure (fun s => (w s).measure) T)
include hCoupling hB hEnvV hEnvW hInitial

theorem integrable_distance_at (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun p => adaptedDistance κ (path control hActivity v T hT hv p s)
      (path control hActivity w T hT hw p s)) (law ν.measure (Jump D)) :=
  CouplingExpectation.integrable_distance κ (law ν.measure (Jump D)) _ _
    (measurable_path_at control hActivity v T hT hv hCoupling s)
    (measurable_path_at control hActivity w T hT hw hCoupling s)
    (integrable_weight_at control hActivity ν v T hT hv hCoupling B hB hEnvV hInitial s hs)
    (integrable_weight_at control hActivity ν w T hT hw hCoupling B hB hEnvW hInitial s hs)

theorem integrable_activity_at (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun p => couplingActivity κ q (path control hActivity v T hT hv p s)
      (path control hActivity w T hT hw p s) (v s) (w s)) (law ν.measure (Jump D)) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact CouplingExpectation.integrable_activity κ q hCoupling (law ν.measure (Jump D)) _ _
    (measurable_path_at control hActivity v T hT hv hCoupling s)
    (measurable_path_at control hActivity w T hT hw hCoupling s)
    (integrable_weight_at control hActivity ν v T hT hv hCoupling B hB hEnvV hInitial s hs)
    (integrable_weight_at control hActivity ν w T hT hw hCoupling B hB hEnvW hInitial s hs) _ _

include hsolV hsolW

/-- Every current-state expectation in the coupling assumption is bounded
using the proved marginal identity, not an assumed coupling estimate. -/
theorem meanActivity_le (s : ℝ) (hs : s ∈ Icc 0 T) :
    meanActivity control hActivity ν v w T hT hv hw s ≤ coefficient hCoupling B *
      (meanDistance control hActivity ν v w T hT hv hw s + wasserstein (v s) (w s)) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact CouplingExpectation.integral_activity_le_uniform κ q hCoupling (law ν.measure (Jump D)) _ _
    (measurable_path_at control hActivity v T hT hv hCoupling s)
    (measurable_path_at control hActivity w T hT hw hCoupling s)
    (integrable_weight_at control hActivity ν v T hT hv hCoupling B hB hEnvV hInitial s hs.1)
    (integrable_weight_at control hActivity ν w T hT hw hCoupling B hB hEnvW hInitial s hs.1)
    (v s) (w s) B
    (moment_le_of_lyapunov_bound control (v s) B hB (hEnvV s hs))
    (moment_le_of_lyapunov_bound control (w s) B hB (hEnvW s hs))
    (mean_weight_le control hActivity ν v T hT hv hCoupling B hB hEnvV hInitial hsolV s hs)
    (mean_weight_le control hActivity ν w T hT hw hCoupling B hB hEnvW hInitial hsolW s hs)

/-- The actual same-noise pair is a coupling of the two candidate laws. -/
theorem input_distance_le (s : ℝ) (hs : s ∈ Icc 0 T) :
    wasserstein (v s) (w s) ≤ meanDistance control hActivity ν v w T hT hv hw s :=
  LawCurveContinuity.wasserstein_le_integral_distance (law ν.measure (Jump D)) _ _
    (measurable_path_at control hActivity v T hT hv hCoupling s)
    (measurable_path_at control hActivity w T hT hw hCoupling s) (v s) (w s)
    (marginal_eq control hActivity ν v T hT hv hCoupling B hB hEnvV hInitial hsolV s hs)
    (marginal_eq control hActivity ν w T hT hw hCoupling B hB hEnvW hInitial hsolW s hs)

/-- Expected coupled distance is continuous by genuine superlinear uniform
integrability and fixed-time stochastic continuity of the actual paths. -/
theorem continuousOn_meanDistance :
    ContinuousOn (meanDistance control hActivity ν v w T hT hv hw) (Icc 0 T) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  apply continuousOn_iff_continuous_restrict.mpr
  exact CoupledDistanceContinuity.continuous_expected_distance (law ν.measure (Jump D))
    control.function control.dominates control.superlinear
    (fun (s : Icc (0 : ℝ) T) p => path control hActivity v T hT hv p s)
    (fun (s : Icc (0 : ℝ) T) p => path control hActivity w T hT hw p s)
    (fun s => measurable_path_at control hActivity v T hT hv hCoupling s)
    (fun s => measurable_path_at control hActivity w T hT hw hCoupling s)
    (fun s => integrable_lyapunov_at control hActivity ν v T hT hv hCoupling B hB hEnvV hInitial s s.property.1)
    (fun s => integrable_lyapunov_at control hActivity ν w T hT hw hCoupling B hB hEnvW hInitial s s.property.1)
    B hB
    (fun s => mean_lyapunov_le control hActivity ν v T hT hv hCoupling B hB hEnvV hInitial hsolV s s.property)
    (fun s => mean_lyapunov_le control hActivity ν w T hT hw hCoupling B hB hEnvW hInitial hsolW s s.property)
    (ae_continuousAt_intervalPath control hActivity ν v T hT hv hCoupling B hB hEnvV hInitial)
    (ae_continuousAt_intervalPath control hActivity ν w T hT hw hCoupling B hB hEnvW hInitial)

omit hsolV hsolW in
/-- The actual same-noise counting inequality and predictable compensation
give the extended expected-distance bound. Finite expected activity is not
assumed, and the shared initial record makes the initial distance zero. -/
theorem expected_distance_le_activity (t : ℝ) (ht : t ∈ Icc 0 T) :
    (∫⁻ p, ENNReal.ofReal (adaptedDistance κ (path control hActivity v T hT hv p t)
      (path control hActivity w T hT hw p t)) ∂law ν.measure (Jump D)) ≤
    ∫⁻ s in Ioc 0 t, ∫⁻ p, ENNReal.ofReal (couplingActivity κ q
      (path control hActivity v T hT hv p s) (path control hActivity w T hT hw p s)
      (v s) (w s)) ∂law ν.measure (Jump D) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  have heV := DeterministicEnvironmentProcess.ae_exhaustive control hActivity v T hT hv id ν.measure
    hCoupling measurable_id B hB hEnvV hInitial
  have heW := DeterministicEnvironmentProcess.ae_exhaustive control hActivity w T hT hw id ν.measure
    hCoupling measurable_id B hB hEnvW hInitial
  have h := SynchronousCompensation.expected_distance_le_activity control.function
    (finite_sublevels control) Jump.advance
    (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv)
    (timeRate κ q w T) (exists_uniform_rate_bounds control w T hT hActivity hw)
    id id 0
    (DeterministicEnvironmentFrozen.measurable_timeRate κ q v T hv hCoupling hT)
    (DeterministicEnvironmentFrozen.measurable_timeRate κ q w T hw hCoupling hT)
    measurable_id measurable_id ν.measure
    (fun j s x => timeRate_nonnegative κ q v T j s x)
    (fun j s x => timeRate_nonnegative κ q w T j s x)
    heV heW (adaptedDistance κ) (adaptedDistance_nonneg κ) ⟨t, ht.1⟩
  change (∫⁻ p, ENNReal.ofReal (adaptedDistance κ (path control hActivity v T hT hv p t)
      (path control hActivity w T hT hw p t)) ∂law ν.measure (Jump D)) ≤
    (∫⁻ p, ENNReal.ofReal (adaptedDistance κ p.1 p.1) ∂law ν.measure (Jump D)) +
    ∫⁻ s in Ioc 0 t, ∫⁻ p, ∑ j, ENNReal.ofReal (activityAt control hActivity v w T hT hv hw j (p,s))
      ∂law ν.measure (Jump D) ∂positiveVolume at h
  simp only [adaptedDistance_self, ENNReal.ofReal_zero, lintegral_zero, zero_add,
    TimeDependentDynkin.positiveVolume_restrict_Ioc_zero] at h
  apply h.trans_eq
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  apply lintegral_congr
  intro p
  exact sum_ofReal_activityAt control hActivity v w T hT hv hw s ⟨hs.1.le, hs.2.trans ht.2⟩ p

/-- The genuine stochastic estimate, finite endpoint moments, and expected
distance continuity imply the real integral inequality. No expected coupling
or drift inequality is an input. -/
theorem meanDistance_integral_inequality (t : ℝ) (ht : t ∈ Icc 0 T) :
    meanDistance control hActivity ν v w T hT hv hw t ≤ coefficient hCoupling B *
      ∫ s in Ioc 0 t, (meanDistance control hActivity ν v w T hT hv hw s + wasserstein (v s) (w s)) := by
  have hA := coefficient_nonnegative hCoupling B hB
  have hn (s : ℝ) : 0 ≤ coefficient hCoupling B *
      (meanDistance control hActivity ν v w T hT hv hw s + wasserstein (v s) (w s)) :=
    mul_nonneg hA (add_nonneg (meanDistance_nonnegative control hActivity ν v w T hT hv hw s)
      (wasserstein_nonneg _ _))
  have hd : ContinuousOn (fun s => wasserstein (v s) (w s)) (Icc 0 T) := by
    simpa only [momentLaw_dist] using continuous_dist.comp_continuousOn (hv.prodMk hw)
  have hc : ContinuousOn (fun s => coefficient hCoupling B *
      (meanDistance control hActivity ν v w T hT hv hw s + wasserstein (v s) (w s))) (Icc 0 T) :=
    continuousOn_const.mul ((continuousOn_meanDistance control hActivity ν v w T hT hv hw
      hCoupling B hB hEnvV hEnvW hInitial hsolV hsolW).add hd)
  have hi := (hc.integrableOn_Icc (μ := volume)).mono_set
    (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2))
  have he : ENNReal.ofReal (meanDistance control hActivity ν v w T hT hv hw t) ≤
      ENNReal.ofReal (∫ s in Ioc 0 t, coefficient hCoupling B *
        (meanDistance control hActivity ν v w T hT hv hw s + wasserstein (v s) (w s))) := by
    calc
      _ = ∫⁻ p, ENNReal.ofReal (adaptedDistance κ (path control hActivity v T hT hv p t)
          (path control hActivity w T hT hw p t)) ∂law ν.measure (Jump D) :=
        ofReal_integral_eq_lintegral_ofReal
          (integrable_distance_at control hActivity ν v w T hT hv hw hCoupling B hB hEnvV hEnvW hInitial t ht.1)
          (Eventually.of_forall (fun _ => adaptedDistance_nonneg κ _ _))
      _ ≤ _ := expected_distance_le_activity control hActivity ν v w T hT hv hw hCoupling B hB
        hEnvV hEnvW hInitial t ht
      _ ≤ ∫⁻ s in Ioc 0 t, ENNReal.ofReal (coefficient hCoupling B *
          (meanDistance control hActivity ν v w T hT hv hw s + wasserstein (v s) (w s))) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        rw [← ofReal_integral_eq_lintegral_ofReal
          (integrable_activity_at control hActivity ν v w T hT hv hw hCoupling B hB hEnvV hEnvW hInitial s hs.1.le)
          (Eventually.of_forall (fun _ => CouplingExpectation.activity_nonnegative κ q _ _ _ _))]
        exact ENNReal.ofReal_le_ofReal (meanActivity_le control hActivity ν v w T hT hv hw
          hCoupling B hB hEnvV hEnvW hInitial hsolV hsolW s ⟨hs.1.le, hs.2.trans ht.2⟩)
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn)).symm
  have hr := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hn)).mp he
  simpa only [integral_const_mul] using hr

end Pair
end CarryingCapacity.DeterministicEnvironmentGeneralCoupling
