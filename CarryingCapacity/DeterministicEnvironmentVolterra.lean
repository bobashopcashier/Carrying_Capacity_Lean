import CarryingCapacity.DeterministicEnvironmentCoupling
import CarryingCapacity.SynchronousCompensation
import CarryingCapacity.VolterraGronwall

/-!
# The actual synchronous environment estimate

The synchronous height activity is identified with the manuscript's coupling
activity on the construction interval. All states and noises here belong to
the already constructed pair of prescribed-environment processes.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

namespace CarryingCapacity.DeterministicEnvironmentVolterra
open CommonInitialNoise LyapunovFlowSpace DeterministicEnvironmentLyapunov
open DeterministicEnvironmentProcess DeterministicEnvironmentLaw DeterministicEnvironmentFrozen
open DeterministicEnvironmentCoupling MarkedIntensity

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T)
  (v w : ManuscriptCurves control.function ν (driftConstant control) T hT)

/-- The actual current-state height activity, specialized without introducing
an auxiliary pair process or changing either marginal construction. -/
def activityAt (j : Jump D) (p : Sample (State D) (Jump D) × ℝ) : ℝ :=
  SynchronousCompensation.currentActivity control.function (finite_sublevels control) Jump.advance
    (timeRate κ q (manuscriptExtension control ν (driftConstant control) T hT v) T)
    (exists_uniform_rate_bounds control _ T hT hActivity
      (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn)
    (timeRate κ q (manuscriptExtension control ν (driftConstant control) T hT w) T)
    (exists_uniform_rate_bounds control _ T hT hActivity
      (continuous_manuscriptExtension control ν (driftConstant control) T hT w).continuousOn)
    id id 0 (adaptedDistance κ) j p

/-- On the actual horizon, the complete three-region synchronous activity
is exactly the paper's couplingActivity, including simultaneous jumps. -/
theorem sum_activityAt (s : ℝ) (hs : s ∈ Icc 0 T) (p : Sample (State D) (Jump D)) :
    (∑ j, activityAt control hActivity ν T hT v w j (p,s)) =
      couplingActivity κ q (manuscriptProcess control hActivity ν T hT v p s)
        (manuscriptProcess control hActivity ν T hT w p s)
        (manuscriptExtension control ν (driftConstant control) T hT v s)
        (manuscriptExtension control ν (driftConstant control) T hT w s) := by
  unfold activityAt SynchronousCompensation.currentActivity
  simp_rw [timeRate_eq κ q _ T _ s hs]
  rfl

theorem activityAt_nonnegative (j : Jump D) (p : Sample (State D) (Jump D) × ℝ) :
    0 ≤ activityAt control hActivity ν T hT v w j p :=
  SynchronousPositiveIncrement.heightActivity_nonnegative _ _ _ _ _ _ _
    (timeRate_nonnegative κ q _ T _ _ _) (timeRate_nonnegative κ q _ T _ _ _)

/-- The nonnegative sum is also the exact extended activity integrand. -/
theorem sum_ofReal_activityAt (s : ℝ) (hs : s ∈ Icc 0 T) (p : Sample (State D) (Jump D)) :
    (∑ j, ENNReal.ofReal (activityAt control hActivity ν T hT v w j (p,s))) =
      ENNReal.ofReal (couplingActivity κ q (manuscriptProcess control hActivity ν T hT v p s)
        (manuscriptProcess control hActivity ν T hT w p s)
        (manuscriptExtension control ν (driftConstant control) T hT v s)
        (manuscriptExtension control ν (driftConstant control) T hT w s)) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => activityAt_nonnegative control hActivity ν T hT v w j (p,s)),
    sum_activityAt control hActivity ν T hT v w s hs p]

variable (hCoupling : MomentCouplingBound κ q)
include hCoupling

/-- The actual shared-noise counting inequality and nonnegative compensation
give the expected-distance bound, without assuming any expected activity is finite. -/
theorem expected_distance_le_activity (t : ℝ) (ht : t ∈ Icc 0 T) :
    (∫⁻ p, ENNReal.ofReal (adaptedDistance κ
      (manuscriptProcess control hActivity ν T hT v p t)
      (manuscriptProcess control hActivity ν T hT w p t)) ∂law ν.measure (Jump D)) ≤
    ∫⁻ s in Ioc 0 t, ∫⁻ p, ENNReal.ofReal (couplingActivity κ q
      (manuscriptProcess control hActivity ν T hT v p s)
      (manuscriptProcess control hActivity ν T hT w p s)
      (manuscriptExtension control ν (driftConstant control) T hT v s)
      (manuscriptExtension control ν (driftConstant control) T hT w s)) ∂law ν.measure (Jump D) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  have h := SynchronousCompensation.expected_distance_le_activity control.function
    (finite_sublevels control) Jump.advance
    (timeRate κ q (manuscriptExtension control ν (driftConstant control) T hT v) T)
    (exists_uniform_rate_bounds control _ T hT hActivity
      (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn)
    (timeRate κ q (manuscriptExtension control ν (driftConstant control) T hT w) T)
    (exists_uniform_rate_bounds control _ T hT hActivity
      (continuous_manuscriptExtension control ν (driftConstant control) T hT w).continuousOn)
    id id 0
    (manuscript_measurable_timeRate control hCoupling ν (driftConstant control) T hT v)
    (manuscript_measurable_timeRate control hCoupling ν (driftConstant control) T hT w)
    measurable_id measurable_id ν.measure
    (fun j s x => timeRate_nonnegative κ q _ T j s x)
    (fun j s x => timeRate_nonnegative κ q _ T j s x)
    (manuscript_exhaustive control hActivity ν T hT v hCoupling)
    (manuscript_exhaustive control hActivity ν T hT w hCoupling)
    (adaptedDistance κ) (adaptedDistance_nonneg κ) ⟨t, ht.1⟩
  change (∫⁻ p, ENNReal.ofReal (adaptedDistance κ
      (manuscriptProcess control hActivity ν T hT v p t)
      (manuscriptProcess control hActivity ν T hT w p t)) ∂law ν.measure (Jump D)) ≤
    (∫⁻ p, ENNReal.ofReal (adaptedDistance κ p.1 p.1) ∂law ν.measure (Jump D)) +
    ∫⁻ s in Ioc 0 t, ∫⁻ p, ∑ j, ENNReal.ofReal (activityAt control hActivity ν T hT v w j (p,s))
      ∂law ν.measure (Jump D) ∂positiveVolume at h
  simp only [adaptedDistance_self, ENNReal.ofReal_zero, lintegral_zero, zero_add,
    TimeDependentDynkin.positiveVolume_restrict_Ioc_zero] at h
  apply h.trans_eq
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  apply lintegral_congr
  intro p
  exact sum_ofReal_activityAt control hActivity ν T hT v w s ⟨hs.1.le, hs.2.trans ht.2⟩ p

/-- The genuine extended estimate becomes the finite real integral inequality
using only the independently proved moment and continuity bounds. -/
theorem meanDistance_integral_inequality (t : ℝ) (ht : t ∈ Icc 0 T) :
    meanDistance control hActivity ν T hT v w t ≤ coefficient control ν T hCoupling *
      ∫ s in Ioc 0 t, (meanDistance control hActivity ν T hT v w s + inputDistance control ν T hT v w s) := by
  have hA := coefficient_nonnegative control ν T hT hCoupling
  have hn (s : ℝ) : 0 ≤ coefficient control ν T hCoupling *
      (meanDistance control hActivity ν T hT v w s + inputDistance control ν T hT v w s) :=
    mul_nonneg hA (add_nonneg (meanDistance_nonnegative control hActivity ν T hT v w s)
      (wasserstein_nonneg _ _))
  have hc : ContinuousOn (fun s => coefficient control ν T hCoupling *
      (meanDistance control hActivity ν T hT v w s + inputDistance control ν T hT v w s)) (Icc 0 T) :=
    continuousOn_const.mul ((continuousOn_meanDistance control hActivity ν T hT v w hCoupling).add
      (continuous_inputDistance control ν T hT v w).continuousOn)
  have hi := (hc.integrableOn_Icc (μ := volume)).mono_set
    (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2))
  have he : ENNReal.ofReal (meanDistance control hActivity ν T hT v w t) ≤
      ENNReal.ofReal (∫ s in Ioc 0 t, coefficient control ν T hCoupling *
        (meanDistance control hActivity ν T hT v w s + inputDistance control ν T hT v w s)) := by
    calc
      _ = ∫⁻ p, ENNReal.ofReal (adaptedDistance κ
          (manuscriptProcess control hActivity ν T hT v p t)
          (manuscriptProcess control hActivity ν T hT w p t)) ∂law ν.measure (Jump D) :=
        ofReal_integral_eq_lintegral_ofReal
          (integrable_distance_at control hActivity ν T hT v w hCoupling t ht.1)
          (Eventually.of_forall (fun _ => adaptedDistance_nonneg κ _ _))
      _ ≤ _ := expected_distance_le_activity control hActivity ν T hT v w hCoupling t ht
      _ ≤ ∫⁻ s in Ioc 0 t, ENNReal.ofReal (coefficient control ν T hCoupling *
          (meanDistance control hActivity ν T hT v w s + inputDistance control ν T hT v w s)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        rw [← ofReal_integral_eq_lintegral_ofReal
          (integrable_activity_at control hActivity ν T hT v w hCoupling s hs.1.le)
          (Eventually.of_forall (fun _ => CouplingExpectation.activity_nonnegative κ q _ _ _ _))]
        exact ENNReal.ofReal_le_ofReal
          (meanActivity_le control hActivity ν T hT v w hCoupling s ⟨hs.1.le, hs.2.trans ht.2⟩)
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn)).symm
  have hr := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hn)).mp he
  simpa only [integral_const_mul] using hr

/-- The fixed-time expected distance satisfies the manuscript's
exponential-kernel bound, derived from the stochastic construction. -/
theorem meanDistance_le_volterra (t : ℝ) (ht : t ∈ Icc 0 T) :
    meanDistance control hActivity ν T hT v w t ≤ coefficient control ν T hCoupling *
      ∫ s in (0 : ℝ)..t, Real.exp (coefficient control ν T hCoupling * (t - s)) *
        inputDistance control ν T hT v w s :=
  VolterraGronwall.le_volterra hT
    (continuousOn_meanDistance control hActivity ν T hT v w hCoupling)
    (continuous_inputDistance control ν T hT v w) (coefficient_nonnegative control ν T hT hCoupling)
    (meanDistance_integral_inequality control hActivity ν T hT v w hCoupling) t ht

/-- The actual invariant evolution map has the precise Volterra bound needed
by the independently proved Bielecki contraction theorem. -/
theorem output_distance_le_volterra (t : Icc (0 : ℝ) T) :
    wasserstein
      ((DeterministicEnvironmentEvolution.evolution control hActivity ν T hT v hCoupling).val t)
      ((DeterministicEnvironmentEvolution.evolution control hActivity ν T hT w hCoupling).val t) ≤
      coefficient control ν T hCoupling *
        ∫ s in (0 : ℝ)..t.val, Real.exp (coefficient control ν T hCoupling * (t.val - s)) *
          inputDistance control ν T hT v w s :=
  (output_distance_le control hActivity ν T hT v w hCoupling t).trans
    (meanDistance_le_volterra control hActivity ν T hT v w hCoupling t t.property)

end CarryingCapacity.DeterministicEnvironmentVolterra
