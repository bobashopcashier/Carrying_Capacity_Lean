import CarryingCapacity.DeterministicEnvironmentVolterra
import CarryingCapacity.SynchronousRunningSupremum

/-!
# The manuscript's expected running-distance estimate

The running cost is the supremum over every real time of the two existing
same-noise manuscript processes. Its measurability is derived through rational
observations. The proved stochastic positive-increment estimate and the actual
moment bounds imply the exponential convolution estimate for this supremum.
Finite expectation and integrability of its real version are conclusions.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

namespace CarryingCapacity.DeterministicEnvironmentRunningSupremum
open CommonInitialNoise LyapunovFlowSpace DeterministicEnvironmentLyapunov
open DeterministicEnvironmentProcess DeterministicEnvironmentLaw DeterministicEnvironmentFrozen
open DeterministicEnvironmentCoupling DeterministicEnvironmentVolterra MarkedIntensity

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T)
  (v w : ManuscriptCurves control.function ν (driftConstant control) T hT)

/-- The actual extended running distance, with all real times included. -/
def runningDistance (t : ℝ) (p : Sample (State D) (Jump D)) : ℝ≥0∞ :=
  SynchronousRunningSupremum.intervalSup (fun s => ENNReal.ofReal (adaptedDistance κ
    (manuscriptProcess control hActivity ν T hT v p s)
    (manuscriptProcess control hActivity ν T hT w p s))) t

variable (hCoupling : MomentCouplingBound κ q)
include hCoupling

/-- The actual supremum is AE measurable; this is not an additional hypothesis. -/
theorem aemeasurable_runningDistance (t : ℝ) (ht : 0 ≤ t) :
    AEMeasurable (runningDistance control hActivity ν T hT v w t) (law ν.measure (Jump D)) := by
  exact SynchronousRunningSupremum.aemeasurable_runningCost control.function
    (finite_sublevels control) Jump.advance
    (timeRate κ q (manuscriptExtension control ν (driftConstant control) T hT v) T)
    (exists_uniform_rate_bounds control _ T hT hActivity
      (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn)
    (timeRate κ q (manuscriptExtension control ν (driftConstant control) T hT w) T)
    (exists_uniform_rate_bounds control _ T hT hActivity
      (continuous_manuscriptExtension control ν (driftConstant control) T hT w).continuousOn)
    id id 0 ν.measure
    (manuscript_measurable_timeRate control hCoupling ν (driftConstant control) T hT v)
    (manuscript_measurable_timeRate control hCoupling ν (driftConstant control) T hT w)
    measurable_id measurable_id
    (manuscript_exhaustive control hActivity ν T hT v hCoupling)
    (manuscript_exhaustive control hActivity ν T hT w hCoupling)
    (adaptedDistance κ) ⟨t, ht⟩

/-- Actual synchronous compensation bounds the expectation of the full
running supremum by the manuscript coupling activity. -/
theorem expected_runningDistance_le_activity (t : ℝ) (ht : t ∈ Icc 0 T) :
    (∫⁻ p, runningDistance control hActivity ν T hT v w t p ∂law ν.measure (Jump D)) ≤
      ∫⁻ s in Ioc 0 t, ∫⁻ p, ENNReal.ofReal (couplingActivity κ q
        (manuscriptProcess control hActivity ν T hT v p s)
        (manuscriptProcess control hActivity ν T hT w p s)
        (manuscriptExtension control ν (driftConstant control) T hT v s)
        (manuscriptExtension control ν (driftConstant control) T hT w s)) ∂law ν.measure (Jump D) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  have h := SynchronousRunningSupremum.expected_runningCost_le_activity control.function
    (finite_sublevels control) Jump.advance
    (timeRate κ q (manuscriptExtension control ν (driftConstant control) T hT v) T)
    (exists_uniform_rate_bounds control _ T hT hActivity
      (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn)
    (timeRate κ q (manuscriptExtension control ν (driftConstant control) T hT w) T)
    (exists_uniform_rate_bounds control _ T hT hActivity
      (continuous_manuscriptExtension control ν (driftConstant control) T hT w).continuousOn)
    id id 0 ν.measure
    (manuscript_measurable_timeRate control hCoupling ν (driftConstant control) T hT v)
    (manuscript_measurable_timeRate control hCoupling ν (driftConstant control) T hT w)
    measurable_id measurable_id
    (fun j s x => timeRate_nonnegative κ q _ T j s x)
    (fun j s x => timeRate_nonnegative κ q _ T j s x)
    (manuscript_exhaustive control hActivity ν T hT v hCoupling)
    (manuscript_exhaustive control hActivity ν T hT w hCoupling)
    (adaptedDistance κ) (adaptedDistance_nonneg κ) ⟨t, ht.1⟩
  change (∫⁻ p, runningDistance control hActivity ν T hT v w t p ∂law ν.measure (Jump D)) ≤
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

/-- The genuine moment bound controls integrated expected activity. -/
theorem expected_runningDistance_le_integral (t : ℝ) (ht : t ∈ Icc 0 T) :
    (∫⁻ p, runningDistance control hActivity ν T hT v w t p ∂law ν.measure (Jump D)) ≤
      ENNReal.ofReal (∫ s in Ioc 0 t, coefficient control ν T hCoupling *
        (meanDistance control hActivity ν T hT v w s + inputDistance control ν T hT v w s)) := by
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
  calc
    _ ≤ _ := expected_runningDistance_le_activity control hActivity ν T hT v w hCoupling t ht
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

omit control hActivity ν T hT v w hCoupling in
/-- Once the fixed-time mean is bounded by the forced response, its integrated
activity is bounded by the same response. The running supremum need not be continuous. -/
theorem integral_activity_le_convolution {m d : ℝ → ℝ} {A T : ℝ}
    (hm : ContinuousOn m (Icc 0 T)) (hd : Continuous d) (hA : 0 ≤ A)
    (hbound : ∀ s ∈ Icc 0 T, m s ≤ A *
      ∫ r in (0 : ℝ)..s, Real.exp (A * (s-r)) * d r)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (∫ s in Ioc 0 t, A * (m s + d s)) ≤
      A * ∫ s in (0 : ℝ)..t, Real.exp (A * (t-s)) * d s := by
  let g : ℝ → ℝ := fun s => A * d s
  let r := VolterraGronwall.response 0 A g
  have hg : Continuous g := continuous_const.mul hd
  have hr : Continuous r := VolterraGronwall.continuous_response 0 A hg
  have he (s : ℝ) : r s = A * ∫ u in (0 : ℝ)..s, Real.exp (A * (s-u)) * d u := by
    rw [show r s = VolterraGronwall.response 0 A g s from rfl,
      VolterraGronwall.response_eq_convolution]
    simp only [zero_mul, zero_add]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp [g]
    ring
  have hi : IntegrableOn (fun s => A * (m s + d s)) (Ioc 0 t) :=
    ((continuousOn_const.mul (hm.add hd.continuousOn)).integrableOn_Icc (μ := volume)).mono_set
    (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2))
  have hj : IntegrableOn (fun s => A * r s + g s) (Ioc 0 t) :=
    ((continuous_const.mul hr).add hg).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  calc
    _ ≤ ∫ s in Ioc 0 t, (A * r s + g s) := by
      apply setIntegral_mono_on hi hj measurableSet_Ioc
      intro s hs
      have hb : m s ≤ r s := (hbound s ⟨hs.1.le, hs.2.trans ht.2⟩).trans_eq (he s).symm
      dsimp [g]
      nlinarith
    _ = r t := by
      simpa only [zero_add] using VolterraGronwall.response_integral_eq 0 A hg t ht.1
    _ = _ := he t

/-- The exact manuscript exponential convolution controls the expectation
of the actual running supremum over all times in the horizon. -/
theorem expected_runningDistance_le_volterra (t : ℝ) (ht : t ∈ Icc 0 T) :
    (∫⁻ p, runningDistance control hActivity ν T hT v w t p ∂law ν.measure (Jump D)) ≤
      ENNReal.ofReal (coefficient control ν T hCoupling *
        ∫ s in (0 : ℝ)..t, Real.exp (coefficient control ν T hCoupling * (t-s)) *
          inputDistance control ν T hT v w s) :=
  (expected_runningDistance_le_integral control hActivity ν T hT v w hCoupling t ht).trans
    (ENNReal.ofReal_le_ofReal (integral_activity_le_convolution
      (continuousOn_meanDistance control hActivity ν T hT v w hCoupling)
      (continuous_inputDistance control ν T hT v w)
      (coefficient_nonnegative control ν T hT hCoupling)
      (meanDistance_le_volterra control hActivity ν T hT v w hCoupling) t ht))


/-- The actual extended running distance has finite expectation. -/
theorem lintegral_runningDistance_lt_top (t : ℝ) (ht : t ∈ Icc 0 T) :
    (∫⁻ p, runningDistance control hActivity ν T hT v w t p ∂law ν.measure (Jump D)) < ⊤ :=
  lt_of_le_of_lt (expected_runningDistance_le_volterra control hActivity ν T hT v w hCoupling t ht)
    ENNReal.ofReal_lt_top

/-- Consequently the all-time supremum itself is finite almost surely. -/
theorem ae_runningDistance_lt_top (t : ℝ) (ht : t ∈ Icc 0 T) :
    ∀ᵐ p ∂law ν.measure (Jump D), runningDistance control hActivity ν T hT v w t p < ⊤ :=
  ae_lt_top' (aemeasurable_runningDistance control hActivity ν T hT v w hCoupling t ht.1)
    (lintegral_runningDistance_lt_top control hActivity ν T hT v w hCoupling t ht).ne

/-- Integrability of the genuine real running distance is a consequence of
the stochastic estimate, rather than a premise of it. -/
theorem integrable_runningDistance_toReal (t : ℝ) (ht : t ∈ Icc 0 T) :
    Integrable (fun p => (runningDistance control hActivity ν T hT v w t p).toReal)
      (law ν.measure (Jump D)) :=
  integrable_toReal_of_lintegral_ne_top
    (aemeasurable_runningDistance control hActivity ν T hT v w hCoupling t ht.1)
    (lintegral_runningDistance_lt_top control hActivity ν T hT v w hCoupling t ht).ne

/-- The usual real-valued expected running-distance estimate, with its
integrability and finiteness already proved. -/
theorem integral_runningDistance_le_volterra (t : ℝ) (ht : t ∈ Icc 0 T) :
    (∫ p, (runningDistance control hActivity ν T hT v w t p).toReal ∂law ν.measure (Jump D)) ≤
      coefficient control ν T hCoupling *
        ∫ s in (0 : ℝ)..t, Real.exp (coefficient control ν T hCoupling * (t-s)) *
          inputDistance control ν T hT v w s := by
  have hnonneg : 0 ≤ coefficient control ν T hCoupling *
      ∫ s in (0 : ℝ)..t, Real.exp (coefficient control ν T hCoupling * (t-s)) *
        inputDistance control ν T hT v w s := by
    apply mul_nonneg (coefficient_nonnegative control ν T hT hCoupling)
    apply intervalIntegral.integral_nonneg ht.1
    intro s _
    exact mul_nonneg (Real.exp_nonneg _) (wasserstein_nonneg _ _)
  rw [integral_toReal (aemeasurable_runningDistance control hActivity ν T hT v w hCoupling t ht.1)
    (ae_runningDistance_lt_top control hActivity ν T hT v w hCoupling t ht)]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (expected_runningDistance_le_volterra control hActivity ν T hT v w hCoupling t ht)
  simpa only [ENNReal.toReal_ofReal hnonneg] using h

end CarryingCapacity.DeterministicEnvironmentRunningSupremum
