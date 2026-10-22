import CarryingCapacity.CoordinateMoments
import CarryingCapacity.PopulationSkorokhodLimit

/-!
# Uniform convergence of the actual vector of type moments

The scalar moment convergence theorem controls the sum of coordinate moments.
Here the stronger l1-vector estimate controls every coordinate simultaneously,
uniformly over the entire time interval. The linear specialization supplies
the mean-vector convergence used in Proposition 7.5; the closed ODE remains
a separate unbounded-test argument.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.PopulationCoordinateMoments
open CommonInitialNoise ConfigurationLocalization SynchronousRunningSupremum

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)

local notation "v" => NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment

section Row
variable {A : Type*} [MeasurableSpace A] (n : ℕ)
  (initial : A → Configuration (n + 1) D)

/-- The true all-time l1 error of the vector of empirical coordinate moments. -/
def runningVectorError (p : Sample A (Label (n + 1) D)) : ℝ≥0∞ :=
  intervalSup (fun t => ENNReal.ofReal (∑ i,
    |CoordinateMoments.vector (empiricalLaw κ (Nat.succ_pos n)
      (ConfigurationTimeDependent.process control (Nat.succ_pos n) initial p t)) i -
      CoordinateMoments.vector (v t) i|)) T

omit [MeasurableSpace A] in
theorem runningVectorError_le_runningError (p : Sample A (Label (n + 1) D)) :
    runningVectorError control hActivity ν T hT hCoupling hMoment n initial p ≤
      PopulationEmpiricalLimit.runningError control hActivity ν T hT hCoupling hMoment n initial p := by
  apply iSup_le
  intro t
  exact (ENNReal.ofReal_le_ofReal (CoordinateMoments.l1_difference_le_wasserstein _ _)).trans
    (le_iSup_of_le t le_rfl)

/-- The supremum is a genuine AE-measurable random variable. -/
theorem aemeasurable_runningVectorError (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial)
    (hV : Integrable (fun a => lyapunov control (initial a)) μ) :
    AEMeasurable (runningVectorError control hActivity ν T hT hCoupling hMoment n initial)
      (law μ (Label (n + 1) D)) := by
  apply RightContinuousSupremum.aemeasurable_intervalSup_of_rightContinuous _ _ T hT
  · intro t _
    have hm := (measurable_of_countable (fun z : Configuration (n + 1) D =>
      ∑ i, |CoordinateMoments.vector (empiricalLaw κ (Nat.succ_pos n) z) i -
        CoordinateMoments.vector (v t) i|)).comp
      ((ConfigurationTimeDependent.measurable_process control (Nat.succ_pos n) initial hinit).of_uncurry_right (y := t))
    exact hm.ennreal_ofReal.aemeasurable
  · filter_upwards [CanonicalSkorokhodPaths.ae_configuration_cadlag
      control (Nat.succ_pos n) initial μ hinit hV] with p hp
    intro t ht
    have he : ContinuousWithinAt (fun s => empiricalLaw κ (Nat.succ_pos n)
        (ConfigurationTimeDependent.process control (Nat.succ_pos n) initial p s)) (Ici t) t :=
      (PopulationSkorokhodLimit.uniformContinuous_empirical
      (κ := κ) (D := D) (Nat.succ_pos n)).continuous.continuousAt.comp_continuousWithinAt
      (hp.1 t ht.1)
    have hv : ContinuousWithinAt v (Ici t) t :=
      (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment).continuousAt.continuousWithinAt
    exact CoordinateMoments.continuousWithinAt_l1Difference_ofReal he hv

end Row

section ManuscriptInitialization
variable {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (z : ∀ n, Ω → Configuration (n + 1) D) (hz : ∀ n, Measurable (z n))
  (hex : ∀ n, ExchangeableMatching.ExchangeableLaw (P.map (z n)))
  (hΨ : ∀ n, Integrable (fun ω => lyapunov control (z n ω)) P)
  (C : ℝ) (hbound : ∀ n, (∫ ω, lyapunov control (z n ω) ∂P) ≤ C)
  (hconv : TendstoInMeasure P
    (fun n ω => wasserstein (empiricalLaw κ (Nat.succ_pos n) (z n ω)) ν) atTop 0)

include hz hex hΨ hbound hconv

/-- All type moments converge uniformly in probability under the original
manuscript initialization, with the exact original vector law and actual noise. -/
theorem measure_runningVectorError_gt_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (P.map (z n)) (Label (n + 1) D))
      {p | ENNReal.ofReal ε < runningVectorError control hActivity ν T hT hCoupling hMoment n id p})
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (PopulationEmpiricalLimit.measure_runningError_gt_tendsto_zero control hActivity ν T hT hCoupling hMoment
      P z hz hex hΨ C hbound hconv ε hε) (fun _ => zero_le _)
  intro n
  exact measure_mono (fun p hp => hp.trans_le
    (runningVectorError_le_runningError control hActivity ν T hT hCoupling hMoment n id p))

theorem probability_runningVectorError_gt_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (P.map (z n)) (Label (n + 1) D)).real
      {p | ENNReal.ofReal ε < runningVectorError control hActivity ν T hT hCoupling hMoment n id p})
      atTop (𝓝 0) :=
  ENNReal.tendsto_toReal ENNReal.zero_ne_top |>.comp
    (measure_runningVectorError_gt_tendsto_zero control hActivity ν T hT hCoupling hMoment
      P z hz hex hΨ C hbound hconv ε hε)

end ManuscriptInitialization
end CarryingCapacity.PopulationCoordinateMoments
