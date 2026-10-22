import CarryingCapacity.PrescribedObservableLaws
import CarryingCapacity.PopulationCoordinateMoments

/-!
# Uniform empirical and moment limits on a supplied Poisson space

The particle paths are the actual canonical strong functions evaluated at the
supplied initial vectors and their reconstructed driving measures. Standard
Poisson count laws and independence derive the record laws. The convergence
conclusions therefore concern the original probability space, not an additional
product-space realization or an assumed equality of output laws.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators ENNReal Topology

namespace CarryingCapacity.PrescribedPopulationLimits
open ConfigurationLocalization CommonInitialNoise PrescribedPoissonRealization
open PopulationCouplingInitialization

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)
  {Ω : Type*} [MeasurableSpace Ω]
  (M : ∀ n, Label (n + 1) D → Ω → Measure (ℝ × ℝ))
  (z : ∀ n, Ω → Configuration (n + 1) D)

/-- True all-real-time transport error of the supplied-input particle system. -/
def runningError (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  PopulationEmpiricalLimit.runningError control hActivity ν T hT hCoupling hMoment n id
    (record (Label (n + 1) D) (M n) (z n) ω)

def runningMomentError (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  PopulationEmpiricalLimit.runningMomentError control hActivity ν T hT hCoupling hMoment n id
    (record (Label (n + 1) D) (M n) (z n) ω)

def runningVectorError (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  PopulationCoordinateMoments.runningVectorError control hActivity ν T hT hCoupling hMoment n id
    (record (Label (n + 1) D) (M n) (z n) ω)

omit [MeasurableSpace Ω] in
theorem runningMomentError_le (n : ℕ) (ω : Ω) :
    runningMomentError control hActivity ν T hT hCoupling hMoment M z n ω ≤
      runningError control hActivity ν T hT hCoupling hMoment M z n ω :=
  PopulationEmpiricalLimit.runningMomentError_le_runningError
    control hActivity ν T hT hCoupling hMoment n id _

omit [MeasurableSpace Ω] in
theorem runningVectorError_le (n : ℕ) (ω : Ω) :
    runningVectorError control hActivity ν T hT hCoupling hMoment M z n ω ≤
      runningError control hActivity ν T hT hCoupling hMoment M z n ω :=
  PopulationCoordinateMoments.runningVectorError_le_runningError
    control hActivity ν T hT hCoupling hMoment n id _

variable (P : Measure Ω) [IsProbabilityMeasure P]
  (hM : ∀ n j, Measurable (M n j))
  (hPoisson : ∀ n, PoissonObservationLaw.HasDisjointLaws P (Label (n + 1) D) (M n))
  (hz : ∀ n, Measurable (z n))
  (hIndependent : ∀ n, IndepFun (z n) (fun ω j => M n j ω) P)
  (hΨ : ∀ n, Integrable (fun ω => lyapunov control (z n ω)) P)

include hM hPoisson hz hIndependent hΨ

theorem aemeasurable_runningError (n : ℕ) :
    AEMeasurable (runningError control hActivity ν T hT hCoupling hMoment M z n) P := by
  letI : IsProbabilityMeasure (P.map (z n)) := isProbabilityMeasure_map (hz n).aemeasurable
  have hV : Integrable (lyapunov control) (P.map (z n)) :=
    integrable_initial_of_map control (P.map (z n)) P id (z n)
      measurable_id (hz n) (by simp) (hΨ n)
  exact PrescribedObservableLaws.aemeasurable_comp (Label (n + 1) D) (M n) (z n)
    P (hM n) (hPoisson n) (hz n) (hIndependent n) _
    (PopulationEmpiricalLimit.aemeasurable_runningError
      control hActivity ν T hT hCoupling hMoment n id (P.map (z n)) measurable_id hV)

theorem aemeasurable_runningMomentError (n : ℕ) :
    AEMeasurable (runningMomentError control hActivity ν T hT hCoupling hMoment M z n) P := by
  letI : IsProbabilityMeasure (P.map (z n)) := isProbabilityMeasure_map (hz n).aemeasurable
  have hV : Integrable (lyapunov control) (P.map (z n)) :=
    integrable_initial_of_map control (P.map (z n)) P id (z n)
      measurable_id (hz n) (by simp) (hΨ n)
  exact PrescribedObservableLaws.aemeasurable_comp (Label (n + 1) D) (M n) (z n)
    P (hM n) (hPoisson n) (hz n) (hIndependent n) _
    (PopulationEmpiricalLimit.aemeasurable_runningMomentError
      control hActivity ν T hT hCoupling hMoment n id (P.map (z n)) measurable_id hV)

theorem aemeasurable_runningVectorError (n : ℕ) :
    AEMeasurable (runningVectorError control hActivity ν T hT hCoupling hMoment M z n) P := by
  letI : IsProbabilityMeasure (P.map (z n)) := isProbabilityMeasure_map (hz n).aemeasurable
  have hV : Integrable (lyapunov control) (P.map (z n)) :=
    integrable_initial_of_map control (P.map (z n)) P id (z n)
      measurable_id (hz n) (by simp) (hΨ n)
  exact PrescribedObservableLaws.aemeasurable_comp (Label (n + 1) D) (M n) (z n)
    P (hM n) (hPoisson n) (hz n) (hIndependent n) _
    (PopulationCoordinateMoments.aemeasurable_runningVectorError
      control hActivity ν T hT hCoupling hMoment n id (P.map (z n)) measurable_id hV)

variable (hex : ∀ n, ExchangeableMatching.ExchangeableLaw (P.map (z n)))
  (C : ℝ) (hbound : ∀ n, (∫ ω, lyapunov control (z n ω) ∂P) ≤ C)
  (hconv : TendstoInMeasure P
    (fun n ω => wasserstein (empiricalLaw κ (Nat.succ_pos n) (z n ω)) ν) atTop 0)

include hex hbound hconv

/-- Uniform empirical convergence on the supplied probability space, with
only the manuscript initialization and genuine independent Poisson laws. -/
theorem measure_runningError_gt_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ENNReal.ofReal ε <
      runningError control hActivity ν T hT hCoupling hMoment M z n ω}) atTop (𝓝 0) := by
  have hc := PopulationEmpiricalLimit.measure_runningError_gt_tendsto_zero
    control hActivity ν T hT hCoupling hMoment P z hz hex hΨ C hbound hconv ε hε
  apply hc.congr'
  apply Eventually.of_forall
  intro n
  letI : IsProbabilityMeasure (P.map (z n)) := isProbabilityMeasure_map (hz n).aemeasurable
  have hV : Integrable (lyapunov control) (P.map (z n)) :=
    integrable_initial_of_map control (P.map (z n)) P id (z n)
      measurable_id (hz n) (by simp) (hΨ n)
  exact (PrescribedObservableLaws.measure_above (Label (n + 1) D) (M n) (z n)
    P (hM n) (hPoisson n) (hz n) (hIndependent n) _
    (PopulationEmpiricalLimit.aemeasurable_runningError
      control hActivity ν T hT hCoupling hMoment n id (P.map (z n)) measurable_id hV)
    (ENNReal.ofReal ε)).symm

theorem measure_runningMomentError_gt_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ENNReal.ofReal ε <
      runningMomentError control hActivity ν T hT hCoupling hMoment M z n ω}) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (measure_runningError_gt_tendsto_zero control hActivity ν T hT hCoupling hMoment
      M z P hM hPoisson hz hIndependent hΨ hex C hbound hconv ε hε) (fun _ => zero_le _)
  intro n
  exact measure_mono (fun ω h => h.trans_le
    (runningMomentError_le control hActivity ν T hT hCoupling hMoment M z n ω))

theorem measure_runningVectorError_gt_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ENNReal.ofReal ε <
      runningVectorError control hActivity ν T hT hCoupling hMoment M z n ω}) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (measure_runningError_gt_tendsto_zero control hActivity ν T hT hCoupling hMoment
      M z P hM hPoisson hz hIndependent hΨ hex C hbound hconv ε hε) (fun _ => zero_le _)
  intro n
  exact measure_mono (fun ω h => h.trans_le
    (runningVectorError_le control hActivity ν T hT hCoupling hMoment M z n ω))

end CarryingCapacity.PrescribedPopulationLimits
