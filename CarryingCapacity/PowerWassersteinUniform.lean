import CarryingCapacity.PowerWassersteinTopology
import CarryingCapacity.PrescribedPopulationLimits

/-!
# Uniform ordinary Wasserstein-p convergence on the supplied probability space

For every real p > 1, the actual supremum over all times in [0,T] is
AE measurable and converges to zero in probability. The proof uses the
genuine coupling inequality Wp^p ≤ Wκ and the already constructed particle
system; no convergence or measurability of the new supremum is assumed.
The linear endpoint p = 1 is exactly the existing l1-ground adapted distance.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators ENNReal Topology

namespace CarryingCapacity.PowerWassersteinUniform
open CommonInitialNoise ConfigurationLocalization PrescribedPoissonRealization
open PopulationCouplingInitialization SynchronousRunningSupremum

variable {D : ℕ} {p : ℝ} (hp : 1 < p)

/-- Ordinary Wp is continuous in the manuscript's adapted transport topology. -/
theorem continuous_distance : Continuous (fun a :
    MomentLaw (MomentScale.realPower p hp.le) D ×
      MomentLaw (MomentScale.realPower p hp.le) D =>
    PowerWasserstein.distance hp a.1 a.2) := by
  have h := @continuous_dist (MomentLaw (MomentScale.realPower p hp.le) D)
    (PowerWasserstein.metricSpace hp).toPseudoMetricSpace
  simpa only [PowerWasserstein.topology_eq hp] using h

/-- The continuous Wp distance can be composed with two right-continuous laws. -/
theorem continuousWithinAt_distance_ofReal {A : Type*} [TopologicalSpace A]
    {f g : A → MomentLaw (MomentScale.realPower p hp.le) D} {s : Set A} {a : A}
    (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a) :
    ContinuousWithinAt (fun x => ENNReal.ofReal (PowerWasserstein.distance hp (f x) (g x))) s a := by
  have hfg : ContinuousWithinAt (fun x => (f x, g x)) s a := hf.prodMk hg
  have hd : ContinuousWithinAt (fun x => PowerWasserstein.distance hp (f x) (g x)) s a :=
    ContinuousAt.comp_continuousWithinAt (f := fun x => (f x, g x))
      (g := fun z : MomentLaw (MomentScale.realPower p hp.le) D ×
        MomentLaw (MomentScale.realPower p hp.le) D => PowerWasserstein.distance hp z.1 z.2)
      (continuous_distance hp).continuousAt hfg
  exact ContinuousAt.comp_continuousWithinAt
    (f := fun x => PowerWasserstein.distance hp (f x) (g x)) (g := ENNReal.ofReal)
    ENNReal.continuous_ofReal.continuousAt hd

/-- A deterministic strict-tail inclusion for the genuine all-real supremum. -/
theorem intervalSup_gt_imp (μ ν : ℝ → MomentLaw (MomentScale.realPower p hp.le) D)
    (T ε : ℝ) (hε : 0 < ε)
    (h : ENNReal.ofReal ε < intervalSup
      (fun t => ENNReal.ofReal (PowerWasserstein.distance hp (μ t) (ν t))) T) :
    ENNReal.ofReal (ε ^ p) < intervalSup
      (fun t => ENNReal.ofReal (wasserstein (μ t) (ν t))) T := by
  obtain ⟨t, ht⟩ := lt_iSup_iff.mp h
  have hd : ε < PowerWasserstein.distance hp (μ t) (ν t) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε.le).mp ht
  have hpow := (Real.rpow_lt_rpow hε.le hd (zero_lt_one.trans hp)).trans_le
    (PowerWasserstein.distance_rpow_le_wasserstein hp (μ t) (ν t))
  exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (Real.rpow_nonneg hε.le p)).mpr hpow).trans_le (le_iSup_of_le t le_rfl)

variable {q : Rates D (MomentLaw (MomentScale.realPower p hp.le) D)}
  (control : LyapunovControl (MomentScale.realPower p hp.le) q)
  (hActivity : MomentActivityBound (MomentScale.realPower p hp.le) q)
  (ν : MomentLaw (MomentScale.realPower p hp.le) D) (T : ℝ) (hT : 0 ≤ T)
  (hCoupling : MomentCouplingBound (MomentScale.realPower p hp.le) q)
  (hMoment : Integrable control.function ν.measure)

local notation "v" => NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment

/-- The exact all-real ordinary-Wp error of a canonical constructed population. -/
def canonicalRunningError {A : Type*} [MeasurableSpace A] (n : ℕ)
    (initial : A → Configuration (n + 1) D) (a : Sample A (Label (n + 1) D)) : ℝ≥0∞ :=
  intervalSup (fun t => ENNReal.ofReal (PowerWasserstein.distance hp
    (empiricalLaw (MomentScale.realPower p hp.le) (Nat.succ_pos n)
      (ConfigurationTimeDependent.process control (Nat.succ_pos n) initial a t)) (v t))) T

/-- The actual uncountable supremum is measurable using right continuity,
not merely because it is bounded by a measurable random variable. -/
theorem aemeasurable_canonicalRunningError {A : Type*} [MeasurableSpace A]
    (n : ℕ) (initial : A → Configuration (n + 1) D)
    (μ : Measure A) [IsProbabilityMeasure μ] (hinit : Measurable initial)
    (hV : Integrable (fun a => lyapunov control (initial a)) μ) :
    AEMeasurable (canonicalRunningError hp control hActivity ν T hT hCoupling hMoment n initial)
      (law μ (Label (n + 1) D)) := by
  apply RightContinuousSupremum.aemeasurable_intervalSup_of_rightContinuous _ _ T hT
  · intro t _
    exact ((measurable_of_countable (fun a : Configuration (n + 1) D =>
      PowerWasserstein.distance hp
        (empiricalLaw (MomentScale.realPower p hp.le) (Nat.succ_pos n) a) (v t))).comp
      ((ConfigurationTimeDependent.measurable_process control (Nat.succ_pos n) initial hinit).of_uncurry_right
        (y := t))).ennreal_ofReal.aemeasurable
  · filter_upwards [CanonicalSkorokhodPaths.ae_configuration_cadlag
      control (Nat.succ_pos n) initial μ hinit hV] with a ha
    intro t ht
    have he : ContinuousWithinAt (fun s =>
        empiricalLaw (MomentScale.realPower p hp.le) (Nat.succ_pos n)
          (ConfigurationTimeDependent.process control (Nat.succ_pos n) initial a s)) (Ici t) t :=
      (continuous_of_discreteTopology : Continuous
        (empiricalLaw (MomentScale.realPower p hp.le) (Nat.succ_pos n) :
          Configuration (n + 1) D → MomentLaw (MomentScale.realPower p hp.le) D)).continuousAt.comp_continuousWithinAt
        (ha.1 t ht.1)
    have hv : ContinuousWithinAt v (Ici t) t :=
      (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment).continuousAt.continuousWithinAt
    exact continuousWithinAt_distance_ofReal hp he hv

variable {Ω : Type*} [MeasurableSpace Ω]
  (M : ∀ n, Label (n + 1) D → Ω → Measure (ℝ × ℝ))
  (z : ∀ n, Ω → Configuration (n + 1) D)

/-- Uniform ordinary Wp error of the actual supplied-PRM particle system. -/
def runningError (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  canonicalRunningError hp control hActivity ν T hT hCoupling hMoment n id
    (record (Label (n + 1) D) (M n) (z n) ω)

variable (P : Measure Ω) [IsProbabilityMeasure P]
  (hM : ∀ n j, Measurable (M n j))
  (hPoisson : ∀ n, PoissonObservationLaw.HasDisjointLaws P (Label (n + 1) D) (M n))
  (hz : ∀ n, Measurable (z n))
  (hIndependent : ∀ n, IndepFun (z n) (fun ω j => M n j ω) P)
  (hΨ : ∀ n, Integrable (fun ω => lyapunov control (z n ω)) P)

include hM hPoisson hz hIndependent hΨ

theorem aemeasurable_runningError (n : ℕ) :
    AEMeasurable (runningError hp control hActivity ν T hT hCoupling hMoment M z n) P := by
  letI : IsProbabilityMeasure (P.map (z n)) := isProbabilityMeasure_map (hz n).aemeasurable
  have hV : Integrable (lyapunov control) (P.map (z n)) :=
    integrable_initial_of_map control (P.map (z n)) P id (z n)
      measurable_id (hz n) (by simp) (hΨ n)
  exact PrescribedObservableLaws.aemeasurable_comp (Label (n + 1) D) (M n) (z n)
    P (hM n) (hPoisson n) (hz n) (hIndependent n) _
    (aemeasurable_canonicalRunningError hp control hActivity ν T hT hCoupling hMoment
      n id (P.map (z n)) measurable_id hV)

variable (hex : ∀ n, ExchangeableMatching.ExchangeableLaw (P.map (z n)))
  (C : ℝ) (hbound : ∀ n, (∫ ω, lyapunov control (z n ω) ∂P) ≤ C)
  (hconv : TendstoInMeasure P
    (fun n ω => wasserstein
      (empiricalLaw (MomentScale.realPower p hp.le) (Nat.succ_pos n) (z n ω)) ν) atTop 0)

include hex hbound hconv

/-- Remark 2.8: uniform ordinary Wp convergence on the supplied probability
space for every real p > 1, under exactly the manuscript initialization. -/
theorem measure_runningError_gt_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | ENNReal.ofReal ε <
      runningError hp control hActivity ν T hT hCoupling hMoment M z n ω}) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (PrescribedPopulationLimits.measure_runningError_gt_tendsto_zero
      control hActivity ν T hT hCoupling hMoment M z P hM hPoisson hz hIndependent hΨ
      hex C hbound hconv (ε ^ p) (Real.rpow_pos_of_pos hε p)) (fun _ => zero_le _)
  intro n
  apply measure_mono
  intro ω h
  exact intervalSup_gt_imp hp
    (fun t => empiricalLaw (MomentScale.realPower p hp.le) (Nat.succ_pos n)
      (ConfigurationTimeDependent.process control (Nat.succ_pos n) id
        (record (Label (n + 1) D) (M n) (z n) ω) t)) v T ε hε h

theorem probability_runningError_gt_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P.real {ω | ENNReal.ofReal ε <
      runningError hp control hActivity ν T hT hCoupling hMoment M z n ω}) atTop (𝓝 0) :=
  ENNReal.tendsto_toReal ENNReal.zero_ne_top |>.comp
    (measure_runningError_gt_tendsto_zero hp control hActivity ν T hT hCoupling hMoment
      M z P hM hPoisson hz hIndependent hΨ hex C hbound hconv ε hε)

end CarryingCapacity.PowerWassersteinUniform

namespace CarryingCapacity.MomentScale

/-- The real-power specialization at two is the existing quadratic scale,
so the uniform theorem applies directly after rewriting this equality. -/
theorem realPower_two_eq_quadratic : realPower 2 (by norm_num) = quadratic := by
  have h : (fun n : ℕ => (n : ℝ) ^ (2 : ℝ)) = (fun n : ℕ => (n : ℝ) ^ (2 : ℕ)) := by
    funext n
    exact Real.rpow_two (n : ℝ)
  unfold realPower quadratic
  congr 1

/-- The real-power endpoint one is exactly the established linear scale. -/
theorem realPower_one_eq_linear : realPower 1 le_rfl = linear := by
  have h : (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) = (fun n : ℕ => (n : ℝ)) := by
    funext n
    exact Real.rpow_one (n : ℝ)
  unfold realPower linear
  congr 1

end CarryingCapacity.MomentScale

namespace CarryingCapacity.PowerWassersteinUniform

/-- For p = 1 the genuine infimum of ordinary l1 coupling costs is precisely
the linear adapted transport distance already covered by the uniform limit. -/
theorem linear_costInf_eq {D : ℕ} (μ ν : MomentLaw MomentScale.linear D) :
    sInf (Set.range (fun c : Coupling μ ν =>
      ∫ z, PowerWasserstein.groundCost 1 z.1 z.2 ∂c.measure)) = wasserstein μ ν := by
  simp only [PowerWasserstein.groundCost, Real.rpow_one]
  rfl

end CarryingCapacity.PowerWassersteinUniform
