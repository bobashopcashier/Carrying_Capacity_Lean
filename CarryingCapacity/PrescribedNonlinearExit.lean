import CarryingCapacity.PrescribedDeterministicEnvironment
import CarryingCapacity.PrescribedNonlinearProcess
import CarryingCapacity.RightContinuousSupremum

/-!
# Whole-horizon Lyapunov tails for the supplied nonlinear process

The process is the single all-time solution on the specified Poisson space.
Its exact running supremum is AE measurable. The finite-horizon frozen-exit
estimate gives the `C_T (1 + ν(Ψ)) / R` tail in Corollary 4.4; no moment or
maximal inequality for the resulting process is supplied as an assumption.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal NNReal BigOperators

namespace CarryingCapacity.PrescribedNonlinearExit
open PrescribedPoissonRealization DeterministicEnvironmentLyapunov LyapunovFlowSpace

variable {Ω : Type*} [MeasurableSpace Ω]
  {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)
  (M : Jump D → Ω → Measure (ℝ × ℝ)) (ξ : Ω → State D)

local notation "X" => PrescribedNonlinearProcess.process control hActivity ν hCoupling hMoment M ξ
local notation "rec" => record (Jump D) M ξ

/-- The supremum over all real times in `[0,T]`, including both endpoints. -/
def runningLyapunov (T : ℝ) (ω : Ω) : ℝ≥0∞ :=
  SynchronousRunningSupremum.intervalSup (fun t => ENNReal.ofReal (control.function (X ω t))) T

/-- An explicit finite constant for the closed running-supremum tail. -/
def exitConstant (T : ℝ) : ℝ :=
  4 * Real.exp (2 * driftConstant control * T)

omit [MeasurableSpace Ω] in
theorem exitConstant_positive (T : ℝ) : 0 < exitConstant control T := by
  unfold exitConstant
  positivity

omit [MeasurableSpace Ω] in
/-- The sharp canonical maximal bound uses the actual frozen expectation
envelope, so its coefficient is independent of the initial law. -/
theorem canonical_crossing_probability_le (T : ℝ) (hT : 0 ≤ T) (R : ℝ) (hR : 0 < R) :
    (CommonInitialNoise.law ν.measure (Jump D))
      (GlobalLyapunovExit.crossingEvent control.function
        (NonlinearFixedPoint.process control hActivity ν T hT hCoupling hMoment) R T) ≤
      ENNReal.ofReal (2 * ((1 + ∫ x, control.function x ∂ν.measure) *
        Real.exp (2 * driftConstant control * T)) / R) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  let v := NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment
  have hv : ContinuousOn v (Icc 0 T) :=
    (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment).continuousOn
  let rate := DeterministicEnvironmentFrozen.timeRate κ q v T
  let hf := finite_sublevels control
  let hb := exists_uniform_rate_bounds control v T hT hActivity hv
  let m := ∫ x, control.function x ∂ν.measure
  let K := LyapunovFlowSpace.exponentialEnvelope m (driftConstant control)
  let Q := (1 + m) * Real.exp (2 * driftConstant control * T)
  have hm : 0 ≤ m := integral_nonneg (function_nonnegative control)
  have hK0 : ∀ s ∈ Icc 0 T, 0 ≤ K s := by
    intro s hs
    exact hm.trans (le_exponentialEnvelope hm (driftConstant_nonnegative control) hs.1)
  have hRate : ∀ j x, Measurable (fun s => rate j s x) :=
    DeterministicEnvironmentFrozen.measurable_timeRate κ q v T hv hCoupling hT
  have hlocal (n : ℕ) :
      (∫ p, control.function (TimeDependentLocalization.path control.function hf
        Jump.advance rate hb id n p T) ∂CommonInitialNoise.law ν.measure (Jump D)) ≤ K T := by
    apply TimeDependentLyapunovComparison.expectation_le_manuscript_envelope
      (LyapunovLocalization.active control.function hf n) Jump.advance rate id ν.measure
      hRate measurable_id (TimeDependentLocalization.rateBound control.function hf rate hb n)
      0 control.function (driftConstant control) (driftConstant_nonnegative control) K T hT
      (function_nonnegative control)
      (fun x _ j s _ => DeterministicEnvironmentFrozen.timeRate_nonnegative κ q v T j s x)
      (fun x hx j s _ => TimeDependentLocalization.rate_le_bound control.function hf rate hb n x hx j s)
      hMoment K.continuous.continuousOn hK0
    · intro s hs x hx
      simpa only [TimeDependentGeneratorIntegral.frozenGenerator,
        FrozenProcess.frozenGenerator, if_pos hx] using
        manuscript_generator_envelope_bound control ν (driftConstant control) T
          (driftConstant_nonnegative control) hT
          (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hMoment) s hs x
    · intro s hs
      exact (DeterministicEnvironmentEnvelope.exponentialEnvelope_integral_eq m
        (driftConstant control) s hs.1).le
    · exact ⟨hT,le_rfl⟩
  have hQ : 1 ≤ Q := by
    have he : 1 ≤ Real.exp (2 * driftConstant control * T) :=
      Real.one_le_exp_iff.mpr (mul_nonneg (mul_nonneg (by norm_num) (driftConstant_nonnegative control)) hT)
    exact (show (1 : ℝ) ≤ (1 + m) * 1 by linarith).trans
      (mul_le_mul_of_nonneg_left he (by linarith))
  have hKQ : K T ≤ Q := by
    change (m + 1 / 2) * Real.exp (2 * driftConstant control * T) - 1 / 2 ≤ _
    dsimp [Q]
    nlinarith [Real.exp_pos (2 * driftConstant control * T)]
  by_cases hlarge : 2 ≤ R
  · let n := Nat.floor (R / 2)
    have hnlow : R / 2 < (n : ℝ) + 1 := Nat.lt_floor_add_one (R / 2)
    have hnupper : (n : ℝ) + 1 ≤ R := by
      have hf' : (n : ℝ) ≤ R / 2 := Nat.floor_le (by positivity)
      linarith
    have hnpos : 0 < (n : ℝ) + 1 := by positivity
    have hi := TimeDependentDynkin.integrable_testFunction
      (LyapunovLocalization.active control.function hf n) Jump.advance rate id ν.measure hRate
      measurable_id (TimeDependentLocalization.rateBound control.function hf rate hb n)
      0 control.function T hMoment
    have hexit := TimeDependentInitialExit.measure_firstExit_le_of_expectation_le ν.measure
      (LyapunovLocalization.active control.function hf n) Jump.advance rate id control.function
      (function_nonnegative control) ((n+1 : ℕ) : ℝ)
      (TimeDependentLocalization.rateBound control.function hf rate hb n) T (K T)
      (by positivity) hT
      (fun x => by simpa only [Nat.cast_add,Nat.cast_one] using
        LyapunovLocalization.mem_active control.function hf n x) hi (hlocal n)
    have hbound := (GlobalLyapunovExit.measure_crossing_le_exit control.function hf
      Jump.advance rate hb id 0 ν.measure n R T hnupper).trans hexit
    have hcast : ENNReal.ofReal ((n+1 : ℕ) : ℝ) = ENNReal.ofReal ((n : ℝ)+1) := by norm_cast
    rw [hcast,← ENNReal.ofReal_div_of_pos hnpos] at hbound
    refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
    have hh : K T / ((n : ℝ)+1) ≤ Q / (R/2) :=
      (div_le_div_of_nonneg_left (hK0 T ⟨hT,le_rfl⟩) (by positivity) hnlow.le).trans
        (div_le_div_of_nonneg_right hKQ (by positivity))
    convert hh using 1
    dsimp [Q]
    ring
  · have hp := measure_mono (μ := CommonInitialNoise.law ν.measure (Jump D))
      (subset_univ (GlobalLyapunovExit.crossingEvent control.function
        (NonlinearFixedPoint.process control hActivity ν T hT hCoupling hMoment) R T))
    rw [measure_univ] at hp
    refine hp.trans (ENNReal.one_le_ofReal.mpr ?_)
    apply (le_div_iff₀ hR).mpr
    change 1 * R ≤ 2 * Q
    linarith

variable (hM : ∀ j, Measurable (M j)) (hξ : Measurable ξ)
  (P : Measure Ω) [IsProbabilityMeasure P]
  (hPoisson : PoissonObservationLaw.HasDisjointLaws P (Jump D) M)
  (hIndependent : IndepFun ξ (fun ω j => M j ω) P)
  (hLaw : P.map ξ = ν.measure)
include hM hξ hPoisson hIndependent hLaw

/-- Finite-horizon agreement is on one event for the entire interval. -/
theorem ae_process_eq_environment (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, EqOn (X ω)
      (PrescribedDeterministicEnvironment.process control hActivity
        (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment)
        T hT (NonlinearFixedPoint.continuous_environment control hActivity ν T hT
          hCoupling hMoment).continuousOn M ξ ω) (Icc 0 T) := by
  have hc := NonlinearGlobalProcess.ae_process_eq_horizon control hActivity ν hCoupling hMoment T hT
  rw [← hLaw] at hc
  exact ae_record (Jump D) M ξ P hM hPoisson hξ hIndependent hc

section SupremumMeasurability
attribute [local irreducible] PrescribedNonlinearProcess.process

/-- AE measurability concerns the actual all-real supremum, not a substitute
chosen only at rational times. -/
theorem aemeasurable_runningLyapunov (T : ℝ) (hT : 0 ≤ T) :
    AEMeasurable (runningLyapunov control hActivity ν hCoupling hMoment M ξ T) P := by
  apply RightContinuousSupremum.aemeasurable_intervalSup_of_rightContinuous P _ T hT
  · intro t _
    have hp : Measurable (fun ω : Ω => (ω,t)) := measurable_id.prodMk measurable_const
    have hm := (PrescribedNonlinearProcess.measurable_process control hActivity ν hCoupling
      hMoment M ξ hM hξ).comp hp
    have hx : Measurable (fun ω => X ω t) := by simpa only [Function.comp_def] using hm
    exact ((measurable_of_countable control.function).comp hx).ennreal_ofReal.aemeasurable
  · filter_upwards [PrescribedNonlinearProcess.ae_cadlag control hActivity ν hCoupling
      hMoment M ξ hM hξ P hPoisson hIndependent hLaw] with ω hω
    intro t ht
    have hc : Continuous control.function := continuous_of_discreteTopology
    exact ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
      (hc.continuousAt.comp_continuousWithinAt (hω.1 t ht.1))

end SupremumMeasurability

/-- A genuine whole-horizon crossing bound for the all-time nonlinear solution. -/
theorem crossing_probability_le_affine (T : ℝ) (hT : 0 ≤ T) (R : ℝ) (hR : 0 < R) :
    P (GlobalLyapunovExit.crossingEvent control.function X R T) ≤
      ENNReal.ofReal (2 * ((1 + ∫ x, control.function x ∂ν.measure) *
        Real.exp (affineConstant control
          (manuscriptBound control ν (driftConstant control) T) * T)) / R) := by
  let v := NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment
  have hv : ContinuousOn v (Icc 0 T) :=
    (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment).continuousOn
  let B := manuscriptBound control ν (driftConstant control) T
  have hB : 0 ≤ B := manuscriptBound_nonnegative control ν (driftConstant control) T
    (driftConstant_nonnegative control) hT
  have hEnv : ∀ s ∈ Icc 0 T,
      LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B := by
    intro s _
    exact manuscriptExtension_bound control ν (driftConstant control) T
      (driftConstant_nonnegative control) hT
      (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hMoment) s
  have he : GlobalLyapunovExit.crossingEvent control.function X R T =ᵐ[P]
      GlobalLyapunovExit.crossingEvent control.function
        (PrescribedDeterministicEnvironment.process control hActivity v T hT hv M ξ) R T := by
    filter_upwards [ae_process_eq_environment control hActivity ν hCoupling hMoment
      M ξ hM hξ P hPoisson hIndependent hLaw T hT] with ω hω
    apply propext
    change (∃ t ∈ Icc 0 T, R ≤ control.function (X ω t)) ↔ _
    constructor
    · rintro ⟨t,ht,hr⟩
      exact ⟨t,ht,(hω ht) ▸ hr⟩
    · rintro ⟨t,ht,hr⟩
      exact ⟨t,ht,(hω ht).symm ▸ hr⟩
  rw [measure_congr he]
  exact PrescribedDeterministicEnvironment.crossing_probability_le control hActivity v T hT hv
    M ξ hCoupling hM hξ P hPoisson hIndependent ν hLaw B hB hEnv hMoment R T hR hT

/-- The sharper supplied-space crossing estimate has no initial-law
dependence hidden in its coefficient. -/
theorem crossing_probability_le (T : ℝ) (hT : 0 ≤ T) (R : ℝ) (hR : 0 < R) :
    P (GlobalLyapunovExit.crossingEvent control.function X R T) ≤
      ENNReal.ofReal (2 * ((1 + ∫ x, control.function x ∂ν.measure) *
        Real.exp (2 * driftConstant control * T)) / R) := by
  let A := GlobalLyapunovExit.crossingEvent control.function
    (NonlinearFixedPoint.process control hActivity ν T hT hCoupling hMoment) R T
  have he : GlobalLyapunovExit.crossingEvent control.function X R T =ᵐ[P] rec ⁻¹' A := by
    filter_upwards [ae_process_eq_environment control hActivity ν hCoupling hMoment
      M ξ hM hξ P hPoisson hIndependent hLaw T hT] with ω hω
    apply propext
    change (∃ t ∈ Icc 0 T, R ≤ control.function (X ω t)) ↔ _
    constructor
    · rintro ⟨t,ht,hr⟩
      have hh : X ω t = NonlinearFixedPoint.process control hActivity ν T hT hCoupling hMoment (rec ω) t := hω ht
      exact ⟨t,ht,hh ▸ hr⟩
    · rintro ⟨t,ht,hr⟩
      have hh : X ω t = NonlinearFixedPoint.process control hActivity ν T hT hCoupling hMoment (rec ω) t := hω ht
      exact ⟨t,ht,hh.symm ▸ hr⟩
  rw [measure_congr he]
  have hm := Measure.le_map_apply (μ := P) (measurable_record (Jump D) M ξ hM hξ).aemeasurable A
  rw [record_map (Jump D) M ξ P hM hPoisson hξ hIndependent,hLaw] at hm
  exact hm.trans (canonical_crossing_probability_le control hActivity ν hCoupling hMoment T hT R hR)

/-- Corollary 4.4: the closed threshold event for the entire running maximum.
The harmless factor four avoids an attainment assumption for the supremum. -/
theorem measure_runningLyapunov_ge_le (T : ℝ) (hT : 0 ≤ T) (R : ℝ) (hR : 0 < R) :
    P {ω | ENNReal.ofReal R ≤ runningLyapunov control hActivity ν hCoupling hMoment M ξ T ω} ≤
      ENNReal.ofReal (exitConstant control T * (1 + ∫ x, control.function x ∂ν.measure) / R) := by
  have hsub : {ω | ENNReal.ofReal R ≤
      runningLyapunov control hActivity ν hCoupling hMoment M ξ T ω} ⊆
      GlobalLyapunovExit.crossingEvent control.function X (R / 2) T := by
    intro ω hω
    have hh : ENNReal.ofReal (R / 2) <
        SynchronousRunningSupremum.intervalSup
          (fun t => ENNReal.ofReal (control.function (X ω t))) T :=
      (ENNReal.ofReal_lt_ofReal_iff hR).mpr (by linarith) |>.trans_le hω
    obtain ⟨t,ht⟩ := (lt_iSup_iff).mp hh
    refine ⟨t,t.property,le_of_lt ?_⟩
    by_contra hn
    exact (not_lt_of_ge (ENNReal.ofReal_le_ofReal (le_of_not_gt hn))) ht
  refine (measure_mono hsub).trans ?_
  have hb := crossing_probability_le control hActivity ν hCoupling hMoment M ξ hM hξ P
    hPoisson hIndependent hLaw T hT (R / 2) (by linarith)
  convert hb using 1
  congr 1
  unfold exitConstant
  ring

end CarryingCapacity.PrescribedNonlinearExit
