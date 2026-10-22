import CarryingCapacity.PrescribedConfigurationProcess
import CarryingCapacity.TimeDependentGlobalMoment
import CarryingCapacity.GlobalLyapunovExit
import CarryingCapacity.NonlinearActivityBound
import CarryingCapacity.PopulationCouplingAlgebra
import CarryingCapacity.RightContinuousSupremum

/-!
# Actual empirical activity, global moments, and maximal tails

The empirical feedback itself gives the activity bound before the genuine
configuration exit. Global Lyapunov integrability and the running-supremum tail
are derived for the constructed process on the supplied Poisson space. The
constants depend on the model and the horizon, and not on population size or
the initial law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal NNReal BigOperators

namespace CarryingCapacity.ConfigurationGlobalEstimates
open ConfigurationLocalization
variable {A : Type*} [MeasurableSpace A] {N D : ℕ}
  {κ : MomentScale} {q : Rates D (MomentLaw κ D)} (control : LyapunovControl κ q)
  (hN : 0 < N) (initial : A → Configuration N D)
  (μ : Measure A) [IsProbabilityMeasure μ] (hinit : Measurable initial)
  (hV : Integrable (fun a => lyapunov control (initial a)) μ)
include hinit hV

theorem integrable (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun p => lyapunov control (ConfigurationTimeDependent.process control hN initial p t))
      (CommonInitialNoise.law μ (Label N D)) :=
  TimeDependentGlobalMoment.integrable (lyapunov control) (finite_sublevel control hN)
    jump (ConfigurationTimeDependent.timeRate κ q hN)
    (ConfigurationTimeDependent.uniform_rate_bounds control hN) initial 0 μ
    (ConfigurationTimeDependent.measurable_timeRate hN) hinit (2 * driftConstant control)
    (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
    (lyapunov_nonnegative control)
    (fun z j s _ => ConfigurationTimeDependent.timeRate_nonnegative hN j s z) hV
    (fun z s _ => ConfigurationTimeDependent.generator_affine_bound control hN z s) t ht

theorem expectation_le (t : ℝ) (ht : 0 ≤ t) :
    (∫ p, lyapunov control (ConfigurationTimeDependent.process control hN initial p t)
      ∂CommonInitialNoise.law μ (Label N D)) ≤
      (1 + ∫ a, lyapunov control (initial a) ∂μ) * Real.exp ((2 * driftConstant control) * t) - 1 :=
  TimeDependentGlobalMoment.expectation_le (lyapunov control) (finite_sublevel control hN)
    jump (ConfigurationTimeDependent.timeRate κ q hN)
    (ConfigurationTimeDependent.uniform_rate_bounds control hN) initial 0 μ
    (ConfigurationTimeDependent.measurable_timeRate hN) hinit (2 * driftConstant control)
    (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
    (lyapunov_nonnegative control)
    (fun z j s _ => ConfigurationTimeDependent.timeRate_nonnegative hN j s z) hV
    (fun z s _ => ConfigurationTimeDependent.generator_affine_bound control hN z s) t ht

theorem crossing_probability_le (T : ℝ) (hT : 0 ≤ T) (R : ℝ) (hR : 0 < R) :
    (CommonInitialNoise.law μ (Label N D))
      (GlobalLyapunovExit.crossingEvent (lyapunov control)
        (ConfigurationTimeDependent.process control hN initial) R T) ≤
      ENNReal.ofReal (2 * ((1 + ∫ a, lyapunov control (initial a) ∂μ) *
        Real.exp ((2 * driftConstant control) * T)) / R) :=
  GlobalLyapunovExit.measure_crossing_le (lyapunov control) (finite_sublevel control hN)
    jump (ConfigurationTimeDependent.timeRate κ q hN)
    (ConfigurationTimeDependent.uniform_rate_bounds control hN) initial 0 μ
    (ConfigurationTimeDependent.measurable_timeRate hN) hinit (2 * driftConstant control)
    (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
    (lyapunov_nonnegative control)
    (fun z j s _ => ConfigurationTimeDependent.timeRate_nonnegative hN j s z) hV
    (fun z s _ => ConfigurationTimeDependent.generator_affine_bound control hN z s) R T hR hT

end CarryingCapacity.ConfigurationGlobalEstimates

namespace CarryingCapacity.PrescribedConfigurationEstimates
open ConfigurationLocalization PrescribedPoissonRealization

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N) (initial : A → Configuration N D)
  (M : Label N D → Ω → Measure (ℝ × ℝ)) (ξ : Ω → A)

local notation "V" => (lyapunov control : Configuration N D → ℝ)
local notation "X" => PrescribedConfigurationProcess.process control hN initial M ξ
local notation "rec" => record (Label N D) M ξ
local notation "hf" => finite_sublevel control hN
local notation "rateT" => ConfigurationTimeDependent.timeRate κ q hN
local notation "hbnd" => ConfigurationTimeDependent.uniform_rate_bounds control hN
local notation "hr" => ConfigurationTimeDependent.measurable_timeRate (κ := κ) (q := q) hN

/-- The exact exit of the global path, rather than an auxiliary frozen exit. -/
def firstExit (R : ℝ) : Ω → ℝ≥0∞ := GlobalLyapunovExit.firstExit V X R

/-- The actual supremum over every real time in the closed horizon. -/
def runningLyapunov (T : ℝ) (ω : Ω) : ℝ≥0∞ :=
  SynchronousRunningSupremum.intervalSup (fun t => ENNReal.ofReal (V (X ω t))) T

/-- A single coefficient for both inequalities of Corollary 3.6. -/
def uniformConstant (T : ℝ) : ℝ := 4 * Real.exp ((2 * driftConstant control) * T)

omit [MeasurableSpace Ω] [MeasurableSpace A] in
theorem uniformConstant_positive (T : ℝ) : 0 < uniformConstant control T := by
  unfold uniformConstant
  positivity

omit [MeasurableSpace Ω] [MeasurableSpace A] in
/-- Exact empirical integration gives the population factor `N`. -/
theorem empirical_weightedActivity_le (hActivity : MomentActivityBound κ q)
    (z : Configuration N D) :
    (∑ i, weightedActivity κ q (z i) (empiricalLaw κ hN z)) ≤
      DeterministicEnvironmentRates.activityConstant κ q hActivity * (N : ℝ) *
        (1 + moment (empiricalLaw κ hN z)) ^ 2 := by
  have hb := NonlinearActivityBound.integral_weightedActivity_le hActivity (empiricalLaw κ hN z)
  rw [integral_empiricalLaw] at hb
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hm := mul_le_mul_of_nonneg_left hb hNp.le
  dsimp [FiniteGenerator.empiricalMean] at hm
  have he : (N : ℝ) * ((N : ℝ)⁻¹ *
      ∑ i, weightedActivity κ q (z i) (empiricalLaw κ hN z)) =
      ∑ i, weightedActivity κ q (z i) (empiricalLaw κ hN z) := by
    rw [← mul_assoc,mul_inv_cancel₀ hNp.ne',one_mul]
  rw [he] at hm
  nlinarith

omit [MeasurableSpace Ω] [MeasurableSpace A] in
/-- Lemma 3.5 for the actual empirical feedback before its genuine global
exit. This deterministic implication holds on every sample. -/
theorem weightedActivity_le_before_exit (hActivity : MomentActivityBound κ q)
    (R : ℝ) (ω : Ω) (t : ℝ) (ht : 0 ≤ t)
    (hbefore : ENNReal.ofReal t < firstExit control hN initial M ξ R ω) :
    (∑ i, weightedActivity κ q (X ω t i) (empiricalLaw κ hN (X ω t))) ≤
      DeterministicEnvironmentRates.activityConstant κ q hActivity * (N : ℝ) * (1 + R)^2 := by
  have hactive : V (X ω t) < R :=
    CommonFrozenExit.mem_before_exit {z | V z < R} (X ω) ht hbefore
  have hmoment := PopulationCouplingAlgebra.moment_empirical_le_lyapunov κ q control hN (X ω t)
  apply (empirical_weightedActivity_le hN hActivity (X ω t)).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg
    (DeterministicEnvironmentRates.activityConstant_nonnegative κ q hActivity) (Nat.cast_nonneg N))
  apply pow_le_pow_left₀ (by linarith [moment_nonneg (empiricalLaw κ hN (X ω t))])
  · linarith

omit [MeasurableSpace Ω] [MeasurableSpace A] in
/-- The same stopped bound controls the ordinary total jump rate. -/
theorem totalRate_le_before_exit (hActivity : MomentActivityBound κ q)
    (R : ℝ) (ω : Ω) (t : ℝ) (ht : 0 ≤ t)
    (hbefore : ENNReal.ofReal t < firstExit control hN initial M ξ R ω) :
    (∑ i, q.totalRate (X ω t i) (empiricalLaw κ hN (X ω t))) ≤
      DeterministicEnvironmentRates.activityConstant κ q hActivity * (N : ℝ) * (1 + R)^2 :=
  (Finset.sum_le_sum (fun i _ => totalRate_le_weightedActivity κ q (X ω t i)
    (empiricalLaw κ hN (X ω t)))).trans
      (weightedActivity_le_before_exit control hN initial M ξ hActivity R ω t ht hbefore)

attribute [local irreducible] PrescribedPoissonRealization.record

variable (hinit : Measurable initial) (hM : ∀ j, Measurable (M j)) (hξ : Measurable ξ)
  (P : Measure Ω) [IsProbabilityMeasure P]
  (hPoisson : PoissonObservationLaw.HasDisjointLaws P (Label N D) M)
  (hIndependent : IndepFun ξ (fun ω j => M j ω) P)
  (hV : Integrable (fun a => lyapunov control (initial a)) (P.map ξ))
include hinit hM hξ hPoisson hIndependent hV

/-- The global empirical Lyapunov moment is genuinely integrable. -/
theorem integrable_lyapunov (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω => V (X ω t)) P := by
  unfold PrescribedConfigurationProcess.process
  letI : IsProbabilityMeasure (P.map ξ) := isProbabilityMeasure_map hξ.aemeasurable
  have hc := ConfigurationGlobalEstimates.integrable control hN initial (P.map ξ) hinit hV t ht
  have hp := measurePreserving_record (Label N D) M ξ P hM hPoisson hξ hIndependent
  exact (hp.integrable_comp hc.aestronglyMeasurable).mpr hc

/-- The global process retains the affine exponential moment bound. -/
theorem expectation_le (t : ℝ) (ht : 0 ≤ t) :
    (∫ ω, V (X ω t) ∂P) ≤
      (1 + ∫ a, V (initial a) ∂P.map ξ) * Real.exp ((2 * driftConstant control) * t) - 1 := by
  letI : IsProbabilityMeasure (P.map ξ) := isProbabilityMeasure_map hξ.aemeasurable
  have hc := ConfigurationGlobalEstimates.integrable control hN initial (P.map ξ) hinit hV t ht
  have hp := measurePreserving_record (Label N D) M ξ P hM hPoisson hξ hIndependent
  have he := integral_map hp.measurable.aemeasurable
    (show AEStronglyMeasurable
      (fun p => V (ConfigurationTimeDependent.process control hN initial p t))
      (P.map rec) from hp.map_eq.symm ▸ hc.aestronglyMeasurable)
  rw [hp.map_eq] at he
  unfold PrescribedConfigurationProcess.process
  exact he.symm.trans_le (ConfigurationGlobalEstimates.expectation_le control hN initial
    (P.map ξ) hinit hV t ht)

/-- A horizon-uniform bound with no dependence on population size. -/
theorem expectation_le_on_horizon (T : ℝ) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    (∫ ω, V (X ω t) ∂P) ≤
      uniformConstant control T * (1 + ∫ a, V (initial a) ∂P.map ξ) := by
  have hm : 0 ≤ ∫ a, V (initial a) ∂P.map ξ := integral_nonneg (fun a => lyapunov_nonnegative control (initial a))
  have he : Real.exp ((2 * driftConstant control) * t) ≤
      Real.exp ((2 * driftConstant control) * T) := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left htT (mul_nonneg (by norm_num) (driftConstant_nonnegative control)))
  have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ 1 + ∫ a, V (initial a) ∂P.map ξ by linarith)
  have hb := expectation_le control hN initial M ξ hinit hM hξ P hPoisson hIndependent hV t ht
  unfold uniformConstant
  nlinarith [Real.exp_pos ((2 * driftConstant control) * T)]

/-- A genuine all-real-time crossing bound, obtained from the actual frozen
construction and its proved stopped moments. -/
theorem crossing_probability_le (T : ℝ) (hT : 0 ≤ T) (R : ℝ) (hR : 0 < R) :
    P (GlobalLyapunovExit.crossingEvent V X R T) ≤
      ENNReal.ofReal (2 * ((1 + ∫ a, V (initial a) ∂P.map ξ) *
        Real.exp ((2 * driftConstant control) * T)) / R) := by
  letI : IsProbabilityMeasure (P.map ξ) := isProbabilityMeasure_map hξ.aemeasurable
  have hm := Measure.le_map_apply (μ := P) (measurable_record (Label N D) M ξ hM hξ).aemeasurable
    (GlobalLyapunovExit.crossingEvent V (ConfigurationTimeDependent.process control hN initial) R T)
  rw [record_map (Label N D) M ξ P hM hPoisson hξ hIndependent] at hm
  change P (rec ⁻¹' GlobalLyapunovExit.crossingEvent V
    (ConfigurationTimeDependent.process control hN initial) R T) ≤ _
  exact hm.trans (ConfigurationGlobalEstimates.crossing_probability_le control hN initial
    (P.map ξ) hinit hV T hT R hR)

section SupremumMeasurability
attribute [local irreducible] PrescribedConfigurationProcess.process

/-- AE measurability of the actual full-time supremum. -/
theorem aemeasurable_runningLyapunov (T : ℝ) (hT : 0 ≤ T) :
    AEMeasurable (runningLyapunov control hN initial M ξ T) P := by
  letI : IsProbabilityMeasure (P.map ξ) := isProbabilityMeasure_map hξ.aemeasurable
  apply RightContinuousSupremum.aemeasurable_intervalSup_of_rightContinuous P _ T hT
  · intro t _
    have hm := (PrescribedConfigurationProcess.measurable_process control hN initial M ξ hinit hM hξ).comp
      (measurable_id.prodMk measurable_const : Measurable (fun ω : Ω => (ω,t)))
    have hx : Measurable (fun ω => X ω t) := by simpa only [Function.comp_def] using hm
    exact ((measurable_of_countable V).comp hx).ennreal_ofReal.aemeasurable
  · filter_upwards [PrescribedConfigurationProcess.ae_cadlag control hN initial M ξ hinit hM hξ P
      hPoisson hIndependent (P.map ξ) rfl hV] with ω hω
    intro t ht
    have hc : Continuous V := continuous_of_discreteTopology
    exact ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
      (hc.continuousAt.comp_continuousWithinAt (hω.1 t ht.1))

end SupremumMeasurability

/-- Corollary 3.6 at the exact closed running-supremum event, with the same
population-independent constant as the moment bound. -/
theorem measure_runningLyapunov_ge_le (T : ℝ) (hT : 0 ≤ T) (R : ℝ) (hR : 0 < R) :
    P {ω | ENNReal.ofReal R ≤ runningLyapunov control hN initial M ξ T ω} ≤
      ENNReal.ofReal (uniformConstant control T * (1 + ∫ a, V (initial a) ∂P.map ξ) / R) := by
  have hsub : {ω | ENNReal.ofReal R ≤ runningLyapunov control hN initial M ξ T ω} ⊆
      GlobalLyapunovExit.crossingEvent V X (R / 2) T := by
    intro ω hω
    have hh : ENNReal.ofReal (R / 2) <
        SynchronousRunningSupremum.intervalSup (fun t => ENNReal.ofReal (V (X ω t))) T :=
      (ENNReal.ofReal_lt_ofReal_iff hR).mpr (by linarith) |>.trans_le hω
    obtain ⟨t,ht⟩ := (lt_iSup_iff).mp hh
    refine ⟨t,t.property,le_of_lt ?_⟩
    by_contra hn
    exact (not_lt_of_ge (ENNReal.ofReal_le_ofReal (le_of_not_gt hn))) ht
  refine (measure_mono hsub).trans ?_
  have hb := crossing_probability_le control hN initial M ξ hinit hM hξ P hPoisson hIndependent hV
    T hT (R / 2) (by linarith)
  convert hb using 1
  congr 1
  unfold uniformConstant
  ring

end CarryingCapacity.PrescribedConfigurationEstimates

namespace CarryingCapacity.PrescribedConfigurationUniformEstimates
open ConfigurationLocalization PrescribedConfigurationEstimates

variable {Ω : Type*} [MeasurableSpace Ω]
  {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q)
  (M : (n : ℕ) → Label (n + 1) D → Ω → Measure (ℝ × ℝ))
  (ξ : (n : ℕ) → Ω → Configuration (n + 1) D)

/-- The family indexes every positive population size, `N = n + 1`. -/
def process (n : ℕ) : Ω → ℝ → Configuration (n + 1) D :=
  PrescribedConfigurationProcess.process control (Nat.succ_pos n) id (M n) (ξ n)

variable (hM : ∀ n j, Measurable (M n j)) (hξ : ∀ n, Measurable (ξ n))
  (P : Measure Ω) [IsProbabilityMeasure P]
  (hPoisson : ∀ n, PoissonObservationLaw.HasDisjointLaws P (Label (n + 1) D) (M n))
  (hIndependent : ∀ n, IndepFun (ξ n) (fun ω j => M n j ω) P)
  (hV : ∀ n, Integrable (lyapunov control : Configuration (n + 1) D → ℝ) (P.map (ξ n)))
include hM hξ hPoisson hIndependent hV

omit hV in
/-- The random initial vector and the actual constructed process have exactly
the same initial Lyapunov expectation. -/
theorem initial_expectation_eq (n : ℕ) :
    (∫ ω, lyapunov control (process control M ξ n ω 0) ∂P) =
      ∫ a, lyapunov control a ∂P.map (ξ n) := by
  have he := PrescribedConfigurationProcess.ae_initial control (Nat.succ_pos n) id (M n) (ξ n)
    (hM n) (hξ n) P (hPoisson n) (hIndependent n) (P.map (ξ n)) rfl
  calc
    _ = ∫ ω, lyapunov control (ξ n ω) ∂P := integral_congr_ae (he.mono (fun _ hh => congrArg _ hh))
    _ = _ := (integral_map_of_stronglyMeasurable (hξ n)
      (measurable_of_countable (lyapunov control : Configuration (n + 1) D → ℝ)).stronglyMeasurable).symm

/-- Corollary 3.6, first display: actual expectations are bounded uniformly in
all positive population sizes and every real time in the closed horizon. -/
theorem sup_expectation_le
    (hBound : BddAbove (Set.range (fun n =>
      ∫ ω, lyapunov control (process control M ξ n ω 0) ∂P)))
    (T : ℝ) (hT : 0 ≤ T) :
    (⨆ n : ℕ, ⨆ t : Icc (0 : ℝ) T,
      ∫ ω, lyapunov control (process control M ξ n ω t) ∂P) ≤
      uniformConstant control T *
        (1 + ⨆ n : ℕ, ∫ ω, lyapunov control (process control M ξ n ω 0) ∂P) := by
  letI : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0,le_rfl,hT⟩⟩
  apply ciSup_le
  intro n
  apply ciSup_le
  intro t
  have hb := expectation_le_on_horizon control (Nat.succ_pos n) id (M n) (ξ n)
    measurable_id (hM n) (hξ n) P (hPoisson n) (hIndependent n) (hV n) T t.property.1 t.property.2
  change (∫ ω, lyapunov control (process control M ξ n ω t) ∂P) ≤
    uniformConstant control T * (1 + ∫ a, lyapunov control a ∂P.map (ξ n)) at hb
  rw [← initial_expectation_eq control M ξ hM hξ P hPoisson hIndependent n] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (add_le_add_left (le_ciSup hBound n) 1)
    (uniformConstant_positive control T).le)

/-- Corollary 3.6, second display: the true closed running-supremum event,
uniformly over all positive population sizes, with exactly reciprocal scaling. -/
theorem sup_runningLyapunov_probability_le
    (hBound : BddAbove (Set.range (fun n =>
      ∫ ω, lyapunov control (process control M ξ n ω 0) ∂P)))
    (T : ℝ) (hT : 0 ≤ T) (R : ℝ) (hR : 0 < R) :
    (⨆ n : ℕ, P {ω | ENNReal.ofReal R ≤
      runningLyapunov control (Nat.succ_pos n) id (M n) (ξ n) T ω}) ≤
      ENNReal.ofReal (uniformConstant control T *
        (1 + ⨆ n : ℕ, ∫ ω, lyapunov control (process control M ξ n ω 0) ∂P) / R) := by
  apply iSup_le
  intro n
  have hb := measure_runningLyapunov_ge_le control (Nat.succ_pos n) id (M n) (ξ n)
    measurable_id (hM n) (hξ n) P (hPoisson n) (hIndependent n) (hV n) T hT R hR
  change P {ω | ENNReal.ofReal R ≤
      runningLyapunov control (Nat.succ_pos n) id (M n) (ξ n) T ω} ≤
    ENNReal.ofReal (uniformConstant control T * (1 + ∫ a, lyapunov control a ∂P.map (ξ n)) / R) at hb
  rw [← initial_expectation_eq control M ξ hM hξ P hPoisson hIndependent n] at hb
  refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add_left (le_ciSup hBound n) 1)
      (uniformConstant_positive control T).le) hR.le

end CarryingCapacity.PrescribedConfigurationUniformEstimates
