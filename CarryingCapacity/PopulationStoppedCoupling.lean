import CarryingCapacity.ConfigurationTimeDependent
import CarryingCapacity.DeterministicEnvironmentConfiguration
import CarryingCapacity.PopulationCouplingAlgebra
import CarryingCapacity.SynchronousStoppedRunningSupremum
import CarryingCapacity.DeterministicEnvironmentGeneralCoupling
import CarryingCapacity.StoppedPathMeasurability

/-!
# Actual stopped population comparison in a prescribed environment

The interacting configuration and the configuration driven by a prescribed
continuous environment are constructed on the same initial-record/noise space.
Their genuine joint Lyapunov exit localizes the exact averaged coupling
activity with a coefficient independent of population size. All stochastic
bounds below invoke actual nonexplosion and compensated positive increments;
no stopped comparison inequality is an input. Expectations remain extended
until a later integrability argument.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal

namespace CarryingCapacity.PopulationStoppedCoupling
open CommonInitialNoise ConfigurationLocalization PopulationCouplingAlgebra
open SynchronousCompensation SynchronousStoppedCompensation SynchronousStoppedRunningSupremum
open MarkedIntensity

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

variable {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N) (hActivity : MomentActivityBound κ q)
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))
  {A : Type*} [MeasurableSpace A] (initialX initialY : A → Configuration N D)

local notation "VX" => lyapunov control
local notation "hfin" => finite_sublevel control hN
local notation "rX" => ConfigurationTimeDependent.timeRate κ q hN
local notation "bX" => ConfigurationTimeDependent.uniform_rate_bounds control hN
local notation "rY" => DeterministicEnvironmentConfiguration.rate κ q v T
local notation "bY" => DeterministicEnvironmentConfiguration.exists_uniform_rate_bounds control hN hActivity v T hT hv
local notation "X" => ConfigurationTimeDependent.process control hN initialX
local notation "Y" => DeterministicEnvironmentConfiguration.process control hN hActivity v T hT hv initialY

/-- The actual joint region used for the population localization. -/
def jointRegion (R : ℝ) : Set (Configuration N D × Configuration N D) :=
  {z | lyapunov control z.1 + lyapunov control z.2 < R}

/-- The genuine exit of the two actual configurations. -/
def pairExit (R : ℝ) (p : Sample A (Label N D)) : ℝ≥0∞ :=
  jointExit VX hfin jump rX bX rY bY initialX initialY 0 (jointRegion control R) p

/-- The actual stopped running supremum of one paired coordinate. -/
def coordinateStoppedCost (R : ℝ) (i : Fin N) (S : ℝ) (p : Sample A (Label N D)) : ℝ≥0∞ :=
  SynchronousStoppedRunningSupremum.stoppedRunningCost VX hfin jump rX bX rY bY initialX initialY 0
    (jointRegion control R) (coordinateCost κ i) S p

/-- The population average is taken after each coordinate's running supremum. -/
def averagedStoppedCost (R S : ℝ) (p : Sample A (Label N D)) : ℝ≥0∞ :=
  ENNReal.ofReal (N : ℝ)⁻¹ * ∑ i : Fin N,
    coordinateStoppedCost control hN hActivity v T hT hv initialX initialY R i S p

/-- The independent configuration's actual empirical comparison error. -/
def empiricalError (p : Sample A (Label N D)) (s : ℝ) : ℝ :=
  wasserstein (empiricalLaw κ hN (Y p s)) (v s)

/-- The exact population average of current positive coupling activity. -/
def activity (p : Sample A (Label N D)) (s : ℝ) : ℝ :=
  meanActivity κ q (X p s) (Y p s) (empiricalLaw κ hN (X p s)) (v s)

omit [MeasurableSpace A] in
theorem empiricalError_nonnegative (p : Sample A (Label N D)) (s : ℝ) :
    0 ≤ empiricalError control hN hActivity v T hT hv initialY p s := wasserstein_nonneg _ _

omit [MeasurableSpace A] in
theorem activity_nonnegative (p : Sample A (Label N D)) (s : ℝ) :
    0 ≤ activity control hN hActivity v T hT hv initialX initialY p s :=
  meanActivity_nonnegative κ q _ _ _ _

omit [MeasurableSpace A] in
/-- Every selected coordinate receives precisely its scalar coupling activity. -/
theorem sum_currentActivity (i : Fin N) (p : Sample A (Label N D)) (s : ℝ)
    (hs : s ∈ Icc 0 T) :
    (∑ j : Label N D, currentActivity VX hfin jump rX bX rY bY initialX initialY 0
      (coordinateCost κ i) j (p,s)) =
      couplingActivity κ q (X p s i) (Y p s i) (empiricalLaw κ hN (X p s)) (v s) := by
  simp only [currentActivity]
  simp only [ConfigurationTimeDependent.timeRate_apply,
    DeterministicEnvironmentConfiguration.rate_eq_on_horizon v T _ s hs]
  exact sum_coordinate_heightActivity κ q i (X p s) (Y p s) _ _

omit [MeasurableSpace A] in
/-- Averaging actual coordinate activities introduces no factor depending on N. -/
theorem mean_currentActivity (p : Sample A (Label N D)) (s : ℝ) (hs : s ∈ Icc 0 T) :
    (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Label N D,
      currentActivity VX hfin jump rX bX rY bY initialX initialY 0 (coordinateCost κ i) j (p,s) =
      activity control hN hActivity v T hT hv initialX initialY p s := by
  simp only [sum_currentActivity control hN hActivity v T hT hv initialX initialY _ p s hs,
    activity, meanActivity]

omit [MeasurableSpace A] in
/-- Strictly before the actual exit the true joint Lyapunov bound holds.
This deterministic infimum property requires no exceptional-event premise. -/
theorem lyapunov_pair_lt_before (R : ℝ) (p : Sample A (Label N D)) (s : ℝ)
    (hs : 0 ≤ s) (hbefore : ENNReal.ofReal s < pairExit control hN hActivity v T hT hv initialX initialY R p) :
    VX (X p s) + VX (Y p s) < R :=
  CommonFrozenExit.mem_before_exit (jointRegion control R)
    (fun t => pairPath VX hfin jump rX bX rY bY initialX initialY 0 t p) hs hbefore

omit [MeasurableSpace A] in
/-- The averaged split on the actual strict pre-exit region, with genuine
prescribed-environment moments and a coefficient independent of N. -/
theorem activity_le_localized (hCoupling : MomentCouplingBound κ q)
    (B : ℝ) (hB : 0 ≤ B)
    (hEnv : ∀ s ∈ Icc 0 T,
      LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
    (R : ℝ) (p : Sample A (Label N D)) (s : ℝ) (hs : s ∈ Icc 0 T)
    (hbefore : ENNReal.ofReal s < pairExit control hN hActivity v T hT hv initialX initialY R p) :
    activity control hN hActivity v T hT hv initialX initialY p s ≤
      localizedConstant κ q hCoupling R B *
        (meanDistance κ (X p s) (Y p s) + empiricalError control hN hActivity v T hT hv initialY p s) := by
  apply meanActivity_le_localized κ q hCoupling hN (X p s) (Y p s) (v s) R B _
  · exact moment_pair_le_of_lyapunov κ q control hN _ _ R
      (lyapunov_pair_lt_before control hN hActivity v T hT hv initialX initialY R p s hs.1 hbefore).le
  · exact DeterministicEnvironmentGeneralCoupling.moment_le_of_lyapunov_bound control
      (v s) B hB (hEnv s hs)
  · exact le_rfl

omit [MeasurableSpace A] in
/-- Current activity of each label is nonnegative without localization. -/
theorem currentActivity_nonnegative (i : Fin N) (j : Label N D)
    (p : Sample A (Label N D)) (s : ℝ) :
    0 ≤ currentActivity VX hfin jump rX bX rY bY initialX initialY 0 (coordinateCost κ i) j (p,s) :=
  SynchronousPositiveIncrement.heightActivity_nonnegative _ _ _ _ _ _ _
    (ConfigurationTimeDependent.timeRate_nonnegative hN j s _)
    (DeterministicEnvironmentConfiguration.rate_nonnegative v T j s _)

/-- The exact inclusive-exit average of the actual current activities. -/
def stoppedMeanActivity (R : ℝ) (p : Sample A (Label N D)) (s : ℝ) : ℝ≥0∞ :=
  if 0 < s ∧ ENNReal.ofReal s ≤ pairExit control hN hActivity v T hT hv initialX initialY R p
  then ENNReal.ofReal (activity control hN hActivity v T hT hv initialX initialY p s) else 0

omit [MeasurableSpace A] in
/-- Finite averaging and height integration produce the true mean activity. -/
theorem mean_stoppedActivity (R : ℝ) (p : Sample A (Label N D)) (s : ℝ)
    (hs : s ∈ Icc 0 T) :
    ENNReal.ofReal (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Label N D,
      stoppedActivity VX hfin jump rX bX rY bY initialX initialY 0
        (jointRegion control R) (coordinateCost κ i) j (p,s) =
      stoppedMeanActivity control hN hActivity v T hT hv initialX initialY R p s := by
  by_cases h : 0 < s ∧ ENNReal.ofReal s ≤ pairExit control hN hActivity v T hT hv initialX initialY R p
  · simp only [stoppedActivity, stoppedMeanActivity, pairExit] at h ⊢
    simp only [h, and_self, if_pos]
    simp_rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
      currentActivity_nonnegative control hN hActivity v T hT hv initialX initialY _ j p s)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      currentActivity_nonnegative control hN hActivity v T hT hv initialX initialY i j p s))]
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg N)),
      mean_currentActivity control hN hActivity v T hT hv initialX initialY p s hs]
  · simp only [stoppedActivity, stoppedMeanActivity, pairExit] at h ⊢
    simp only [h, if_false, Finset.sum_const_zero, mul_zero]

/-- Summed actual label activity for one stopped coordinate. -/
def coordinateActivity (R : ℝ) (i : Fin N) (p : Sample A (Label N D) × ℝ) : ℝ≥0∞ :=
  ∑ j : Label N D, stoppedActivity VX hfin jump rX bX rY bY initialX initialY 0
    (jointRegion control R) (coordinateCost κ i) j p

variable (μ : Measure A) [IsProbabilityMeasure μ]
  (hCoupling : MomentCouplingBound κ q) (hinitX : Measurable initialX) (hinitY : Measurable initialY)
  (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ s ∈ Icc 0 T,
    LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
  (hInitialX : Integrable (fun a => lyapunov control (initialX a)) μ)
  (hInitialY : Integrable (fun a => lyapunov control (initialY a)) μ)
include hCoupling hinitX hinitY hB hEnv hInitialX hInitialY

/-- Actual coordinate stopped comparison from the constructed paths and their
proved exhaustive exits. No finite expected activity premise is needed. -/
theorem expected_coordinateStoppedCost_le (R : ℝ) (i : Fin N) (S : ℝ≥0) :
    (∫⁻ p, coordinateStoppedCost control hN hActivity v T hT hv initialX initialY R i S p
      ∂law μ (Label N D)) ≤
    (∫⁻ p, ENNReal.ofReal (adaptedDistance κ (initialX p.1 i) (initialY p.1 i))
      ∂law μ (Label N D)) +
      ∫⁻ s in Ioc 0 S, ∫⁻ p, ∑ j : Label N D,
        stoppedActivity VX hfin jump rX bX rY bY initialX initialY 0
          (jointRegion control R) (coordinateCost κ i) j (p,s)
        ∂law μ (Label N D) ∂positiveVolume := by
  have hx := ConfigurationTimeDependent.ae_exhaustive control hN initialX μ hinitX hInitialX
  have hy := DeterministicEnvironmentConfiguration.ae_exhaustive control hN hActivity v T hT hv initialY μ
    hCoupling hinitY B hB hEnv hInitialY
  have hh := expected_stoppedRunningCost_le_activity (A := A) (E := Configuration N D) (J := Label N D) VX hfin jump rX bX rY bY initialX initialY 0 μ
    hx hy
    (ConfigurationTimeDependent.measurable_timeRate hN)
    (DeterministicEnvironmentConfiguration.measurable_rate v T hT hv hCoupling) hinitX hinitY
    (ConfigurationTimeDependent.timeRate_nonnegative hN)
    (DeterministicEnvironmentConfiguration.rate_nonnegative v T)
    (jointRegion control R) (coordinateCost κ i) (fun x y => adaptedDistance_nonneg κ (x i) (y i)) S
  exact hh

/-- The actual stopped coordinate supremum is AE measurable. -/
theorem aemeasurable_coordinateStoppedCost (R : ℝ) (i : Fin N) (S : ℝ≥0) :
    AEMeasurable (coordinateStoppedCost control hN hActivity v T hT hv initialX initialY R i S)
      (law μ (Label N D)) :=
  aemeasurable_stoppedRunningCost VX hfin jump rX bX rY bY initialX initialY 0 μ
    (ConfigurationTimeDependent.ae_exhaustive control hN initialX μ hinitX hInitialX)
    (DeterministicEnvironmentConfiguration.ae_exhaustive control hN hActivity v T hT hv initialY μ
      hCoupling hinitY B hB hEnv hInitialY)
    (ConfigurationTimeDependent.measurable_timeRate hN)
    (DeterministicEnvironmentConfiguration.measurable_rate v T hT hv hCoupling) hinitX hinitY
    (jointRegion control R) (coordinateCost κ i) S

/-- The actual averaged running supremum has a measurable version; no finite
expectation or supremum assumption is supplied. -/
theorem aemeasurable_averagedStoppedCost (R : ℝ) (S : ℝ≥0) :
    AEMeasurable (averagedStoppedCost control hN hActivity v T hT hv initialX initialY R S)
      (law μ (Label N D)) :=
  (Finset.aemeasurable_sum Finset.univ (fun i _ =>
    aemeasurable_coordinateStoppedCost control hN hActivity v T hT hv initialX initialY μ
      hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R i S)).const_mul _

/-- Joint AE measurability of the actual stopped coordinate activity. -/
theorem aemeasurable_coordinateActivity (τ : Measure ℝ) (R : ℝ) (i : Fin N) :
    AEMeasurable (coordinateActivity control hN hActivity v T hT hv initialX initialY R i)
      ((law μ (Label N D)).prod τ) :=
  Finset.aemeasurable_sum Finset.univ (fun j _ =>
    aemeasurable_stoppedActivity VX hfin jump rX bX rY bY initialX initialY 0
      (ConfigurationTimeDependent.measurable_timeRate hN)
      (DeterministicEnvironmentConfiguration.measurable_rate v T hT hv hCoupling) hinitX hinitY μ
      (ConfigurationTimeDependent.ae_exhaustive control hN initialX μ hinitX hInitialX)
      (DeterministicEnvironmentConfiguration.ae_exhaustive control hN hActivity v T hT hv initialY μ
        hCoupling hinitY B hB hEnv hInitialY) τ (jointRegion control R) (coordinateCost κ i) j)

/-- Actual time sections have measurable versions under the original law. -/
theorem aemeasurable_coordinateActivity_at (R : ℝ) (i : Fin N) (s : ℝ) :
    AEMeasurable (fun p => coordinateActivity control hN hActivity v T hT hv initialX initialY R i (p,s))
      (law μ (Label N D)) :=
  Finset.aemeasurable_sum Finset.univ (fun j _ =>
    aemeasurable_stoppedActivity_at VX hfin jump rX bX rY bY initialX initialY 0
      (ConfigurationTimeDependent.measurable_timeRate hN)
      (DeterministicEnvironmentConfiguration.measurable_rate v T hT hv hCoupling) hinitX hinitY μ
      (ConfigurationTimeDependent.ae_exhaustive control hN initialX μ hinitX hInitialX)
      (DeterministicEnvironmentConfiguration.ae_exhaustive control hN hActivity v T hT hv initialY μ
        hCoupling hinitY B hB hEnv hInitialY) (jointRegion control R) (coordinateCost κ i) j s)

/-- The original-environment mean activity is jointly AE measurable on the
actual comparison horizon. No measurability outside that horizon is inferred. -/
theorem aemeasurable_stoppedMeanActivity (R : ℝ) (S : ℝ≥0) (hST : (S : ℝ) ≤ T) :
    AEMeasurable (fun p : Sample A (Label N D) × ℝ =>
      stoppedMeanActivity control hN hActivity v T hT hv initialX initialY R p.1 p.2)
      ((law μ (Label N D)).prod (positiveVolume.restrict (Ioc 0 S))) := by
  have h := (Finset.aemeasurable_sum Finset.univ (fun i _ =>
    aemeasurable_coordinateActivity control hN hActivity v T hT hv initialX initialY μ
      hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY
      (positiveVolume.restrict (Ioc 0 S)) R i)).const_mul (ENNReal.ofReal (N : ℝ)⁻¹)
  apply h.congr
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)] with p hp
  exact mean_stoppedActivity control hN hActivity v T hT hv initialX initialY R p.1 p.2
    ⟨hp.1.le, hp.2.trans hST⟩

/-- Tonelli and exact finite averaging identify the time-integrated mean
activity with the sum of the coordinate expected activities. -/
theorem expected_stoppedMeanActivity_eq (R : ℝ) (S : ℝ≥0) (hST : (S : ℝ) ≤ T) :
    (∫⁻ s in Ioc 0 S, ∫⁻ p,
      stoppedMeanActivity control hN hActivity v T hT hv initialX initialY R p s
      ∂law μ (Label N D) ∂positiveVolume) =
    ENNReal.ofReal (N : ℝ)⁻¹ * ∑ i : Fin N, ∫⁻ s in Ioc 0 S, ∫⁻ p,
      coordinateActivity control hN hActivity v T hT hv initialX initialY R i (p,s)
      ∂law μ (Label N D) ∂positiveVolume := by
  calc
    _ = ∫⁻ s in Ioc 0 S, ENNReal.ofReal (N : ℝ)⁻¹ * ∑ i : Fin N, ∫⁻ p,
        coordinateActivity control hN hActivity v T hT hv initialX initialY R i (p,s)
        ∂law μ (Label N D) ∂positiveVolume := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have he : (fun p => stoppedMeanActivity control hN hActivity v T hT hv initialX initialY R p s) =
          (fun p => ENNReal.ofReal (N : ℝ)⁻¹ * ∑ i : Fin N,
            coordinateActivity control hN hActivity v T hT hv initialX initialY R i (p,s)) := by
        funext p
        exact (mean_stoppedActivity control hN hActivity v T hT hv initialX initialY R p s
          ⟨hs.1.le, hs.2.trans hST⟩).symm
      rw [he, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_finset_sum' Finset.univ (fun i _ => aemeasurable_coordinateActivity_at
          control hN hActivity v T hT hv initialX initialY μ hCoupling hinitX hinitY
          B hB hEnv hInitialX hInitialY R i s)]
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_finset_sum' Finset.univ (fun i _ =>
          (aemeasurable_coordinateActivity control hN hActivity v T hT hv initialX initialY μ
            hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY
            (positiveVolume.restrict (Ioc 0 S)) R i).lintegral_prod_left')]

/-- The actual averaged stopped comparison, in extended expectation form.
It follows from compensated increments, not a supplied population bound. -/
theorem expected_averagedStoppedCost_le (R : ℝ) (S : ℝ≥0) (hST : (S : ℝ) ≤ T) :
    (∫⁻ p, averagedStoppedCost control hN hActivity v T hT hv initialX initialY R S p
      ∂law μ (Label N D)) ≤
    (∫⁻ p, ENNReal.ofReal (meanDistance κ (initialX p.1) (initialY p.1))
      ∂law μ (Label N D)) +
      ∫⁻ s in Ioc 0 S, ∫⁻ p,
        stoppedMeanActivity control hN hActivity v T hT hv initialX initialY R p s
        ∂law μ (Label N D) ∂positiveVolume := by
  have hinit (i : Fin N) : Measurable (fun p : Sample A (Label N D) =>
      ENNReal.ofReal (adaptedDistance κ (initialX p.1 i) (initialY p.1 i))) :=
    ((measurable_of_countable (fun z : Configuration N D × Configuration N D =>
      adaptedDistance κ (z.1 i) (z.2 i))).comp
      ((hinitX.comp measurable_fst).prodMk (hinitY.comp measurable_fst))).ennreal_ofReal
  have hinitEq : (∫⁻ p, ENNReal.ofReal (meanDistance κ (initialX p.1) (initialY p.1)) ∂law μ (Label N D)) =
      ENNReal.ofReal (N : ℝ)⁻¹ * ∑ i : Fin N, ∫⁻ p,
        ENNReal.ofReal (adaptedDistance κ (initialX p.1 i) (initialY p.1 i)) ∂law μ (Label N D) := by
    simp only [meanDistance, ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg N)),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => adaptedDistance_nonneg κ (initialX _ i) (initialY _ i))]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_finset_sum Finset.univ (fun i _ => hinit i)]
  rw [hinitEq, expected_stoppedMeanActivity_eq control hN hActivity v T hT hv initialX initialY μ
    hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R S hST]
  change (∫⁻ p, ENNReal.ofReal (N : ℝ)⁻¹ * ∑ i : Fin N,
    coordinateStoppedCost control hN hActivity v T hT hv initialX initialY R i S p ∂law μ (Label N D)) ≤ _
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_finset_sum' Finset.univ (fun i _ => aemeasurable_coordinateStoppedCost
      control hN hActivity v T hT hv initialX initialY μ hCoupling hinitX hinitY
      B hB hEnv hInitialX hInitialY R i S), ← mul_add, ← Finset.sum_add_distrib]
  exact mul_le_mul_left' (Finset.sum_le_sum (fun i _ =>
    expected_coordinateStoppedCost_le control hN hActivity v T hT hv initialX initialY μ
      hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R i S)) _

end CarryingCapacity.PopulationStoppedCoupling
