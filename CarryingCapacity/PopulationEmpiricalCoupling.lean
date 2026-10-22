import CarryingCapacity.PopulationCouplingRemoval

/-!
# Uniform empirical transport comparison from the actual paired paths

The indexwise empirical coupling bounds transport at every real time by the
average of coordinate distances. Taking a supremum then gives the actual
uniform empirical discrepancy bounded by the average coordinate running cost.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal

namespace CarryingCapacity.PopulationEmpiricalCoupling
open CommonInitialNoise ConfigurationLocalization PopulationCouplingAlgebra
open PopulationCouplingRemoval SynchronousRunningSupremum

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

/-- Supremum of the actual empirical transport distance over the whole horizon. -/
def empiricalRunningCost (S : ℝ) (p : Sample A (Label N D)) : ℝ≥0∞ :=
  runningCost VX hfin jump rX bX rY bY initialX initialY 0
    (fun z w => wasserstein (empiricalLaw κ hN z) (empiricalLaw κ hN w)) S p

omit [MeasurableSpace A] in
/-- Every current average distance is dominated by the average of the actual
coordinate running suprema. -/
theorem currentMeanDistance_le_runningCost (S s : ℝ) (p : Sample A (Label N D))
    (hs : s ∈ Icc 0 S) :
    ENNReal.ofReal (meanDistance κ (X p s) (Y p s)) ≤
      averagedRunningCost control hN hActivity v T hT hv initialX initialY S p := by
  simp only [meanDistance, ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg N)),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => adaptedDistance_nonneg κ (X p s i) (Y p s i)),
    averagedRunningCost]
  apply mul_le_mul_left'
  apply Finset.sum_le_sum
  intro i _
  exact le_iSup_of_le (⟨s,hs⟩ : Icc (0 : ℝ) S) le_rfl

omit [MeasurableSpace A] in
/-- The uniform empirical comparison is pointwise dominated, without any
measurability premise or exceptional event. -/
theorem empiricalRunningCost_le (S : ℝ) (p : Sample A (Label N D)) :
    empiricalRunningCost control hN hActivity v T hT hv initialX initialY S p ≤
      averagedRunningCost control hN hActivity v T hT hv initialX initialY S p := by
  apply iSup_le
  intro s
  exact (ENNReal.ofReal_le_ofReal (wasserstein_empiricalLaw_le κ hN (X p s) (Y p s))).trans
    (currentMeanDistance_le_runningCost control hN hActivity v T hT hv initialX initialY S s p s.property)

variable (μ : Measure A) [IsProbabilityMeasure μ]
  (hCoupling : MomentCouplingBound κ q) (hinitX : Measurable initialX) (hinitY : Measurable initialY)
  (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ s ∈ Icc 0 T,
    LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
  (hInitialX : Integrable (fun a => lyapunov control (initialX a)) μ)
  (hInitialY : Integrable (fun a => lyapunov control (initialY a)) μ)
include hCoupling hinitX hinitY hB hEnv hInitialX hInitialY

/-- Actual empirical path comparison is AE measurable by the constructed
paths and their countable observation version. -/
theorem aemeasurable_empiricalRunningCost (S : ℝ≥0) :
    AEMeasurable (empiricalRunningCost control hN hActivity v T hT hv initialX initialY S)
      (law μ (Label N D)) :=
  aemeasurable_runningCost VX hfin jump rX bX rY bY initialX initialY 0 μ
    (ConfigurationTimeDependent.measurable_timeRate hN)
    (DeterministicEnvironmentConfiguration.measurable_rate v T hT hv hCoupling) hinitX hinitY
    (ConfigurationTimeDependent.ae_exhaustive control hN initialX μ hinitX hInitialX)
    (DeterministicEnvironmentConfiguration.ae_exhaustive control hN hActivity v T hT hv initialY μ
      hCoupling hinitY B hB hEnv hInitialY)
    (fun z w => wasserstein (empiricalLaw κ hN z) (empiricalLaw κ hN w)) S

omit hCoupling hinitX hinitY hB hEnv hInitialX hInitialY in
/-- The genuine empirical-error probability is bounded by the paired-path
probability, with finite probabilities before real conversion. -/
theorem probability_empiricalRunningCost_le (S ε : ℝ) :
    (law μ (Label N D)).real
      {p | ENNReal.ofReal ε < empiricalRunningCost control hN hActivity v T hT hv initialX initialY S p} ≤
    (law μ (Label N D)).real
      {p | ENNReal.ofReal ε < averagedRunningCost control hN hActivity v T hT hv initialX initialY S p} := by
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro p hp
  exact hp.trans_le (empiricalRunningCost_le control hN hActivity v T hT hv initialX initialY S p)

end CarryingCapacity.PopulationEmpiricalCoupling
