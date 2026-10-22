import CarryingCapacity.PopulationStoppedCoupling
import CarryingCapacity.GlobalLyapunovExit

/-!
# Uniform tails of the actual population comparison exit

The interacting and prescribed-environment configurations share the original
noise and arbitrary coupled initial records. Their proved averaged drifts
discharge the global paired-exit theorem. A uniform bound on the two initial
averaged Lyapunov expectations gives an explicit constant independent of N
and the localization threshold, as required in Proposition 5.3.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal NNReal

namespace CarryingCapacity.PopulationCouplingExit
open CommonInitialNoise ConfigurationLocalization PopulationStoppedCoupling

variable {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N) (hActivity : MomentActivityBound κ q)
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))
  {A : Type*} [MeasurableSpace A] (initialX initialY : A → Configuration N D)
  (μ : Measure A) [IsProbabilityMeasure μ]
  (hCoupling : MomentCouplingBound κ q)
  (hinitX : Measurable initialX) (hinitY : Measurable initialY)
  (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ s ∈ Icc 0 T,
    LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
  (hInitialX : Integrable (fun a => lyapunov control (initialX a)) μ)
  (hInitialY : Integrable (fun a => lyapunov control (initialY a)) μ)

local notation "V" => lyapunov control
local notation "hfin" => finite_sublevel control hN
local notation "rX" => ConfigurationTimeDependent.timeRate κ q hN
local notation "rY" => DeterministicEnvironmentConfiguration.rate κ q v T
local notation "boundX" => ConfigurationTimeDependent.uniform_rate_bounds control hN
local notation "boundY" => DeterministicEnvironmentConfiguration.exists_uniform_rate_bounds control hN hActivity v T hT hv
local notation "aX" => (2 * ConfigurationLocalization.driftConstant control)
local notation "aY" => DeterministicEnvironmentLyapunov.affineConstant control B

include hCoupling hinitX hinitY hB hEnv hInitialX hInitialY

/-- The actual joint exit is AE measurable on the original probability space. -/
theorem aemeasurable_pairExit (R : ℝ) :
    AEMeasurable (pairExit control hN hActivity v T hT hv initialX initialY R)
      (law μ (Label N D)) :=
  GlobalLyapunovExit.aemeasurable_pairedFirstExit V hfin jump rX rY boundX boundY
    initialX initialY 0 μ (ConfigurationTimeDependent.measurable_timeRate hN)
    (DeterministicEnvironmentConfiguration.measurable_rate v T hT hv hCoupling)
    hinitX hinitY aX aY
    (mul_nonneg (by norm_num) (ConfigurationLocalization.driftConstant_nonnegative control))
    (DeterministicEnvironmentLyapunov.affineConstant_nonnegative control B hB)
    (lyapunov_nonnegative control)
    (fun z j t _ => ConfigurationTimeDependent.timeRate_nonnegative hN j t z)
    (fun z j t _ => DeterministicEnvironmentConfiguration.rate_nonnegative v T j t z)
    hInitialX hInitialY
    (fun z t _ => ConfigurationTimeDependent.generator_affine_bound control hN z t)
    (fun z t _ => DeterministicEnvironmentConfiguration.generator_lyapunov_affine
      control hN v T hT B hB hEnv t z) R

/-- Reciprocal probability bound for the genuine joint exit, including an
initial exit and crossings at the terminal time. No coupling independence
or stochastic exit estimate is assumed. -/
theorem pairExit_probability_le (R S : ℝ) (hR : 0 < R) (hS : 0 ≤ S) :
    (law μ (Label N D))
      {p | pairExit control hN hActivity v T hT hv initialX initialY R p ≤ ENNReal.ofReal S} ≤
    ENNReal.ofReal (4 *
      ((1 + ∫ a, V (initialX a) ∂μ) * Real.exp (aX * S) +
       (1 + ∫ a, V (initialY a) ∂μ) * Real.exp (aY * S)) / R) :=
  GlobalLyapunovExit.pairedFirstExit_probability_le V hfin jump rX rY boundX boundY
    initialX initialY 0 μ (ConfigurationTimeDependent.measurable_timeRate hN)
    (DeterministicEnvironmentConfiguration.measurable_rate v T hT hv hCoupling)
    hinitX hinitY aX aY
    (mul_nonneg (by norm_num) (ConfigurationLocalization.driftConstant_nonnegative control))
    (DeterministicEnvironmentLyapunov.affineConstant_nonnegative control B hB)
    (lyapunov_nonnegative control)
    (fun z j t _ => ConfigurationTimeDependent.timeRate_nonnegative hN j t z)
    (fun z j t _ => DeterministicEnvironmentConfiguration.rate_nonnegative v T j t z)
    hInitialX hInitialY
    (fun z t _ => ConfigurationTimeDependent.generator_affine_bound control hN z t)
    (fun z t _ => DeterministicEnvironmentConfiguration.generator_lyapunov_affine
      control hN v T hT B hB hEnv t z) R S hR hS

omit hN hActivity v T hT hv initialX initialY μ hCoupling hinitX hinitY hB hEnv
  hInitialX hInitialY [MeasurableSpace A] [IsProbabilityMeasure μ] in
/-- The numerator depends on the model, environment bound, initial bound and
horizon, but not on N, R, the initial coupling, or the realization. -/
def exitConstant (M S : ℝ) : ℝ :=
  4 * (1 + M) * (Real.exp (aX * S) + Real.exp (aY * S))

/-- The stated bound is uniform over particle numbers whenever the two
genuine initial averaged Lyapunov expectations have a common bound. -/
theorem pairExit_probability_le_uniform (M : ℝ)
    (hMX : (∫ a, V (initialX a) ∂μ) ≤ M)
    (hMY : (∫ a, V (initialY a) ∂μ) ≤ M)
    (R S : ℝ) (hR : 0 < R) (hS : 0 ≤ S) :
    (law μ (Label N D))
      {p | pairExit control hN hActivity v T hT hv initialX initialY R p ≤ ENNReal.ofReal S} ≤
    ENNReal.ofReal (exitConstant control B M S / R) := by
  apply (pairExit_probability_le control hN hActivity v T hT hv initialX initialY μ
    hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R S hR hS).trans
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ hR.le
  have hx := mul_le_mul_of_nonneg_right (add_le_add_left hMX 1) (Real.exp_pos (aX * S)).le
  have hy := mul_le_mul_of_nonneg_right (add_le_add_left hMY 1) (Real.exp_pos (aY * S)).le
  calc
    _ ≤ 4 * ((1 + M) * Real.exp (aX * S) + (1 + M) * Real.exp (aY * S)) := by linarith
    _ = exitConstant control B M S := by unfold exitConstant; ring

end CarryingCapacity.PopulationCouplingExit
