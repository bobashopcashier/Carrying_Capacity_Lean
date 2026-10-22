import CarryingCapacity.PopulationCouplingExit
import CarryingCapacity.PopulationCouplingRemoval
import CarryingCapacity.PopulationCouplingTime

/-!
# Probability estimate for the actual unstopped population discrepancy

The genuine common-exit tail and stopped Markov estimate combine into the
finite real probability bound needed to take population and cutoff limits.
The stopped expectation is finite by the already-proved compensation bound.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal

namespace CarryingCapacity.PopulationCouplingProbability
open CommonInitialNoise ConfigurationLocalization PopulationCouplingAlgebra
open PopulationStoppedCoupling PopulationCouplingTime PopulationCouplingExit PopulationCouplingRemoval

variable {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N) (hActivity : MomentActivityBound κ q)
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))
  {A : Type*} [MeasurableSpace A] (initialX initialY : A → Configuration N D)
  (μ : Measure A) [IsProbabilityMeasure μ]
  (hCoupling : MomentCouplingBound κ q) (hinitX : Measurable initialX) (hinitY : Measurable initialY)
  (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ s ∈ Icc 0 T,
    LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
  (hInitialX : Integrable (fun a => lyapunov control (initialX a)) μ)
  (hInitialY : Integrable (fun a => lyapunov control (initialY a)) μ)

/-- The true exit coefficient is nonnegative under a nonnegative common
initial moment bound. It has no population-size argument. -/
theorem exitConstant_nonnegative (M S : ℝ) (hM : 0 ≤ M) :
    0 ≤ exitConstant control B M S := by
  unfold exitConstant
  positivity

include hCoupling hinitX hinitY hB hEnv hInitialX hInitialY

/-- An actual unstopped-error probability is bounded by the genuine uniform
exit tail and the actual finite stopped expectation. -/
theorem probability_runningCost_le (M : ℝ)
    (hMX : (∫ a, lyapunov control (initialX a) ∂μ) ≤ M)
    (hMY : (∫ a, lyapunov control (initialY a) ∂μ) ≤ M)
    (R : ℝ) (hR : 0 < R) (S : ℝ≥0) (hST : (S : ℝ) ≤ T)
    (ε : ℝ) (hε : 0 < ε) :
    (law μ (Label N D)).real
      {p | ENNReal.ofReal ε < averagedRunningCost control hN hActivity v T hT hv initialX initialY S p} ≤
    exitConstant control B M S / R +
      expectedCost control hN hActivity v T hT hv initialX initialY μ R S / ε := by
  have he := pairExit_probability_le_uniform control hN hActivity v T hT hv initialX initialY
    μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY M hMX hMY R S hR S.coe_nonneg
  simp only [ENNReal.ofReal_coe_nnreal] at he
  have hm := probability_runningCost_le_exit_add_markov control hN hActivity v T hT hv initialX initialY
    μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R S ε hε
  have hf := expectedStoppedCost_eq_ofReal control hN hActivity v T hT hv initialX initialY
    μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R hR.le S ⟨S.coe_nonneg,hST⟩
  change (∫⁻ p, averagedStoppedCost control hN hActivity v T hT hv initialX initialY R S p
    ∂law μ (Label N D)) = _ at hf
  rw [hf] at hm
  have hb := hm.trans (add_le_add_right he _)
  have hε' : ENNReal.ofReal ε ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hε)
  have hi : (ENNReal.ofReal ε)⁻¹ ≠ ⊤ := by simp [hε']
  have hp : (ENNReal.ofReal ε)⁻¹ *
      ENNReal.ofReal (expectedCost control hN hActivity v T hT hv initialX initialY μ R S) ≠ ⊤ :=
    ENNReal.mul_ne_top hi ENNReal.ofReal_ne_top
  have hfinite : ENNReal.ofReal (exitConstant control B M S / R) +
      (ENNReal.ofReal ε)⁻¹ *
        ENNReal.ofReal (expectedCost control hN hActivity v T hT hv initialX initialY μ R S) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,hp⟩
  have hM : 0 ≤ M := (integral_nonneg (fun a => lyapunov_nonnegative control (initialX a))).trans hMX
  have htail := div_nonneg (exitConstant_nonnegative control B M S hM) hR.le
  have hcost := expectedCost_nonnegative control hN hActivity v T hT hv initialX initialY μ R (S : ℝ)
  have hr := ENNReal.toReal_mono hfinite hb
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hp, ENNReal.toReal_ofReal htail,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hε.le,
    ENNReal.toReal_ofReal hcost] at hr
  simpa only [Measure.real, div_eq_mul_inv, mul_comm ε⁻¹] using hr

end CarryingCapacity.PopulationCouplingProbability
