import CarryingCapacity.PopulationCouplingConvergence
import CarryingCapacity.PopulationFocalProbability

/-!
# Convergence of finitely many actual coupled particle paths

Exchangeability of the paired initial law and the actual noise law gives a
fixed-particle probability estimate with one common exit tail and k times
the population-averaged stopped expectation. The established stopped-cost
limit then removes the common cutoff. No unstopped-cost expectation is
assumed finite. The initialization theorem separately constructs the coupled
initial laws satisfying the genuine initial pairing-error hypothesis below.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.PopulationFocalConvergence
open CommonInitialNoise ConfigurationLocalization PopulationCouplingAlgebra
open PopulationCouplingInitialization PopulationCouplingTime PopulationStoppedGronwall
open PopulationCouplingExit PopulationFocalProbability

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)
  (γ : ∀ n, Measure (Record (n + 1) D)) [∀ n, IsProbabilityMeasure (γ n)]
  (hex : ∀ n, ExchangeableMatching.ExchangeableLaw (γ n))
  (hright : ∀ n, (γ n).map right = Measure.pi (fun _ : Fin (n + 1) => ν.measure))
  (hInitialX : ∀ n, Integrable (fun a => lyapunov control (left a)) (γ n))
  (hInitialDistance : Tendsto (fun n => ∫ a, meanDistance κ (left a) (right a) ∂γ n)
    atTop (𝓝 0))

local notation "v" => NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment
local notation "hv" => Continuous.continuousOn (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment)
local notation "B" => environmentBound control ν T

include hex hright hInitialX hInitialDistance

/-- Each fixed finite collection of actual particle paths approaches its
synchronously driven nonlinear copies uniformly on the prescribed horizon,
in probability. The two initial arrays may depend on one another. -/
theorem probability_focalRunningCost_tendsto_zero (M : ℝ)
    (hMX : ∀ n, (∫ a, lyapunov control (left a) ∂γ n) ≤ M)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (γ n) (Label (n + 1) D)).real
      {p | ENNReal.ofReal ε < focalRunningCost control (Nat.succ_pos n) hActivity v T hT hv
        left right (focalIndices (n + 1) k) T p}) atTop (𝓝 0) := by
  let K := max M (∫ x, control.function x ∂ν.measure)
  apply LimitArguments.reciprocal_cutoff_limit
    (fun n => (law (γ n) (Label (n + 1) D)).real
      {p | ENNReal.ofReal ε < focalRunningCost control (Nat.succ_pos n) hActivity v T hT hv
        left right (focalIndices (n + 1) k) T p})
    (fun R n => (k : ℝ) * expectedCost control (Nat.succ_pos n) hActivity v T hT hv
      left right (γ n) ((R : ℝ) + 1) T / ε)
    (exitConstant control B K T)
  · intro n
    exact measureReal_nonneg
  · intro R _
    exact Eventually.of_forall (fun n => by
      have hy := NonlinearParticleConfiguration.integrable_initial_lyapunov control ν hMoment
        right measurable_right (γ n) (hright n)
      have hMY : (∫ a, lyapunov control (right a) ∂γ n) ≤ K := by
        rw [integral_initial_iid control (Nat.succ_pos n) ν hMoment
          (γ n) right measurable_right (hright n)]
        exact le_max_right _ _
      exact probability_focalRunningCost_le
        control (Nat.succ_pos n) hActivity v T hT hv (γ n) (hex n)
        hCoupling B (environmentBound_nonnegative control ν T hT)
        (environment_lyapunov_le_bound control hActivity ν T hT hCoupling hMoment)
        (hInitialX n) hy K ((hMX n).trans (le_max_left _ _)) hMY
        ((R : ℝ) + 1) (by positivity) ⟨T, hT⟩ le_rfl k ε hε)
  · intro R _
    have hh := PopulationCouplingConvergence.expectedCost_tendsto_zero
      control hActivity ν T hT hCoupling hMoment (fun _ => left) (fun _ => right) γ
      (fun _ => measurable_left) (fun _ => measurable_right) hright hInitialX hInitialDistance
      ((R : ℝ) + 1) (by positivity)
    simpa only [mul_zero, zero_div] using (hh.const_mul (k : ℝ)).div_const ε

/-- The same fixed-particle convergence for the actual extended event masses.
The finite probability law justifies the exact real-to-extended conversion. -/
theorem measure_focalRunningCost_tendsto_zero (M : ℝ)
    (hMX : ∀ n, (∫ a, lyapunov control (left a) ∂γ n) ≤ M)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (γ n) (Label (n + 1) D))
      {p | ENNReal.ofReal ε < focalRunningCost control (Nat.succ_pos n) hActivity v T hT hv
        left right (focalIndices (n + 1) k) T p}) atTop (𝓝 0) := by
  have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (probability_focalRunningCost_tendsto_zero control hActivity ν T hT hCoupling hMoment γ
      hex hright hInitialX hInitialDistance M hMX k ε hε)
  apply (show Tendsto (fun n => ENNReal.ofReal ((law (γ n) (Label (n + 1) D)).real
      {p | ENNReal.ofReal ε < focalRunningCost control (Nat.succ_pos n) hActivity v T hT hv
        left right (focalIndices (n + 1) k) T p})) atTop (𝓝 0) by
      simpa only [ENNReal.ofReal_zero] using hh).congr'
  exact Eventually.of_forall (fun n => ENNReal.ofReal_toReal (measure_ne_top _ _))

end CarryingCapacity.PopulationFocalConvergence
