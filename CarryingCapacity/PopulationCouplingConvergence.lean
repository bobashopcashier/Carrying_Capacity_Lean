import CarryingCapacity.PopulationStoppedGronwall
import CarryingCapacity.PopulationCouplingProbability
import CarryingCapacity.PopulationCouplingInitialization
import CarryingCapacity.LimitArguments

/-!
# Convergence of the actual coupled population paths

At each fixed Lyapunov cutoff, the actual expected stopped discrepancy tends
to zero using the derived Gronwall estimate and iid empirical-error theorem.
The genuine uniform exit bound then removes the cutoff after the population
limit. The initial-record spaces and their coupled laws may vary with N.
Only the genuine initial expected pairing error is assumed to converge here;
the initialization theorem separately derives that hypothesis from the paper.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.PopulationCouplingConvergence
open CommonInitialNoise ConfigurationLocalization PopulationCouplingAlgebra
open PopulationStoppedCoupling PopulationCouplingTime PopulationStoppedGronwall
open PopulationCouplingRemoval PopulationCouplingExit

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)
  {A : ℕ → Type*} [∀ n, MeasurableSpace (A n)]
  (initialX initialY : ∀ n, A n → Configuration (n + 1) D)
  (γ : ∀ n, Measure (A n)) [∀ n, IsProbabilityMeasure (γ n)]
  (hinitX : ∀ n, Measurable (initialX n)) (hinitY : ∀ n, Measurable (initialY n))
  (hright : ∀ n, (γ n).map (initialY n) = Measure.pi (fun _ : Fin (n + 1) => ν.measure))
  (hInitialX : ∀ n, Integrable (fun a => lyapunov control (initialX n a)) (γ n))
  (hInitialDistance : Tendsto (fun n => ∫ a, meanDistance κ (initialX n a) (initialY n a) ∂γ n)
    atTop (𝓝 0))

local notation "v" => NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment
local notation "hv" => Continuous.continuousOn (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment)
local notation "B" => environmentBound control ν T

include hinitX hinitY hright hInitialX hInitialDistance

/-- For each fixed cutoff the genuine real expected stopped cost tends to
zero. The integrated empirical error is the proved error of the actual iid copies. -/
theorem expectedCost_tendsto_zero (R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun n => expectedCost control (Nat.succ_pos n) hActivity v T hT hv
      (initialX n) (initialY n) (γ n) R T) atTop (𝓝 0) := by
  have hβ := NonlinearParticleEmpirical.integral_Ioc_beta_tendsto_zero
    control hActivity ν T hT hCoupling hMoment initialY hinitY γ hright
  have hupper : Tendsto (fun n => comparisonFactor control hCoupling ν T R *
      ((∫ a, meanDistance κ (initialX n a) (initialY n a) ∂γ n) +
        ∫ t in Ioc 0 T, NonlinearParticleEmpirical.beta control hActivity ν T hT hCoupling hMoment
          n (initialY n) (γ n) t)) atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using (hInitialDistance.add hβ).const_mul
      (comparisonFactor control hCoupling ν T R)
  apply squeeze_zero (fun n => expectedCost_nonnegative control (Nat.succ_pos n) hActivity v T hT hv
    (initialX n) (initialY n) (γ n) R T) _ hupper
  intro n
  exact nonlinear_expectedCost_le_factor control hActivity ν T hT hCoupling hMoment n
    (initialX n) (initialY n) (γ n) (hinitX n) (hinitY n) (hright n) (hInitialX n)
    R hR T ⟨hT, le_rfl⟩

/-- Extended expectations also converge: finiteness is proved before replacing
the extended value by `ofReal` of its ordinary expectation. -/
theorem expectedStoppedCost_tendsto_zero (R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun n => expectedStoppedCost control (Nat.succ_pos n) hActivity v T hT hv
      (initialX n) (initialY n) (γ n) R T) atTop (𝓝 0) := by
  have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (expectedCost_tendsto_zero control hActivity ν T hT hCoupling hMoment initialX initialY γ
      hinitX hinitY hright hInitialX hInitialDistance R hR)
  apply (show Tendsto (fun n => ENNReal.ofReal (expectedCost control (Nat.succ_pos n) hActivity v T hT hv
      (initialX n) (initialY n) (γ n) R T)) atTop (𝓝 0) by simpa only [ENNReal.ofReal_zero] using hh).congr'
  exact Eventually.of_forall (fun n =>
    (expectedStoppedCost_eq_ofReal control (Nat.succ_pos n) hActivity v T hT hv
      (initialX n) (initialY n) (γ n) hCoupling (hinitX n) (hinitY n) B
      (environmentBound_nonnegative control ν T hT)
      (environment_lyapunov_le_bound control hActivity ν T hT hCoupling hMoment)
      (hInitialX n) (NonlinearParticleConfiguration.integrable_initial_lyapunov control ν hMoment
        (initialY n) (hinitY n) (γ n) (hright n)) R hR T ⟨hT, le_rfl⟩).symm)

/-- A uniform initial left moment and the exact iid right marginal suffice
for removal of the actual common cutoff. There is no independence assumption
between the two coupled initial arrays. -/
theorem probability_runningCost_tendsto_zero (M : ℝ)
    (hMX : ∀ n, (∫ a, lyapunov control (initialX n a) ∂γ n) ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (γ n) (Label (n + 1) D)).real
      {p | ENNReal.ofReal ε < averagedRunningCost control (Nat.succ_pos n) hActivity v T hT hv
        (initialX n) (initialY n) T p}) atTop (𝓝 0) := by
  let K := max M (∫ x, control.function x ∂ν.measure)
  apply LimitArguments.reciprocal_cutoff_limit
    (fun n => (law (γ n) (Label (n + 1) D)).real
      {p | ENNReal.ofReal ε < averagedRunningCost control (Nat.succ_pos n) hActivity v T hT hv
        (initialX n) (initialY n) T p})
    (fun R n => expectedCost control (Nat.succ_pos n) hActivity v T hT hv
      (initialX n) (initialY n) (γ n) ((R : ℝ) + 1) T / ε)
    (exitConstant control B K T)
  · intro n
    exact measureReal_nonneg
  · intro R _
    exact Eventually.of_forall (fun n => by
      have hy := NonlinearParticleConfiguration.integrable_initial_lyapunov control ν hMoment
        (initialY n) (hinitY n) (γ n) (hright n)
      have hMY : (∫ a, lyapunov control (initialY n a) ∂γ n) ≤ K := by
        rw [PopulationCouplingInitialization.integral_initial_iid control (Nat.succ_pos n) ν hMoment
          (γ n) (initialY n) (hinitY n) (hright n)]
        exact le_max_right _ _
      exact PopulationCouplingProbability.probability_runningCost_le
        control (Nat.succ_pos n) hActivity v T hT hv (initialX n) (initialY n) (γ n)
        hCoupling (hinitX n) (hinitY n) B (environmentBound_nonnegative control ν T hT)
        (environment_lyapunov_le_bound control hActivity ν T hT hCoupling hMoment)
        (hInitialX n) hy K ((hMX n).trans (le_max_left _ _)) hMY
        ((R : ℝ) + 1) (by positivity) ⟨T, hT⟩ le_rfl ε hε)
  · intro R _
    simpa only [zero_div] using
      (expectedCost_tendsto_zero control hActivity ν T hT hCoupling hMoment initialX initialY γ
        hinitX hinitY hright hInitialX hInitialDistance ((R : ℝ) + 1) (by positivity)).div_const ε

/-- The same convergence for the genuine event masses in `ℝ≥0∞`; the finite
probability law justifies the exact real-to-extended conversion. -/
theorem measure_runningCost_tendsto_zero (M : ℝ)
    (hMX : ∀ n, (∫ a, lyapunov control (initialX n a) ∂γ n) ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (γ n) (Label (n + 1) D))
      {p | ENNReal.ofReal ε < averagedRunningCost control (Nat.succ_pos n) hActivity v T hT hv
        (initialX n) (initialY n) T p}) atTop (𝓝 0) := by
  have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (probability_runningCost_tendsto_zero control hActivity ν T hT hCoupling hMoment initialX initialY γ
      hinitX hinitY hright hInitialX hInitialDistance M hMX ε hε)
  apply (show Tendsto (fun n => ENNReal.ofReal ((law (γ n) (Label (n + 1) D)).real
      {p | ENNReal.ofReal ε < averagedRunningCost control (Nat.succ_pos n) hActivity v T hT hv
        (initialX n) (initialY n) T p})) atTop (𝓝 0) by simpa only [ENNReal.ofReal_zero] using hh).congr'
  exact Eventually.of_forall (fun n => ENNReal.ofReal_toReal (measure_ne_top _ _))

end CarryingCapacity.PopulationCouplingConvergence
