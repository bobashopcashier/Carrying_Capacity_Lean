import CarryingCapacity.PopulationStoppedVolterra
import CarryingCapacity.PopulationCouplingTime
import CarryingCapacity.PopulationNonlinearError
import CarryingCapacity.IntegrableGronwall

/-!
# The actual stopped population Gronwall estimate

The sharp compensated inequality is combined with genuine time integrability
of the expected stopped cost and empirical error. The nonlinear specialization
discharges all empirical-error and independent-initial moment premises using
the actual iid array. Its constants depend on the model, Lyapunov envelope,
localization threshold and horizon, but not on population size.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal

namespace CarryingCapacity.PopulationStoppedGronwall
open CommonInitialNoise ConfigurationLocalization PopulationCouplingAlgebra
open PopulationStoppedCoupling PopulationCouplingTime

section General
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
  (hError : ∀ s ∈ Icc 0 T, Integrable
    (fun p => empiricalError control hN hActivity v T hT hv initialY p s) (law μ (Label N D)))
  (hErrorProd : Integrable (fun p : Sample A (Label N D) × ℝ =>
    empiricalError control hN hActivity v T hT hv initialY p.1 p.2)
    ((law μ (Label N D)).prod (volume.restrict (Ioc 0 T))))
include hCoupling hinitX hinitY hB hEnv hInitialX hInitialY hError hErrorProd

/-- Actual compensated comparison followed by integrable Gronwall. No
expected comparison inequality or continuity of the expected cost is an input. -/
theorem expectedCost_le_exp (R : ℝ) (hR : 0 ≤ R) (s : ℝ) (hs : s ∈ Icc 0 T) :
    expectedCost control hN hActivity v T hT hv initialX initialY μ R s ≤
      ((∫ a, meanDistance κ (initialX a) (initialY a) ∂μ) +
        localizedConstant κ q hCoupling R B * ∫ t in Ioc 0 s,
          ∫ p, empiricalError control hN hActivity v T hT hv initialY p t ∂law μ (Label N D)) *
        Real.exp (localizedConstant κ q hCoupling R B * s) := by
  apply IntegrableGronwall.le_exp_mul_add_integral
    (PopulationCouplingTime.integrableOn_expectedCost_Ioc control hN hActivity v T hT hv
      initialX initialY μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R hR)
    hErrorProd.integral_prod_right
    (Eventually.of_forall (fun t => integral_nonneg (fun p =>
      empiricalError_nonnegative control hN hActivity v T hT hv initialY p t)))
    (localizedConstant_nonnegative κ q hCoupling R B hR hB) _ s hs
  intro t ht
  exact PopulationStoppedVolterra.expectedCost_le_integral control hN hActivity v T hT hv
    initialX initialY μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY
    hError hErrorProd R hR ⟨t, ht.1⟩ ht.2

end General

section Nonlinear
variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}

/-- The actual terminal manuscript envelope, independent of population size. -/
def environmentBound (control : LyapunovControl κ q) (ν : MomentLaw κ D) (T : ℝ) : ℝ :=
  DeterministicEnvironmentLyapunov.manuscriptBound control ν
    (DeterministicEnvironmentLyapunov.driftConstant control) T

theorem environmentBound_nonnegative (control : LyapunovControl κ q) (ν : MomentLaw κ D)
    (T : ℝ) (hT : 0 ≤ T) : 0 ≤ environmentBound control ν T :=
  DeterministicEnvironmentLyapunov.manuscriptBound_nonnegative control ν
    (DeterministicEnvironmentLyapunov.driftConstant control) T
    (DeterministicEnvironmentLyapunov.driftConstant_nonnegative control) hT

/-- The localized scalar coefficient contains no particle-number factor. -/
def comparisonConstant (control : LyapunovControl κ q) (hCoupling : MomentCouplingBound κ q)
    (ν : MomentLaw κ D) (T R : ℝ) : ℝ :=
  localizedConstant κ q hCoupling R (environmentBound control ν T)

theorem comparisonConstant_nonnegative (control : LyapunovControl κ q)
    (hCoupling : MomentCouplingBound κ q) (ν : MomentLaw κ D)
    (T : ℝ) (hT : 0 ≤ T) (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ comparisonConstant control hCoupling ν T R :=
  localizedConstant_nonnegative κ q hCoupling R (environmentBound control ν T) hR
    (environmentBound_nonnegative control ν T hT)

/-- A convenient common coefficient in the final population estimate. -/
def comparisonFactor (control : LyapunovControl κ q) (hCoupling : MomentCouplingBound κ q)
    (ν : MomentLaw κ D) (T R : ℝ) : ℝ :=
  (1 + comparisonConstant control hCoupling ν T R) *
    Real.exp (comparisonConstant control hCoupling ν T R * T)

theorem comparisonFactor_nonnegative (control : LyapunovControl κ q)
    (hCoupling : MomentCouplingBound κ q) (ν : MomentLaw κ D)
    (T : ℝ) (hT : 0 ≤ T) (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ comparisonFactor control hCoupling ν T R :=
  mul_nonneg (by linarith [comparisonConstant_nonnegative control hCoupling ν T hT R hR])
    (Real.exp_pos _).le

variable (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)

local notation "v" => NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment
local notation "hv" => Continuous.continuousOn (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment)
local notation "B" => environmentBound control ν T
local notation "C" => comparisonConstant control hCoupling ν T

/-- The actual fixed curve supplies the genuine uniform environmental moment
bound required by the population construction and exit estimate. -/
theorem environment_lyapunov_le_bound (s : ℝ) (_hs : s ∈ Icc 0 T) :
    LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B :=
  DeterministicEnvironmentLyapunov.manuscriptExtension_bound control ν
    (DeterministicEnvironmentLyapunov.driftConstant control) T
    (DeterministicEnvironmentLyapunov.driftConstant_nonnegative control) hT
    (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hMoment) s

variable {A : Type*} [MeasurableSpace A] (n : ℕ)
  (initialX initialY : A → Configuration (n + 1) D)
  (μ : Measure A) [IsProbabilityMeasure μ]
  (hinitX : Measurable initialX) (hinitY : Measurable initialY)
  (hright : μ.map initialY = Measure.pi (fun _ : Fin (n + 1) => ν.measure))
  (hInitialX : Integrable (fun a => lyapunov control (initialX a)) μ)
include hinitX hinitY hright hInitialX

/-- The sharp stopped estimate for the actual nonlinear comparison array.
Every empirical-error and right-initial integrability premise is discharged. -/
theorem nonlinear_expectedCost_le (R : ℝ) (hR : 0 ≤ R) (s : ℝ) (hs : s ∈ Icc 0 T) :
    expectedCost control (Nat.succ_pos n) hActivity v T hT hv initialX initialY μ R s ≤
      ((∫ a, meanDistance κ (initialX a) (initialY a) ∂μ) + C R *
        ∫ t in Ioc 0 s, NonlinearParticleEmpirical.beta control hActivity ν T hT hCoupling hMoment
          n initialY μ t) * Real.exp (C R * s) := by
  have hY := NonlinearParticleConfiguration.integrable_initial_lyapunov control ν hMoment
    initialY hinitY μ hright
  have h := expectedCost_le_exp control (Nat.succ_pos n) hActivity v T hT hv initialX initialY μ
    hCoupling hinitX hinitY B (environmentBound_nonnegative control ν T hT)
    (environment_lyapunov_le_bound control hActivity ν T hT hCoupling hMoment) hInitialX hY
    (PopulationNonlinearError.integrable_error control hActivity ν T hT hCoupling hMoment
      n initialY hinitY μ hright)
    (PopulationNonlinearError.integrable_error_prod control hActivity ν T hT hCoupling hMoment
      n initialY hinitY μ hright) R hR s hs
  have he : (∫ t in Ioc 0 s, ∫ p,
      empiricalError control (Nat.succ_pos n) hActivity v T hT hv initialY p t ∂law μ (Label (n + 1) D)) =
      ∫ t in Ioc 0 s, NonlinearParticleEmpirical.beta control hActivity ν T hT hCoupling hMoment
        n initialY μ t := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    exact PopulationNonlinearError.expectedError_eq_beta control hActivity ν T hT hCoupling hMoment
      n initialY hinitY μ hright t ht.1.le
  rw [he] at h
  exact h

/-- A uniform-in-time factor for the actual finite population stopped mean. -/
theorem nonlinear_expectedCost_le_factor (R : ℝ) (hR : 0 ≤ R) (s : ℝ) (hs : s ∈ Icc 0 T) :
    expectedCost control (Nat.succ_pos n) hActivity v T hT hv initialX initialY μ R s ≤
      comparisonFactor control hCoupling ν T R *
        ((∫ a, meanDistance κ (initialX a) (initialY a) ∂μ) +
          ∫ t in Ioc 0 s, NonlinearParticleEmpirical.beta control hActivity ν T hT hCoupling hMoment
            n initialY μ t) := by
  have hC := comparisonConstant_nonnegative control hCoupling ν T hT R hR
  have ha : 0 ≤ ∫ a, meanDistance κ (initialX a) (initialY a) ∂μ :=
    integral_nonneg (fun a => meanDistance_nonnegative κ _ _)
  have hb : 0 ≤ ∫ t in Ioc 0 s,
      NonlinearParticleEmpirical.beta control hActivity ν T hT hCoupling hMoment n initialY μ t :=
    integral_nonneg (fun t => NonlinearParticleEmpirical.beta_nonnegative
      control hActivity ν T hT hCoupling hMoment n initialY μ t)
  apply (nonlinear_expectedCost_le control hActivity ν T hT hCoupling hMoment n initialX initialY μ
    hinitX hinitY hright hInitialX R hR s hs).trans
  have he : Real.exp (C R * s) ≤ Real.exp (C R * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 hC)
  apply (mul_le_mul_of_nonneg_left he (add_nonneg ha (mul_nonneg hC hb))).trans
  unfold comparisonFactor
  have hh := add_nonneg (mul_nonneg hC ha) hb
  nlinarith [Real.exp_pos (C R * T)]

/-- Exact extended expectation version of the sharp bound. Finiteness was
proved before conversion, so infinity is never replaced by zero. -/
theorem nonlinear_expectedStoppedCost_le (R : ℝ) (hR : 0 ≤ R) (s : ℝ) (hs : s ∈ Icc 0 T) :
    expectedStoppedCost control (Nat.succ_pos n) hActivity v T hT hv initialX initialY μ R s ≤
      ENNReal.ofReal (((∫ a, meanDistance κ (initialX a) (initialY a) ∂μ) + C R *
        ∫ t in Ioc 0 s, NonlinearParticleEmpirical.beta control hActivity ν T hT hCoupling hMoment
          n initialY μ t) * Real.exp (C R * s)) := by
  rw [PopulationCouplingTime.expectedStoppedCost_eq_ofReal control (Nat.succ_pos n) hActivity v T hT hv
    initialX initialY μ hCoupling hinitX hinitY B (environmentBound_nonnegative control ν T hT)
    (environment_lyapunov_le_bound control hActivity ν T hT hCoupling hMoment) hInitialX
    (NonlinearParticleConfiguration.integrable_initial_lyapunov control ν hMoment initialY hinitY μ hright)
    R hR s hs]
  exact ENNReal.ofReal_le_ofReal (nonlinear_expectedCost_le control hActivity ν T hT hCoupling hMoment
    n initialX initialY μ hinitX hinitY hright hInitialX R hR s hs)

/-- The common coefficient version is the form used in the N-then-R limit. -/
theorem nonlinear_expectedStoppedCost_le_factor (R : ℝ) (hR : 0 ≤ R) (s : ℝ) (hs : s ∈ Icc 0 T) :
    expectedStoppedCost control (Nat.succ_pos n) hActivity v T hT hv initialX initialY μ R s ≤
      ENNReal.ofReal (comparisonFactor control hCoupling ν T R *
        ((∫ a, meanDistance κ (initialX a) (initialY a) ∂μ) +
          ∫ t in Ioc 0 s, NonlinearParticleEmpirical.beta control hActivity ν T hT hCoupling hMoment
            n initialY μ t)) := by
  rw [PopulationCouplingTime.expectedStoppedCost_eq_ofReal control (Nat.succ_pos n) hActivity v T hT hv
    initialX initialY μ hCoupling hinitX hinitY B (environmentBound_nonnegative control ν T hT)
    (environment_lyapunov_le_bound control hActivity ν T hT hCoupling hMoment) hInitialX
    (NonlinearParticleConfiguration.integrable_initial_lyapunov control ν hMoment initialY hinitY μ hright)
    R hR s hs]
  exact ENNReal.ofReal_le_ofReal (nonlinear_expectedCost_le_factor control hActivity ν T hT hCoupling hMoment
    n initialX initialY μ hinitX hinitY hright hInitialX R hR s hs)

end Nonlinear
end CarryingCapacity.PopulationStoppedGronwall
