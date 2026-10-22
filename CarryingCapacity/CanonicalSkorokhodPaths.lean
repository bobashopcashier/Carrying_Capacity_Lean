import CarryingCapacity.SkorokhodPathOperations
import CarryingCapacity.SkorokhodStepApproximation
import CarryingCapacity.ConfigurationTimeDependent
import CarryingCapacity.NonlinearFixedPoint
import CarryingCapacity.NonlinearGlobalProcess

/-!
# The actual canonical processes as Skorokhod random paths

The finite-activity sets come from the genuine localized proposal lists.
Measurable coordinate observations and deterministic grid approximation give
Borel AE measurability of the actual restrictions, with a constant fallback
only on exceptional non-càdlàg samples.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical Topology ENNReal NNReal

namespace CarryingCapacity.CanonicalSkorokhodPaths
open CommonInitialNoise ConfigurationLocalization SkorokhodJ1

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q)

section Configuration
variable {N : ℕ} (hN : 0 < N) {A : Type*} [MeasurableSpace A]
  (initial : A → Configuration N D) (T : ℝ≥0)

def configurationPath (p : Sample A (Label N D)) : Path T (Configuration N D) :=
  realPathOrConst T 0 (ConfigurationTimeDependent.process control hN initial p)

variable (μ : Measure A) [IsProbabilityMeasure μ] (hinit : Measurable initial)
  (hV : Integrable (fun a => lyapunov control (initial a)) μ)
include hinit hV

theorem ae_configuration_cadlag : ∀ᵐ p ∂law μ (Label N D),
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt
      (ConfigurationTimeDependent.process control hN initial p) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : Configuration N D, Tendsto
      (ConfigurationTimeDependent.process control hN initial p) (𝓝[<] t) (𝓝 y)) :=
  TimeDependentGlobalProcess.ae_process_cadlag (lyapunov control)
    (finite_sublevel control hN) jump (ConfigurationTimeDependent.timeRate κ q hN)
    (ConfigurationTimeDependent.uniform_rate_bounds control hN) initial 0 μ
    (ConfigurationTimeDependent.ae_exhaustive control hN initial μ hinit hV)

theorem ae_configuration_finite_activity : ∀ᵐ p ∂law μ (Label N D),
    ∃ F : Finset ℝ, (∀ r ∈ F, r ∈ Ioc 0 (T : ℝ)) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        (∀ r ∈ F, r ∉ Ioc s t) →
        ConfigurationTimeDependent.process control hN initial p s =
          ConfigurationTimeDependent.process control hN initial p t := by
  filter_upwards [TimeDependentGlobalActivity.ae_finite_activity (lyapunov control)
    (finite_sublevel control hN) jump (ConfigurationTimeDependent.timeRate κ q hN)
    (ConfigurationTimeDependent.uniform_rate_bounds control hN) initial 0 μ
    (ConfigurationTimeDependent.ae_exhaustive control hN initial μ hinit hV)] with p hp
  obtain ⟨n, hF, he⟩ := hp T
  exact ⟨_, fun r hr => hF hr, he⟩

theorem ae_configurationPath_apply : ∀ᵐ p ∂law μ (Label N D),
    ∀ t : Time T, configurationPath control hN initial T p t =
      ConfigurationTimeDependent.process control hN initial p t :=
  ae_realPathOrConst_apply (law μ (Label N D)) 0 _
    (ae_configuration_cadlag control hN initial μ hinit hV)

/-- Genuine Borel AE measurability of the constructed configuration path. -/
theorem aemeasurable_configurationPath :
    AEMeasurable (configurationPath control hN initial T) (law μ (Label N D)) :=
  SkorokhodStepApproximation.aemeasurable_realPathOrConst (law μ (Label N D)) T 0 _
    (fun _ => (ConfigurationTimeDependent.measurable_process control hN initial hinit).of_uncurry_right)
    (ae_configuration_cadlag control hN initial μ hinit hV)
    (ae_configuration_finite_activity control hN initial T μ hinit hV)

end Configuration

section Nonlinear
variable (hActivity : MomentActivityBound κ q) (ν : MomentLaw κ D) (T : ℝ≥0)
  (hCoupling : MomentCouplingBound κ q) (hMoment : Integrable control.function ν.measure)

local notation "v" => NonlinearFixedPoint.environment control hActivity ν T T.coe_nonneg hCoupling hMoment
local notation "hv" => Continuous.continuousOn (NonlinearFixedPoint.continuous_environment control hActivity ν T T.coe_nonneg hCoupling hMoment)
local notation "X" => NonlinearFixedPoint.process control hActivity ν T T.coe_nonneg hCoupling hMoment

def nonlinearPath (p : Sample (State D) (Jump D)) : Path T (State D) :=
  realPathOrConst T 0 (X p)

/-- The finite proposal lists controlling the actual nonlinear realization
also control its closed finite-horizon restriction. -/
theorem ae_nonlinear_finite_activity : ∀ᵐ p ∂law ν.measure (Jump D),
    ∃ F : Finset ℝ, (∀ r ∈ F, r ∈ Ioc 0 (T : ℝ)) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        (∀ r ∈ F, r ∉ Ioc s t) → X p s = X p t := by
  filter_upwards [TimeDependentGlobalActivity.ae_finite_activity control.function
    (DeterministicEnvironmentLyapunov.finite_sublevels control) Jump.advance
    (DeterministicEnvironmentFrozen.timeRate κ q v T)
    (DeterministicEnvironmentLyapunov.exists_uniform_rate_bounds control v T T.coe_nonneg hActivity hv)
    id 0 ν.measure
    (NonlinearFixedPoint.ae_exhaustive control hActivity ν T T.coe_nonneg hCoupling hMoment)]
    with p hp
  obtain ⟨n, hF, he⟩ := hp T
  exact ⟨_, fun r hr => hF hr, he⟩

theorem ae_nonlinearPath_apply : ∀ᵐ p ∂law ν.measure (Jump D),
    ∀ t : Time T, nonlinearPath control hActivity ν T hCoupling hMoment p t = X p t :=
  ae_realPathOrConst_apply (law ν.measure (Jump D)) 0 _
    (NonlinearFixedPoint.ae_process_cadlag control hActivity ν T T.coe_nonneg hCoupling hMoment)

/-- The actual nonlinear trajectory defines a random variable in the genuine
J1 Borel space, not just in the coordinate sigma algebra. -/
theorem aemeasurable_nonlinearPath :
    AEMeasurable (nonlinearPath control hActivity ν T hCoupling hMoment) (law ν.measure (Jump D)) :=
  SkorokhodStepApproximation.aemeasurable_realPathOrConst (law ν.measure (Jump D)) T 0 _
    (fun _ => (NonlinearFixedPoint.measurable_process control hActivity ν T T.coe_nonneg
      hCoupling hMoment).of_uncurry_right)
    (NonlinearFixedPoint.ae_process_cadlag control hActivity ν T T.coe_nonneg hCoupling hMoment)
    (ae_nonlinear_finite_activity control hActivity ν T hCoupling hMoment)

/-- The restriction of the single all-time own-marginal nonlinear process. -/
def globalNonlinearPath (p : Sample (State D) (Jump D)) : Path T (State D) :=
  realPathOrConst T 0 (NonlinearGlobalProcess.process control hActivity ν hCoupling hMoment p)

/-- The finite-horizon trajectory law is genuinely the restriction of the
all-time nonlinear realization, not a different limiting process. -/
theorem ae_globalNonlinearPath_eq_nonlinearPath : ∀ᵐ p ∂law ν.measure (Jump D),
    globalNonlinearPath control hActivity ν T hCoupling hMoment p =
      nonlinearPath control hActivity ν T hCoupling hMoment p := by
  filter_upwards [NonlinearGlobalProcess.ae_process_eq_horizon
    control hActivity ν hCoupling hMoment T T.coe_nonneg] with p hp
  exact realPathOrConst_congr 0 _ _ hp

theorem aemeasurable_globalNonlinearPath :
    AEMeasurable (globalNonlinearPath control hActivity ν T hCoupling hMoment)
      (law ν.measure (Jump D)) := by
  apply (aemeasurable_nonlinearPath control hActivity ν T hCoupling hMoment).congr
  filter_upwards [ae_globalNonlinearPath_eq_nonlinearPath
    control hActivity ν T hCoupling hMoment] with p hp
  exact hp.symm

theorem globalNonlinearPath_map_eq :
    (law ν.measure (Jump D)).map (globalNonlinearPath control hActivity ν T hCoupling hMoment) =
      (law ν.measure (Jump D)).map (nonlinearPath control hActivity ν T hCoupling hMoment) :=
  Measure.map_congr (ae_globalNonlinearPath_eq_nonlinearPath control hActivity ν T hCoupling hMoment)

end Nonlinear
end CarryingCapacity.CanonicalSkorokhodPaths
