import CarryingCapacity.PrescribedCountingKernel
import CarryingCapacity.RateTableSumCompensation
import CarryingCapacity.DeterministicEnvironmentRates

/-!
# Random-environment compensation for the specified Poisson measures

The input noise consists of independent specified PRMs and an independent
initial record. The states and environments may be arbitrary adapted càdlàg
processes in the usual natural filtration. Scalar-rate-table encoding avoids
adding a Polish-space assumption on the original environment space. The
primitive intensity and future independence conclusions are supplied by the
actual Poisson construction, not assumed as compensator hypotheses.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal NNReal BigOperators

namespace CarryingCapacity.PrescribedRandomEnvironmentCompensation
open PrescribedPoissonFiltration RandomEnvironmentCompensation

variable {Ω A E V : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace A]
  [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
  [Countable E] [MeasurableSingletonClass E] [DiscreteTopology E]
  [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  (J : Type) [Fintype J] (M : J → Ω → Measure (ℝ × ℝ)) (ξ : Ω → A)
  (P : Measure Ω) [IsProbabilityMeasure P]
  (hM : ∀ j, Measurable (M j)) (hPoisson : PoissonObservationLaw.HasDisjointLaws P J M)
  (hξ : Measurable ξ) (hIndependent : IndepFun ξ (fun ω j => M j ω) P)

variable (jump : J → E → E) (q : J → E → V → ℝ)
  (X Y : ℝ → Ω → E) (U W : ℝ → Ω → V) (e : E)
  (hq : ∀ j x, Continuous (q j x))
  (hX : ∀ s, 0 ≤ s → Measurable[(UsualFiltration.filtration P (rawFiltration J M ξ hM hξ)) s] (X s))
  (hY : ∀ s, 0 ≤ s → Measurable[(UsualFiltration.filtration P (rawFiltration J M ξ hM hξ)) s] (Y s))
  (hU : ∀ s, 0 ≤ s → Measurable[(UsualFiltration.filtration P (rawFiltration J M ξ hM hξ)) s] (U s))
  (hW : ∀ s, 0 ≤ s → Measurable[(UsualFiltration.filtration P (rawFiltration J M ξ hM hξ)) s] (W s))
  (τ : Ω → ℝ≥0∞)
  (hτ : ∀ s : ℝ, 0 ≤ s → MeasurableSet[(UsualFiltration.filtration P (rawFiltration J M ξ hM hξ)) s] {ω | τ ω ≤ ENNReal.ofReal s})
  (hnonneg : ∀ j x u, 0 ≤ q j x u)
  (hcX : ∀ᵐ ω ∂P, CadlagNonnegative (fun t => X t ω))
  (hcY : ∀ᵐ ω ∂P, CadlagNonnegative (fun t => Y t ω))
  (hcU : ∀ᵐ ω ∂P, CadlagNonnegative (fun t => U t ω))
  (hcW : ∀ᵐ ω ∂P, CadlagNonnegative (fun t => W t ω))
include hPoisson hIndependent hq hX hY hU hW hτ hnonneg hcX hcY hcU hcW

/-- Exact stopped compensation for each actual supplied label. It includes
the stopping-time jump, retains shared jumps, and allows infinite values. -/
theorem expected_stoppedField_eq_currentActivity (ρ : E → E → ℝ) (j : J) (T : ℝ) :
    (∫⁻ ω, ∫⁻ z, ENNReal.ofReal
      (RateTableCompensation.stoppedField jump q X Y U W e τ ρ j T (ω,z))
      ∂M j ω ∂UsualFiltration.completedLaw P) =
      ∫⁻ ω, ∫⁻ t in Ioc 0 T, if ENNReal.ofReal t ≤ τ ω then
        ENNReal.ofReal (currentActivity jump q X Y U W ρ j ω t) else 0
        ∂MarkedIntensity.positiveVolume ∂UsualFiltration.completedLaw P := by
  let K : @Kernel Ω (ℝ × ℝ) (UsualFiltration.completedSpace P) inferInstance := PrescribedCountingKernel.countingKernel J M P hM j
  have hmean := PrescribedCountingKernel.hasIntensity J M P hM hPoisson j
  have hind := PrescribedCountingKernel.futureCountsIndependent J M P hM hPoisson ξ hξ hIndependent j
  have he : ∀ᵐ ω ∂UsualFiltration.completedLaw P, K ω = M j ω :=
    (PrescribedCountingKernel.ae_countingKernel_eq J M P hM hPoisson).mono (fun ω hω => hω j)
  have hh := @RateTableCompensation.expected_stoppedField_eq_currentActivity
    Ω E V J (UsualFiltration.completedSpace P) _ _ _ _ _ _ _ _ _ _ _
    (UsualFiltration.filtration P (rawFiltration J M ξ hM hξ)) jump q X Y U W e hq hX hY hU hW (UsualFiltration.completedLaw P) _ K _ hmean hind τ hτ hnonneg hcX hcY hcU hcW ρ j T
  refine (lintegral_congr_ae ?_).trans hh
  filter_upwards [he] with ω hω
  rw [hω]

/-- Exact aggregate compensation against the original specified random measures.
The activity is the sum of all shared and one-sided positive jump terms. -/
theorem expected_sum_stoppedField_eq_currentActivity (ρ : E → E → ℝ) (T : ℝ) :
    (∫⁻ ω, ∑ j, ∫⁻ z, ENNReal.ofReal
      (RateTableCompensation.stoppedField jump q X Y U W e τ ρ j T (ω,z))
      ∂M j ω ∂UsualFiltration.completedLaw P) =
      ∫⁻ ω, ∫⁻ t in Ioc 0 T, if ENNReal.ofReal t ≤ τ ω then
        ENNReal.ofReal (∑ j, currentActivity jump q X Y U W ρ j ω t) else 0
        ∂MarkedIntensity.positiveVolume ∂UsualFiltration.completedLaw P := by
  let K : J → @Kernel Ω (ℝ × ℝ) (UsualFiltration.completedSpace P) inferInstance :=
    PrescribedCountingKernel.countingKernel J M P hM
  have hh := @RateTableSumCompensation.expected_sum_stoppedField_eq_currentActivity
    Ω E V J (UsualFiltration.completedSpace P) _ _ _ _ _ _ _ _ _ _ _
    (UsualFiltration.filtration P (rawFiltration J M ξ hM hξ)) jump q X Y U W e
    hq hX hY hU hW (UsualFiltration.completedLaw P) _ K _
    (PrescribedCountingKernel.hasIntensity J M P hM hPoisson)
    (PrescribedCountingKernel.futureCountsIndependent J M P hM hPoisson ξ hξ hIndependent)
    τ hτ hnonneg hcX hcY hcU hcW ρ T
  refine (lintegral_congr_ae ?_).trans hh
  filter_upwards [PrescribedCountingKernel.ae_countingKernel_eq J M P hM hPoisson] with ω hω
  exact Finset.sum_congr rfl (fun j _ => by rw [show K j ω = M j ω from hω j])

end CarryingCapacity.PrescribedRandomEnvironmentCompensation
