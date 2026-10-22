import CarryingCapacity.PrescribedJumpProcess
import CarryingCapacity.ConfigurationTimeDependent

/-!
# The interacting system on prescribed Poisson measures

The initial record and independent standard labelled Poisson measures are the
only supplied randomness. The actual empirical rates discharge all local-rate
and Lyapunov premises of the generic strong construction. The constructed
system is adapted to the usual natural filtration of these supplied inputs.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.PrescribedConfigurationProcess
open ConfigurationLocalization PrescribedPoissonRealization

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N) (initial : A → Configuration N D)
  (M : Label N D → Ω → Measure (ℝ × ℝ)) (ξ : Ω → A)

/-- The actual empirical-rate process, using only the prescribed inputs. -/
def process (ω : Ω) (t : ℝ) : Configuration N D :=
  ConfigurationTimeDependent.process control hN initial (record (Label N D) M ξ ω) t

def preState (ω : Ω) (t : ℝ) : Configuration N D :=
  ConfigurationTimeDependent.preState control hN initial (record (Label N D) M ξ ω) t

/-- The physical accepted increment with the actual empirical environment. -/
def increment (f : Configuration N D → ℝ) (j : Label N D) (T : ℝ)
    (ω : Ω) (z : ℝ × ℝ) : ℝ :=
  if z.1 ∈ Ioc 0 T ∧ z.2 ≤ q.rate j.2 (preState control hN initial M ξ ω z.1 j.1)
      (empiricalLaw κ hN (preState control hN initial M ξ ω z.1))
  then f (jump j (preState control hN initial M ξ ω z.1)) -
    f (preState control hN initial M ξ ω z.1) else 0

local notation "V" => lyapunov control
local notation "hf" => finite_sublevel control hN
local notation "r" => ConfigurationTimeDependent.timeRate κ q hN
local notation "hbnd" => ConfigurationTimeDependent.uniform_rate_bounds control hN
local notation "hr" => ConfigurationTimeDependent.measurable_timeRate (κ := κ) (q := q) hN

variable (hinit : Measurable initial) (hM : ∀ j, Measurable (M j)) (hξ : Measurable ξ)
include hinit hM hξ

theorem measurable_process : Measurable
    (fun p : Ω × ℝ => process control hN initial M ξ p.1 p.2) :=
  PrescribedJumpProcess.measurable_process (Label N D) V hf jump r hbnd initial 0 M ξ hr hinit hM hξ

variable (P : Measure Ω) [IsProbabilityMeasure P]
  (hPoisson : PoissonObservationLaw.HasDisjointLaws P (Label N D) M)
  (hIndependent : IndepFun ξ (fun ω => fun j => M j ω) P)
include hPoisson hIndependent

theorem adapted_process : Adapted
    (UsualFiltration.filtration P
      (PrescribedPoissonFiltration.rawFiltration (Label N D) M ξ hM hξ))
    (fun t ω => process control hN initial M ξ ω t) :=
  PrescribedJumpProcess.adapted_process (Label N D) V hf jump r hbnd initial 0 M ξ
    hr hinit hM hξ P hPoisson hIndependent

variable (μ : Measure A) [IsProbabilityMeasure μ] (hLaw : P.map ξ = μ)
include hLaw

omit hinit [IsProbabilityMeasure μ] in
theorem ae_initial : ∀ᵐ ω ∂P, process control hN initial M ξ ω 0 = initial (ξ ω) :=
  PrescribedJumpProcess.ae_initial (Label N D) V hf jump r hbnd initial 0 M ξ
    hM hξ P hPoisson hIndependent μ hLaw

variable (hV : Integrable (fun a => lyapunov control (initial a)) μ)
include hV


theorem ae_cadlag : ∀ᵐ ω ∂P,
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (process control hN initial M ξ ω) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : Configuration N D,
      Tendsto (process control hN initial M ξ ω) (𝓝[<] t) (𝓝 y)) :=
  PrescribedJumpProcess.ae_cadlag (Label N D) V hf jump r hbnd initial 0 M ξ
    hr hinit hM hξ P hPoisson hIndependent μ hLaw (2 * driftConstant control)
    (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
    (lyapunov_nonnegative control)
    (fun z j t _ => ConfigurationTimeDependent.timeRate_nonnegative hN j t z) hV
    (fun z t _ => ConfigurationTimeDependent.generator_affine_bound control hN z t)

theorem ae_tendsto_preState : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
    Tendsto (process control hN initial M ξ ω) (𝓝[<] t)
      (𝓝 (preState control hN initial M ξ ω t)) :=
  PrescribedJumpProcess.ae_tendsto_preState (Label N D) V hf jump r hbnd initial 0 M ξ
    hr hinit hM hξ P hPoisson hIndependent μ hLaw (2 * driftConstant control)
    (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
    (lyapunov_nonnegative control)
    (fun z j t _ => ConfigurationTimeDependent.timeRate_nonnegative hN j t z) hV
    (fun z t _ => ConfigurationTimeDependent.generator_affine_bound control hN z t)

theorem ae_integrable_increment : ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (f : Configuration N D → ℝ) (j : Label N D),
    Integrable (increment control hN initial M ξ f j T ω) (M j ω) :=
  PrescribedJumpProcess.ae_integrable_increment (Label N D) V hf jump r hbnd initial 0 M ξ
    hr hinit hM hξ P hPoisson hIndependent μ hLaw (2 * driftConstant control)
    (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
    (lyapunov_nonnegative control)
    (fun z j t _ => ConfigurationTimeDependent.timeRate_nonnegative hN j t z) hV
    (fun z t _ => ConfigurationTimeDependent.generator_affine_bound control hN z t)

/-- Every test solves the actual supplied counting equation. -/
theorem ae_counting_identity (f : Configuration N D → ℝ) : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
    f (process control hN initial M ξ ω T) - f (initial (ξ ω)) =
      ∑ j, ∫ z, increment control hN initial M ξ f j T ω z ∂M j ω :=
  PrescribedJumpProcess.ae_counting_identity (Label N D) V hf jump r hbnd initial 0 M ξ
    hr hinit hM hξ P hPoisson hIndependent μ hLaw (2 * driftConstant control)
    (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
    (lyapunov_nonnegative control)
    (fun z j t _ => ConfigurationTimeDependent.timeRate_nonnegative hN j t z) hV
    (fun z t _ => ConfigurationTimeDependent.generator_affine_bound control hN z t) f

theorem ae_finite_activity : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ times : Finset ℝ,
    (times : Set ℝ) ⊆ Ioc 0 T ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
      (∀ u ∈ times, u ∉ Ioc s t) →
        process control hN initial M ξ ω s = process control hN initial M ξ ω t :=
  PrescribedJumpProcess.ae_finite_activity (Label N D) V hf jump r hbnd initial 0 M ξ
    hr hinit hM hξ P hPoisson hIndependent μ hLaw (2 * driftConstant control)
    (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
    (lyapunov_nonnegative control)
    (fun z j t _ => ConfigurationTimeDependent.timeRate_nonnegative hN j t z) hV
    (fun z t _ => ConfigurationTimeDependent.generator_affine_bound control hN z t)

/-- Coordinate equations suffice for pathwise uniqueness on the supplied space. -/
theorem ae_unique_of_coordinate_equations (X : Ω → ℝ → Configuration N D)
    (hcadlag : ∀ᵐ ω ∂P,
      (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (X ω) (Ici t) t) ∧
      (∀ t : ℝ, 0 < t → ∃ y : Configuration N D, Tendsto (X ω) (𝓝[<] t) (𝓝 y)))
    (hzero : ∀ᵐ ω ∂P, X ω 0 = initial (ξ ω))
    (heq : ∀ i : Fin N × Fin D, ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      (X ω T i.1 i.2 : ℝ) - (initial (ξ ω) i.1 i.2 : ℝ) =
        ∑ j, ∫ z, TimeDependentEquationUniqueness.increment jump r
          (Function.leftLim (X ω)) (fun x => (x i.1 i.2 : ℝ)) j T z ∂M j ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → X ω t = process control hN initial M ξ ω t := by
  apply PrescribedJumpProcess.ae_unique_of_separating_equations
    (Label N D) V hf jump r hbnd initial 0 M ξ hr hinit hM hξ P hPoisson hIndependent
    μ hLaw (2 * driftConstant control)
    (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
    (lyapunov_nonnegative control)
    (fun z j t _ => ConfigurationTimeDependent.timeRate_nonnegative hN j t z) hV
    (fun z t _ => ConfigurationTimeDependent.generator_affine_bound control hN z t)
    (fun i : Fin N × Fin D => fun x : Configuration N D => (x i.1 i.2 : ℝ))
    _ X hcadlag hzero heq
  intro x y hxy
  funext i d
  have h : (x i d : ℝ) = (y i d : ℝ) := hxy (i,d)
  exact_mod_cast h

/-- The external realization is the same actual autonomous interacting path
used by the population limit theorems, on one event for all nonnegative times. -/
theorem ae_eq_autonomous : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
    process control hN initial M ξ ω t =
      ConfigurationNonexplosion.process control hN initial (record (Label N D) M ξ ω) t := by
  have h := ConfigurationTimeDependent.ae_process_eq_autonomous control hN initial μ hinit hV
  rw [← hLaw] at h
  exact ae_record (Label N D) M ξ P hM hPoisson hξ hIndependent h

end CarryingCapacity.PrescribedConfigurationProcess
