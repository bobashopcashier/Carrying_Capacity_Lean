import CarryingCapacity.PrescribedNonlinearProcess
import CarryingCapacity.FiniteHorizonCountingUniqueness

/-!
# Uniqueness on the exact finite horizon of Corollary 4.4

A competing solution needs its coordinate equations only on `[0,T]` and
right continuity only before the terminal time. No equations or regularity
beyond the requested horizon, or extra candidate moment bound, are assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology BigOperators NNReal

namespace CarryingCapacity.PrescribedNonlinearFiniteHorizon
open PrescribedNonlinearProcess

variable {Ω : Type*} [MeasurableSpace Ω]
  {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)
  (M : Jump D → Ω → Measure (ℝ × ℝ)) (ξ : Ω → State D)
  (hM : ∀ j, Measurable (M j)) (hξ : Measurable ξ)
  (P : Measure Ω) [IsProbabilityMeasure P]
  (hPoisson : PoissonObservationLaw.HasDisjointLaws P (Jump D) M)
  (hIndependent : IndepFun ξ (fun ω => fun j => M j ω) P)
  (hLaw : P.map ξ = ν.measure)

local notation "X" => process control hActivity ν hCoupling hMoment M ξ
local notation "Z" => preState control hActivity ν hCoupling hMoment M ξ
local notation "v" => NonlinearGlobalProcess.environment control hActivity ν hCoupling hMoment

include hM hξ hPoisson hIndependent hLaw

/-- Exact finite-horizon pathwise uniqueness for the nonlinear environment
identified in the manuscript's well-posedness theorem. -/
theorem ae_unique_on_horizon (T : ℝ) (Y : Ω → ℝ → State D)
    (hcadlag : ∀ᵐ ω ∂P,
      (∀ t ∈ Ico 0 T, ContinuousWithinAt (Y ω) (Ici t) t) ∧
      (∀ t ∈ Ioc 0 T, ∃ y : State D, Tendsto (Y ω) (𝓝[<] t) (𝓝 y)))
    (hzero : ∀ᵐ ω ∂P, Y ω 0 = ξ ω)
    (heq : ∀ i : Fin D, ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 T,
      (Y ω t i : ℝ) - (ξ ω i : ℝ) =
        ∑ j, ∫ z, TimeDependentEquationUniqueness.increment Jump.advance
          (fun j s x => q.rate j x (v s)) (Function.leftLim (Y ω))
          (fun x => (x i : ℝ)) j t z ∂M j ω) :
    ∀ᵐ ω ∂P, EqOn (Y ω) (X ω) (Icc 0 T) := by
  have hactual := ae_all_iff.mpr (fun i : Fin D => ae_counting_identity
    control hActivity ν hCoupling hMoment M ξ hM hξ P hPoisson hIndependent hLaw
    (fun x => (x i : ℝ)))
  filter_upwards [hcadlag,hzero,ae_all_iff.mpr heq,
    ae_cadlag control hActivity ν hCoupling hMoment M ξ hM hξ P hPoisson hIndependent hLaw,
    ae_initial control hActivity ν hCoupling hMoment M ξ hM hξ P hPoisson hIndependent hLaw,
    ae_tendsto_preState control hActivity ν hCoupling hMoment M ξ hM hξ P hPoisson hIndependent hLaw,
    hactual] with ω hc hz hEq ha hazero hapre haEq
  have hxpre : ∀ t ∈ Ioc 0 T,
      Tendsto (Y ω) (𝓝[<] t) (𝓝 (Function.leftLim (Y ω) t)) := by
    intro t ht
    obtain ⟨y,hy⟩ := hc.2 t ht
    rw [leftLim_eq_of_tendsto (neBot_iff.mp inferInstance) hy]
    exact hy
  apply FiniteHorizonCountingUniqueness.eqOn_of_separating_counting_equations
    (fun i : Fin D => fun x : State D => (x i : ℝ))
    (fun x y hxy => by
      funext i
      have h : (x i : ℝ) = (y i : ℝ) := hxy i
      exact_mod_cast h)
    Jump.advance (fun j s x => q.rate j x (v s)) (fun j => M j ω) (Y ω) (X ω)
    (Function.leftLim (Y ω)) (Z ω) T hc.1 (fun t ht => ha.1 t ht.1)
    hxpre (fun t ht => hapre t ht.1) (hz.trans hazero.symm)
  · intro i t ht
    rw [hz]
    exact hEq i t ht
  · intro i t ht
    rw [hazero]
    exact haEq i ⟨t,ht.1⟩

end CarryingCapacity.PrescribedNonlinearFiniteHorizon
