import CarryingCapacity.NonlinearGlobalProcess
import CarryingCapacity.NonlinearForwardUniqueness
import CarryingCapacity.FiniteJumpForwardRestriction

/-!
# Global nonlinear weak-law existence and uniqueness

A global candidate satisfies the genuine finite-support weak forward equation
and a finite uniform Lyapunov bound on every compact nonnegative interval.
Neither transport continuity nor the exact exponential envelope is assumed.
The actual globally realized nonlinear environment satisfies this definition,
and every candidate agrees with it on the nonnegative half-line. Negative-time
extensions are never identified.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace CarryingCapacity.NonlinearGlobalForward
open LyapunovFlowSpace DeterministicEnvironmentLyapunov

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}

/-- Genuine weak forward equations and finite Lyapunov bounds on every
nonnegative finite horizon. The bound may depend on the horizon. -/
def IsGlobalMomentBoundedSolution (Ψ : State D → ℝ) (q : Rates D (MomentLaw κ D))
    (ν : MomentLaw κ D) (v : ℝ → MomentLaw κ D) : Prop :=
  ∀ T : ℝ, 0 ≤ T → NonlinearForwardUniqueness.IsMomentBoundedSolution Ψ q ν T v

/-- Changing only the negative-time extension preserves the global property.
The congruence transports actual tested time integrability as well as equations. -/
theorem IsGlobalMomentBoundedSolution.congr {Ψ : State D → ℝ} {ν : MomentLaw κ D}
    {v w : ℝ → MomentLaw κ D} (hv : IsGlobalMomentBoundedSolution Ψ q ν v)
    (he : EqOn v w (Ici 0)) : IsGlobalMomentBoundedSolution Ψ q ν w := by
  intro T hT
  obtain ⟨hforward, B, hB, hbound⟩ := hv T hT
  refine ⟨?_, B, hB, ?_⟩
  · apply FiniteJumpForwardRestriction.congr Jump.advance
      (fun j s x => q.rate j x (v s)) (fun j s x => q.rate j x (w s))
      ν.measure (fun s => (v s).measure) (fun s => (w s).measure) T hT hforward
    · intro s hs j x
      rw [he hs.1]
    · intro s hs
      exact congrArg MomentLaw.measure (he hs.1)
  · intro s hs
    rw [← he hs.1]
    exact hbound s hs

variable (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)

local notation "globalLaw" => NonlinearGlobalProcess.environment control hActivity ν hCoupling hMoment

include hActivity hCoupling hMoment

/-- The actual all-time marginal law is a global weak solution. Each compact
interval inherits both its equation and genuine tested integrability from its
already constructed finite-horizon realization. -/
theorem environment_isSolution :
    IsGlobalMomentBoundedSolution control.function q ν globalLaw := by
  intro T hT
  let v := NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment
  have hv := NonlinearForwardUniqueness.environment_isSolution
    control hActivity ν T hT hCoupling hMoment
  have he := NonlinearGlobalProcess.environment_eq_horizon control hActivity ν hCoupling hMoment T hT
  refine ⟨?_, ?_⟩
  · apply FiniteJumpForwardRestriction.congr Jump.advance
      (fun j s x => q.rate j x (v s)) (fun j s x => q.rate j x (globalLaw s))
      ν.measure (fun s => (v s).measure) (fun s => (globalLaw s).measure) T hT hv.1
    · intro s hs j x
      rw [he hs]
    · intro s hs
      exact congrArg MomentLaw.measure (he hs).symm
  · obtain ⟨B, hB, hb⟩ := hv.2
    refine ⟨B, hB, ?_⟩
    intro s hs
    rw [he hs]
    exact hb s hs

/-- Every locally moment-bounded nonlinear weak law agrees with the actual
constructed marginal law at all nonnegative times. -/
theorem solution_eq_environment (v : ℝ → MomentLaw κ D)
    (hv : IsGlobalMomentBoundedSolution control.function q ν v) :
    EqOn v globalLaw (Ici 0) := by
  intro t ht
  have he := NonlinearForwardUniqueness.solution_eq_environment
    control hActivity ν t ht hCoupling hMoment v (hv t ht) (show t ∈ Icc 0 t from ⟨ht, le_rfl⟩)
  exact he.trans (NonlinearGlobalProcess.environment_eq_horizon
    control hActivity ν hCoupling hMoment t ht ⟨ht, le_rfl⟩).symm

/-- Uniqueness compares only nonnegative times, leaving all negative-time
extensions unconstrained. -/
theorem solution_unique (v w : ℝ → MomentLaw κ D)
    (hv : IsGlobalMomentBoundedSolution control.function q ν v)
    (hw : IsGlobalMomentBoundedSolution control.function q ν w) : EqOn v w (Ici 0) := by
  intro t ht
  exact (solution_eq_environment control hActivity ν hCoupling hMoment v hv ht).trans
    (solution_eq_environment control hActivity ν hCoupling hMoment w hw ht).symm

/-- Transport continuity of a global candidate is a consequence of its weak
equations and local moment bounds. -/
theorem continuousOn_solution (v : ℝ → MomentLaw κ D)
    (hv : IsGlobalMomentBoundedSolution control.function q ν v) : ContinuousOn v (Ici 0) := by
  apply (NonlinearGlobalProcess.continuousOn_environment control hActivity ν hCoupling hMoment).congr
  exact solution_eq_environment control hActivity ν hCoupling hMoment v hv

/-- The exact manuscript envelope follows for every global candidate, without
being included in the solution definition. -/
theorem solution_envelope (v : ℝ → MomentLaw κ D)
    (hv : IsGlobalMomentBoundedSolution control.function q ν v)
    (t : ℝ) (ht : 0 ≤ t) :
    lyapunovIntegral control.function (v t) ≤
      ENNReal.ofReal (exponentialEnvelope (∫ x, control.function x ∂ν.measure)
        (driftConstant control) t) :=
  NonlinearForwardUniqueness.solution_envelope control hActivity ν t ht hCoupling hMoment
    v (hv t ht) t ⟨ht, le_rfl⟩

/-- In particular the genuine all-time marginal law satisfies the exact
Lyapunov envelope at every nonnegative time. -/
theorem environment_envelope (t : ℝ) (ht : 0 ≤ t) :
    lyapunovIntegral control.function (globalLaw t) ≤
      ENNReal.ofReal (exponentialEnvelope (∫ x, control.function x ∂ν.measure)
        (driftConstant control) t) :=
  solution_envelope control hActivity ν hCoupling hMoment globalLaw
    (environment_isSolution control hActivity ν hCoupling hMoment) t ht

/-- The actual marginal law supplies global existence and uniqueness in the
whole locally moment-bounded class. -/
theorem exists_solution_and_unique :
    ∃ v : ℝ → MomentLaw κ D, IsGlobalMomentBoundedSolution control.function q ν v ∧
      ∀ w : ℝ → MomentLaw κ D, IsGlobalMomentBoundedSolution control.function q ν w →
        EqOn w v (Ici 0) :=
  ⟨globalLaw, environment_isSolution control hActivity ν hCoupling hMoment,
    fun w hw => solution_eq_environment control hActivity ν hCoupling hMoment w hw⟩

/-- On the nonnegative-time domain the global result is genuine unique
existence, not uniqueness modulo an arbitrary negative-time extension. -/
theorem existsUnique_nonnegative_solution :
    ∃! v : ℝ≥0 → MomentLaw κ D,
      IsGlobalMomentBoundedSolution control.function q ν (fun s => v s.toNNReal) := by
  refine ⟨fun t => globalLaw t, ?_, ?_⟩
  · apply (environment_isSolution control hActivity ν hCoupling hMoment).congr
    intro s hs
    simp only [Real.coe_toNNReal s hs]
  · intro w hw
    funext t
    have he := solution_eq_environment control hActivity ν hCoupling hMoment
      (fun s => w s.toNNReal) hw (show (t : ℝ) ∈ Ici 0 from t.coe_nonneg)
    simpa only [Real.toNNReal_coe] using he

end CarryingCapacity.NonlinearGlobalForward
