import CarryingCapacity.NonlinearGlobalForward

/-!
# Lyapunov envelopes for any supplied admissible drift constant

The drift hypothesis retains its witness as data. Replacing that witness
does not change the Lyapunov function or the rate assumptions. Consequently
the uniqueness theorem gives the exact exponential envelope for any chosen
admissible constant, including for a law already constructed with another one.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CarryingCapacity.LyapunovControl

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}

/-- Use an explicitly supplied admissible constant with the same Lyapunov function. -/
def withDriftConstant (control : LyapunovControl κ q) (C : ℝ) (hC : 0 ≤ C)
    (hDrift : ∀ x (μ : MomentLaw κ D), Integrable control.function μ.measure →
      q.generator μ control.function x ≤
        C * (1 + control.function x + ∫ y, control.function y ∂μ.measure)) :
    LyapunovControl κ q :=
  { control with drift := ⟨C, hC, hDrift⟩ }

end CarryingCapacity.LyapunovControl

namespace CarryingCapacity.ExplicitLyapunovConstant
open LyapunovFlowSpace

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (C : ℝ) (hC : 0 ≤ C)
  (hDrift : ∀ x (μ : MomentLaw κ D), Integrable control.function μ.measure →
    q.generator μ control.function x ≤
      C * (1 + control.function x + ∫ y, control.function y ∂μ.measure))

@[simp] theorem function_withDriftConstant :
    (control.withDriftConstant C hC hDrift).function = control.function := rfl

@[simp] theorem configuration_driftConstant :
    ConfigurationLocalization.driftConstant (control.withDriftConstant C hC hDrift) = C := rfl

@[simp] theorem environment_driftConstant :
    DeterministicEnvironmentLyapunov.driftConstant
      (control.withDriftConstant C hC hDrift) = C := rfl

variable (hActivity : MomentActivityBound κ q) (ν : MomentLaw κ D)
  (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)

include hC hDrift hActivity hT hCoupling hMoment in
/-- Equations (4.6)/(4.10) for the specified constant `C`, for every solution
in the paper's moment class. No comparison with a choice-selected constant is needed. -/
theorem solution_envelope (v : ℝ → MomentLaw κ D)
    (hv : NonlinearForwardUniqueness.IsMomentBoundedSolution control.function q ν T v)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    lyapunovIntegral control.function (v t) ≤
      ENNReal.ofReal (exponentialEnvelope (∫ x, control.function x ∂ν.measure) C t) := by
  exact NonlinearForwardUniqueness.solution_envelope
    (control.withDriftConstant C hC hDrift) hActivity ν T hT hCoupling hMoment v hv t ht

include hC hDrift in
/-- The law originally constructed from `control` obeys the envelope for any
other admissible constant; rebuilding the law is not a premise. -/
theorem environment_envelope (t : ℝ) (ht : t ∈ Icc 0 T) :
    lyapunovIntegral control.function
      (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment t) ≤
      ENNReal.ofReal (exponentialEnvelope (∫ x, control.function x ∂ν.measure) C t) :=
  solution_envelope control C hC hDrift hActivity ν T hT hCoupling hMoment _
    (NonlinearForwardUniqueness.environment_isSolution
      control hActivity ν T hT hCoupling hMoment) t ht

end CarryingCapacity.ExplicitLyapunovConstant
