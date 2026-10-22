import CarryingCapacity.DeterministicEnvironmentForwardUniqueness
import CarryingCapacity.FiniteJumpForwardRestriction

/-!
# Consistency of nonlinear law curves across construction horizons

Restricting a longer manuscript curve preserves its exact time-specific
Lyapunov envelope. The larger fixed curve's genuine nonlinear weak equation
therefore restricts to the shorter interval. Nonlinear weak-law uniqueness
identifies that restriction with the smaller fixed curve.

These statements concern the actual laws and their environmental values on
overlapping construction intervals. They make no pathwise identification of
the independently selected finite-horizon realizations.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace CarryingCapacity.NonlinearHorizonConsistency
open CommonInitialNoise LyapunovFlowSpace DeterministicEnvironmentLyapunov

variable {D : ℕ} {κ : MomentScale}

/-- Restriction preserves the exact manuscript envelope, whose value at a
given time does not depend on the final construction horizon. -/
def restrictCurve {Ψ : State D → ℝ} {ν : MomentLaw κ D} {C S T : ℝ}
    {hS : 0 ≤ S} {hT : 0 ≤ T} (hST : S ≤ T)
    (w : ManuscriptCurves Ψ ν C T hT) : ManuscriptCurves Ψ ν C S hS := by
  let inclusion : C(Icc (0 : ℝ) S, Icc (0 : ℝ) T) :=
    ⟨fun t => ⟨t, t.property.1, t.property.2.trans hST⟩,
      continuous_subtype_val.subtype_mk _⟩
  refine ⟨w.val.comp inclusion, ?_, ?_⟩
  · exact w.property.1
  · intro t
    exact w.property.2 (inclusion t)

theorem restrictCurve_apply {Ψ : State D → ℝ} {ν : MomentLaw κ D} {C S T : ℝ}
    {hS : 0 ≤ S} {hT : 0 ≤ T} (hST : S ≤ T)
    (w : ManuscriptCurves Ψ ν C T hT) (t : Icc (0 : ℝ) S) :
    (restrictCurve (hS := hS) hST w).val t =
      w.val ⟨t, t.property.1, t.property.2.trans hST⟩ := rfl

variable {q : Rates D (MomentLaw κ D)} (control : LyapunovControl κ q)
  (ν : MomentLaw κ D) (C S T : ℝ) (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T)

/-- Endpoint extensions of a curve and its restriction agree on the smaller
original interval; no agreement beyond that interval is asserted. -/
theorem restriction_extension_eq (w : ManuscriptCurves control.function ν C T hT)
    (t : ℝ) (ht : t ∈ Icc 0 S) :
    manuscriptExtension control ν C S hS (restrictCurve hST w) t =
      manuscriptExtension control ν C T hT w t := by
  calc
    _ = (restrictCurve hST w).val ⟨t,ht⟩ :=
      manuscriptExtension_eq control ν C S hS _ ⟨t,ht⟩
    _ = w.val ⟨t,ht.1,ht.2.trans hST⟩ := rfl
    _ = _ := (manuscriptExtension_eq control ν C T hT w ⟨t,ht.1,ht.2.trans hST⟩).symm

omit C
variable (hActivity : MomentActivityBound κ q) (hCoupling : MomentCouplingBound κ q)
  (hInitial : Integrable control.function ν.measure)

/-- The restriction of the already constructed larger fixed curve solves the
nonlinear weak equation on the smaller interval, including true tested time
integrability. This is inherited from the proved larger-horizon equation. -/
theorem restricted_fixedCurve_isSolution :
    let w := restrictCurve (hS := hS) hST
      (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hInitial)
    FiniteJumpForward.IsSolution Jump.advance
      (DeterministicEnvironmentForward.originalRate control ν S hS w) ν.measure
      (fun t => (manuscriptExtension control ν (driftConstant control) S hS w t).measure) S := by
  let w := restrictCurve (hS := hS) hST
    (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hInitial)
  apply FiniteJumpForwardRestriction.restrict_congr Jump.advance
    (fun j t x => q.rate j x (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hInitial t))
    (DeterministicEnvironmentForward.originalRate control ν S hS w) ν.measure
    (fun t => (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hInitial t).measure)
    (fun t => (manuscriptExtension control ν (driftConstant control) S hS w t).measure)
    S T hS hST
    (DeterministicEnvironmentForward.nonlinear_isSolution control hActivity ν T hT hCoupling hInitial)
  · intro t ht j x
    change q.rate j x (manuscriptExtension control ν (driftConstant control) T hT
      (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hInitial) t) =
      q.rate j x (manuscriptExtension control ν (driftConstant control) S hS w t)
    exact congrArg (q.rate j x) (restriction_extension_eq control ν (driftConstant control)
      S T hS hT hST _ t ht).symm
  · intro t ht
    exact congrArg MomentLaw.measure (restriction_extension_eq control ν (driftConstant control)
      S T hS hT hST _ t ht).symm

/-- The longer fixed curve restricted to the smaller interval is exactly the
fixed curve constructed there, by the proved nonlinear weak-law uniqueness. -/
theorem restrict_fixedCurve_eq :
    restrictCurve (hS := hS) hST
      (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hInitial) =
      NonlinearFixedPoint.fixedCurve control hActivity ν S hS hCoupling hInitial :=
  DeterministicEnvironmentForwardUniqueness.nonlinear_solution_eq_fixedCurve
    control hActivity ν S hS hCoupling hInitial _
    (restricted_fixedCurve_isSolution control ν S T hS hT hST hActivity hCoupling hInitial)

/-- The actual fixed law values coincide throughout the overlap, including
both endpoints and a zero construction horizon. -/
theorem fixedCurve_eq_on_overlap (t : ℝ) (ht : t ∈ Icc 0 S) :
    (NonlinearFixedPoint.fixedCurve control hActivity ν S hS hCoupling hInitial).val ⟨t,ht⟩ =
      (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hInitial).val
        ⟨t,ht.1,ht.2.trans hST⟩ := by
  have he := congrArg (fun w : ManuscriptCurves control.function ν (driftConstant control) S hS =>
    w.val ⟨t,ht⟩) (restrict_fixedCurve_eq control ν S T hS hT hST hActivity hCoupling hInitial)
  exact he.symm

include hST

/-- The deterministic nonlinear environments agree on the smaller original
interval, although their endpoint extensions may differ afterward. -/
theorem environment_eq_on_overlap :
    EqOn (NonlinearFixedPoint.environment control hActivity ν S hS hCoupling hInitial)
      (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hInitial) (Icc 0 S) := by
  intro t ht
  unfold NonlinearFixedPoint.environment
  rw [← restrict_fixedCurve_eq control ν S T hS hT hST hActivity hCoupling hInitial]
  exact restriction_extension_eq control ν (driftConstant control) S T hS hT hST _ t ht

/-- The actual constructed process marginals are consistent across horizons.
This asserts equality of probability laws, not equality of sample paths. -/
theorem process_marginals_eq_on_overlap (t : ℝ) (ht : t ∈ Icc 0 S) :
    (law ν.measure (Jump D)).map
      (fun p => NonlinearFixedPoint.process control hActivity ν S hS hCoupling hInitial p t) =
      (law ν.measure (Jump D)).map
        (fun p => NonlinearFixedPoint.process control hActivity ν T hT hCoupling hInitial p t) := by
  rw [← NonlinearFixedPoint.environment_measure_eq_marginal control hActivity ν S hS hCoupling hInitial ⟨t,ht⟩,
    ← NonlinearFixedPoint.environment_measure_eq_marginal control hActivity ν T hT hCoupling hInitial
      ⟨t,ht.1,ht.2.trans hST⟩]
  exact congrArg MomentLaw.measure (environment_eq_on_overlap control ν S T hS hT hST hActivity hCoupling hInitial ht)

end CarryingCapacity.NonlinearHorizonConsistency
