import CarryingCapacity.TimeDependentForwardUniqueness
import CarryingCapacity.DeterministicEnvironmentForward
import CarryingCapacity.DeterministicEnvironmentGeneralForward

/-!
# Uniqueness of prescribed-environment and nonlinear forward laws

The actual prescribed-environment construction has exhaustive exits under
the proved Lyapunov bounds. Finite predecessor geometry and coefficient
continuity therefore identify its law with every probability-valued weak
forward solution. No Lyapunov moment is required of the competing law.

For a self-consistent candidate in the manuscript's continuous Lyapunov curve
space, linear law identification makes that candidate a fixed point of the
actual evolution. The proved fixed-point uniqueness then gives uniqueness
of the nonlinear weak forward solution in that curve space. All statements
concern the original interval `[0,T]`, not an arbitrary continuation outside it.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace CarryingCapacity.DeterministicEnvironmentForwardUniqueness
open CommonInitialNoise LyapunovFlowSpace DeterministicEnvironmentLyapunov
open DeterministicEnvironmentFrozen DeterministicEnvironmentProcess

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}

/-- Original and clamped coefficients give the same genuine weak-solution
class on the construction interval, including time integrability. -/
theorem isSolution_clamped_of_original
    (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T)
    (α : Measure (State D)) (p : ℝ → Measure (State D))
    (hp : FiniteJumpForward.IsSolution Jump.advance (fun j s x => q.rate j x (v s)) α p T) :
    FiniteJumpForward.IsSolution Jump.advance (timeRate κ q v T) α p T := by
  have he (f : State D → ℝ) (s : ℝ) (hs : s ∈ Icc 0 T) (x : State D) :
      FiniteJumpForward.generator Jump.advance (fun j s x => q.rate j x (v s)) f s x =
      FiniteJumpForward.generator Jump.advance (timeRate κ q v T) f s x := by
    simp only [FiniteJumpForward.generator, timeRate_eq κ q v T _ s hs]
  refine ⟨hp.probability, ?_, ?_⟩
  · intro f hf
    apply (hp.integrable f hf).congr
    rw [uIoc_of_le hT]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    apply integral_congr_ae
    exact Eventually.of_forall (he f s ⟨hs.1.le, hs.2⟩)
  · intro f hf t ht
    rw [hp.equation f hf t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    apply integral_congr_ae
    exact Eventually.of_forall (he f s ⟨hs.1, hs.2.trans ht.2⟩)

/-- Continuity of every clamped rate on the actual interval is derived
from the paper's coupling assumption and prescribed curve continuity. -/
theorem continuousOn_clampedRate (hCoupling : MomentCouplingBound κ q)
    (v : ℝ → MomentLaw κ D) (T : ℝ) (hv : ContinuousOn v (Icc 0 T))
    (j : Jump D) (x : State D) :
    ContinuousOn (fun s => timeRate κ q v T j s x) (Icc 0 T) := by
  apply (DeterministicEnvironmentRates.continuousOn_timeRate κ q hCoupling v T hv j x).congr
  intro s hs
  exact timeRate_eq κ q v T j s hs x

variable (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T)
  (hv : ContinuousOn v (Icc 0 T)) (hCoupling : MomentCouplingBound κ q)
  (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ s ∈ Icc 0 T, lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
  (hInitial : Integrable control.function ν.measure)
include hActivity hT hv hCoupling hB hEnv hInitial

/-- Any probability weak forward solution in a prescribed continuous
environment is the actual common-noise marginal. The candidate has no
moment-bound hypothesis. Nonexplosion is discharged by the construction. -/
theorem law_eq_solution (p : ℝ → Measure (State D))
    (hp : FiniteJumpForward.IsSolution Jump.advance (fun j s x => q.rate j x (v s)) ν.measure p T)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (law ν.measure (Jump D)).map
      (fun a => DeterministicEnvironmentProcess.process control hActivity v T hT hv id a t) = p t := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact TimeDependentForwardUniqueness.globalLaw_eq_solution control.function
    (finite_sublevels control) Jump.advance (timeRate κ q v T)
    (exists_uniform_rate_bounds control v T hT hActivity hv) 0 ν.measure
    (DeterministicEnvironmentFrozen.measurable_timeRate κ q v T hv hCoupling hT)
    DeterministicEnvironmentFiniteSupport.finite_advance_fiber
    (fun j s x _ => timeRate_nonnegative κ q v T j s x)
    (DeterministicEnvironmentProcess.ae_exhaustive control hActivity v T hT hv id ν.measure
      hCoupling measurable_id B hB hEnv hInitial)
    T hT (continuousOn_clampedRate hCoupling v T hv) p
    (isSolution_clamped_of_original v T hT ν.measure p hp) t ht

/-- Two probability-valued weak forward solutions coincide on the entire
prescribed interval, with no moment assumption on either candidate. -/
theorem solution_unique (p r : ℝ → Measure (State D))
    (hp : FiniteJumpForward.IsSolution Jump.advance (fun j s x => q.rate j x (v s)) ν.measure p T)
    (hr : FiniteJumpForward.IsSolution Jump.advance (fun j s x => q.rate j x (v s)) ν.measure r T) :
    EqOn p r (Icc 0 T) := by
  intro t ht
  exact (law_eq_solution control hActivity ν v T hT hv hCoupling B hB hEnv hInitial p hp t ht).symm.trans
    (law_eq_solution control hActivity ν v T hT hv hCoupling B hB hEnv hInitial r hr t ht)

/-- General prescribed-environment existence and uniqueness: the actual
process law solves the original weak equation and every probability weak
solution agrees with it on `[0,T]`. The environment need not be a manuscript
curve and need not start from the process's separately prescribed initial law. -/
theorem actualLaw_isSolution_and_unique :
    FiniteJumpForward.IsSolution Jump.advance (fun j s x => q.rate j x (v s)) ν.measure
      (DeterministicEnvironmentGeneralForward.actualLaw control hActivity v T hT hv ν) T ∧
    ∀ p : ℝ → Measure (State D),
      FiniteJumpForward.IsSolution Jump.advance (fun j s x => q.rate j x (v s)) ν.measure p T →
      EqOn (DeterministicEnvironmentGeneralForward.actualLaw control hActivity v T hT hv ν) p (Icc 0 T) :=
  ⟨DeterministicEnvironmentGeneralForward.isSolution control hActivity v T hT hv ν
      hCoupling B hB hEnv hInitial,
    fun p hp t ht => law_eq_solution control hActivity ν v T hT hv hCoupling B hB hEnv hInitial p hp t ht⟩

section Manuscript
omit v hv B hB hEnv hInitial
variable (w : ManuscriptCurves control.function ν (driftConstant control) T hT)

/-- Membership of the prescribed environment in the manuscript curve space
supplies all environmental and initial moment bounds used in uniqueness. -/
theorem manuscript_law_eq_solution (p : ℝ → Measure (State D))
    (hp : FiniteJumpForward.IsSolution Jump.advance
      (DeterministicEnvironmentForward.originalRate control ν T hT w) ν.measure p T)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    DeterministicEnvironmentForward.lawCurve control hActivity ν T hT w t = p t :=
  law_eq_solution control hActivity ν
    (manuscriptExtension control ν (driftConstant control) T hT w) T hT
    (continuous_manuscriptExtension control ν (driftConstant control) T hT w).continuousOn
    hCoupling (manuscriptBound control ν (driftConstant control) T)
    (manuscriptBound_nonnegative control ν (driftConstant control) T (driftConstant_nonnegative control) hT)
    (fun s _ => manuscriptExtension_bound control ν (driftConstant control) T
      (driftConstant_nonnegative control) hT w s)
    (manuscript_initial_integrable control ν T hT w) p hp t ht

/-- Existence is furnished by the actual process and uniqueness holds
against every probability weak solution, not just moment-controlled ones. -/
theorem manuscript_isSolution_and_unique :
    FiniteJumpForward.IsSolution Jump.advance
      (DeterministicEnvironmentForward.originalRate control ν T hT w) ν.measure
      (DeterministicEnvironmentForward.lawCurve control hActivity ν T hT w) T ∧
    ∀ p : ℝ → Measure (State D),
      FiniteJumpForward.IsSolution Jump.advance
        (DeterministicEnvironmentForward.originalRate control ν T hT w) ν.measure p T →
      EqOn (DeterministicEnvironmentForward.lawCurve control hActivity ν T hT w) p (Icc 0 T) :=
  ⟨DeterministicEnvironmentForward.isSolution control hActivity ν T hT w hCoupling,
    fun p hp t ht => manuscript_law_eq_solution control hActivity ν T hT hCoupling w p hp t ht⟩

/-- A nonlinear weak forward solution in the manuscript curve class is a
fixed point of the actual stochastic evolution, by linear law uniqueness. -/
theorem evolution_eq_of_nonlinear_isSolution
    (hw : FiniteJumpForward.IsSolution Jump.advance
      (DeterministicEnvironmentForward.originalRate control ν T hT w) ν.measure
      (fun s => (manuscriptExtension control ν (driftConstant control) T hT w s).measure) T) :
    DeterministicEnvironmentEvolution.evolution control hActivity ν T hT w hCoupling = w := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  apply MomentLaw.ext
  rw [DeterministicEnvironmentEvolution.evolution_measure]
  have he := manuscript_law_eq_solution control hActivity ν T hT hCoupling w
    (fun s => (manuscriptExtension control ν (driftConstant control) T hT w s).measure) hw t t.property
  dsimp only at he
  rw [manuscriptExtension_eq] at he
  exact he

include hInitial in
/-- Full weak-equation uniqueness within the manuscript curve space now
follows from actual forward-law identification and the checked Banach theorem. -/
theorem nonlinear_solution_eq_fixedCurve
    (hw : FiniteJumpForward.IsSolution Jump.advance
      (DeterministicEnvironmentForward.originalRate control ν T hT w) ν.measure
      (fun s => (manuscriptExtension control ν (driftConstant control) T hT w s).measure) T) :
    w = NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hInitial :=
  NonlinearFixedPoint.fixedCurve_unique control hActivity ν T hT hCoupling hInitial w
    (evolution_eq_of_nonlinear_isSolution control hActivity ν T hT hCoupling w hw)

omit w in
include hInitial in
/-- The actual nonlinear weak forward equation has exactly one solution
in the manuscript's continuous Lyapunov curve space. -/
theorem existsUnique_nonlinear_solution :
    ∃! w : ManuscriptCurves control.function ν (driftConstant control) T hT,
      FiniteJumpForward.IsSolution Jump.advance
        (DeterministicEnvironmentForward.originalRate control ν T hT w) ν.measure
        (fun s => (manuscriptExtension control ν (driftConstant control) T hT w s).measure) T := by
  refine ⟨NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hInitial,
    DeterministicEnvironmentForward.nonlinear_isSolution control hActivity ν T hT hCoupling hInitial, ?_⟩
  intro w hw
  exact nonlinear_solution_eq_fixedCurve control hActivity ν T hT hCoupling hInitial w hw

end Manuscript
end CarryingCapacity.DeterministicEnvironmentForwardUniqueness
