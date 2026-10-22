import CarryingCapacity.PrescribedJumpProcess
import CarryingCapacity.PrescribedObservableLaws
import CarryingCapacity.DeterministicEnvironmentGeneralLaw
import CarryingCapacity.DeterministicEnvironmentForwardUniqueness
import CarryingCapacity.GlobalLyapunovExit

/-!
# Proposition 4.2 on a specified Poisson probability space

The independent specified initial variable and PRMs determine the strong path
without additional randomness. The canonical input-law identity transfers the
proved path properties, genuine moments and continuous marginal curve. The
original-rate forward equation and its uniqueness are conclusions of that
construction, not hypotheses on the resulting marginals.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal NNReal BigOperators

namespace CarryingCapacity.PrescribedDeterministicEnvironment
open PrescribedPoissonRealization DeterministicEnvironmentLyapunov DeterministicEnvironmentFrozen

variable {Ω : Type*} [MeasurableSpace Ω]
  {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))
  (M : Jump D → Ω → Measure (ℝ × ℝ)) (ξ : Ω → State D)

local notation "bounds" => exists_uniform_rate_bounds control v T hT hActivity hv
local notation "rate" => timeRate κ q v T
local notation "rec" => record (Jump D) M ξ

def process (ω : Ω) (t : ℝ) : State D :=
  DeterministicEnvironmentProcess.process control hActivity v T hT hv id (rec ω) t

def preState (ω : Ω) (t : ℝ) : State D :=
  DeterministicEnvironmentProcess.preState control hActivity v T hT hv id (rec ω) t

def increment (f : State D → ℝ) (j : Jump D) (S : ℝ) (ω : Ω) (z : ℝ × ℝ) : ℝ :=
  TimeDependentEquationUniqueness.increment Jump.advance rate
    (preState control hActivity v T hT hv M ξ ω) f j S z

local notation "X" => process control hActivity v T hT hv M ξ
local notation "Z" => preState control hActivity v T hT hv M ξ
local notation "H" => increment control hActivity v T hT hv M ξ

omit [MeasurableSpace Ω] in
/-- On the original horizon the accepted integrand uses exactly the given
unclamped environment, including jumps at its terminal time. -/
theorem increment_eq_original (f : State D → ℝ) (j : Jump D) (S : ℝ)
    (hST : S ≤ T) (ω : Ω) (z : ℝ × ℝ) :
    H f j S ω z = TimeDependentEquationUniqueness.increment Jump.advance
      (fun j s x => q.rate j x (v s)) (Z ω) f j S z := by
  by_cases hz : z.1 ∈ Ioc 0 S
  · simp only [increment, TimeDependentEquationUniqueness.increment,
      timeRate_eq κ q v T j z.1 ⟨hz.1.le, hz.2.trans hST⟩]
  · simp only [increment, TimeDependentEquationUniqueness.increment, hz, false_and, if_false]

variable (hCoupling : MomentCouplingBound κ q)
  (hM : ∀ j, Measurable (M j)) (hξ : Measurable ξ)
include hCoupling hM hξ

section JointMeasurability
attribute [local irreducible] PrescribedPoissonRealization.record DeterministicEnvironmentProcess.process

theorem measurable_process : Measurable (fun p : Ω × ℝ => X p.1 p.2) := by
  have hp : Measurable (fun p : Ω × ℝ => (rec p.1,p.2)) :=
    ((measurable_record (Jump D) M ξ hM hξ).comp measurable_fst).prodMk measurable_snd
  exact (DeterministicEnvironmentProcess.measurable_process control hActivity v T hT hv id
    hCoupling measurable_id).comp hp

end JointMeasurability

variable (P : Measure Ω) [IsProbabilityMeasure P]
  (hPoisson : PoissonObservationLaw.HasDisjointLaws P (Jump D) M)
  (hIndependent : IndepFun ξ (fun ω j => M j ω) P)
include hPoisson hIndependent

/-- Adaptedness uses the completed right-continuous natural input filtration. -/
theorem adapted_process : Adapted
    (UsualFiltration.filtration P (PrescribedPoissonFiltration.rawFiltration (Jump D) M ξ hM hξ))
    (fun t ω => X ω t) := by
  intro t
  exact (PrescribedPoissonFiltration.measurable_realized_at (Jump D) M ξ P hM hPoisson hξ hIndependent
    _ t (DeterministicEnvironmentProcess.measurable_process_at control hActivity v T hT hv id
      hCoupling measurable_id t)).stronglyMeasurable

variable (α : MomentLaw κ D) (hLaw : P.map ξ = α.measure)
include hLaw

theorem process_map (s : ℝ) : P.map (fun ω => X ω s) =
    DeterministicEnvironmentGeneralForward.actualLaw control hActivity v T hT hv α s := by
  have hm := DeterministicEnvironmentGeneralLaw.measurable_at control hActivity v T hT hv hCoupling s
  have he := PrescribedObservableLaws.map_comp (Jump D) M ξ P hM hPoisson hξ hIndependent _ hm.aemeasurable
  rw [hLaw] at he
  exact he

omit hCoupling in
theorem ae_initial : ∀ᵐ ω ∂P, X ω 0 = ξ ω := by
  have hc := DeterministicEnvironmentProcess.ae_initial control hActivity v T hT hv id α.measure
  rw [← hLaw] at hc
  exact ae_record (Jump D) M ξ P hM hPoisson hξ hIndependent hc

variable (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ s ∈ Icc 0 T, LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
  (hInitial : Integrable control.function α.measure)
include hB hEnv hInitial

/-- The genuine frozen exits exhaust every finite horizon on the supplied space. -/
theorem ae_exhaustive : ∀ᵐ ω ∂P, ∀ S : ℝ≥0, ∃ n : ℕ,
    (S : ℝ≥0∞) < DeterministicEnvironmentProcess.exit control hActivity v T hT hv id n (rec ω) := by
  letI : IsProbabilityMeasure α.measure := α.probability
  have hc := DeterministicEnvironmentProcess.ae_exhaustive control hActivity v T hT hv id α.measure
    hCoupling measurable_id B hB hEnv hInitial
  rw [← hLaw] at hc
  exact ae_record (Jump D) M ξ P hM hPoisson hξ hIndependent hc

theorem ae_cadlag : ∀ᵐ ω ∂P,
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (X ω) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : State D, Tendsto (X ω) (𝓝[<] t) (𝓝 y)) := by
  letI : IsProbabilityMeasure α.measure := α.probability
  have hc := DeterministicEnvironmentProcess.ae_cadlag control hActivity v T hT hv id α.measure
    hCoupling measurable_id B hB hEnv hInitial
  rw [← hLaw] at hc
  exact ae_record (Jump D) M ξ P hM hPoisson hξ hIndependent hc

theorem ae_finite_activity : ∀ᵐ ω ∂P, ∀ S : ℝ≥0, ∃ times : Finset ℝ,
    (times : Set ℝ) ⊆ Ioc 0 S ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ S →
      (∀ u ∈ times, u ∉ Ioc s t) → X ω s = X ω t := by
  letI : IsProbabilityMeasure α.measure := α.probability
  have hc := DeterministicEnvironmentProcess.ae_finite_activity control hActivity v T hT hv id α.measure
    hCoupling measurable_id B hB hEnv hInitial
  rw [← hLaw] at hc
  exact ae_record (Jump D) M ξ P hM hPoisson hξ hIndependent hc

/-- The accepted counting equation is driven by the specified measures. -/
theorem ae_counting_identity (f : State D → ℝ) : ∀ᵐ ω ∂P, ∀ S : ℝ≥0,
    f (X ω S) - f (ξ ω) = ∑ j, ∫ z, H f j S ω z ∂M j ω := by
  letI : IsProbabilityMeasure α.measure := α.probability
  exact PrescribedJumpProcess.ae_counting_identity (Jump D) control.function (finite_sublevels control)
    Jump.advance rate bounds id 0 M ξ (measurable_timeRate κ q v T hv hCoupling hT) measurable_id
    hM hξ P hPoisson hIndependent α.measure hLaw (affineConstant control B)
    (affineConstant_nonnegative control B hB) (function_nonnegative control)
    (fun x j t _ => timeRate_nonnegative κ q v T j t x) hInitial
    (fun x t _ => clamped_generator_affine_bound control v T hT B hB hEnv t x) f

theorem ae_integrable_increment : ∀ᵐ ω ∂P, ∀ (S : ℝ≥0) (f : State D → ℝ) (j : Jump D),
    Integrable (H f j S ω) (M j ω) := by
  letI : IsProbabilityMeasure α.measure := α.probability
  exact PrescribedJumpProcess.ae_integrable_increment (Jump D) control.function (finite_sublevels control)
    Jump.advance rate bounds id 0 M ξ (measurable_timeRate κ q v T hv hCoupling hT) measurable_id
    hM hξ P hPoisson hIndependent α.measure hLaw (affineConstant control B)
    (affineConstant_nonnegative control B hB) (function_nonnegative control)
    (fun x j t _ => timeRate_nonnegative κ q v T j t x) hInitial
    (fun x t _ => clamped_generator_affine_bound control v T hT B hB hEnv t x)

theorem ae_tendsto_preState : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
    Tendsto (X ω) (𝓝[<] t) (𝓝 (Z ω t)) := by
  letI : IsProbabilityMeasure α.measure := α.probability
  exact PrescribedJumpProcess.ae_tendsto_preState (Jump D) control.function (finite_sublevels control)
    Jump.advance rate bounds id 0 M ξ (measurable_timeRate κ q v T hv hCoupling hT) measurable_id
    hM hξ P hPoisson hIndependent α.measure hLaw (affineConstant control B)
    (affineConstant_nonnegative control B hB) (function_nonnegative control)
    (fun x j t _ => timeRate_nonnegative κ q v T j t x) hInitial
    (fun x t _ => clamped_generator_affine_bound control v T hT B hB hEnv t x)

/-- Pathwise uniqueness for the specified inputs, without a candidate moment
or finite-activity assumption. The environment is held at its endpoints. -/
theorem ae_unique (Y : Ω → ℝ → State D)
    (hcadlag : ∀ᵐ ω ∂P,
      (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (Y ω) (Ici t) t) ∧
      (∀ t : ℝ, 0 < t → ∃ y : State D, Tendsto (Y ω) (𝓝[<] t) (𝓝 y)))
    (hzero : ∀ᵐ ω ∂P, Y ω 0 = ξ ω)
    (heq : ∀ i : Fin D, ∀ᵐ ω ∂P, ∀ S : ℝ≥0,
      (Y ω S i : ℝ) - (ξ ω i : ℝ) = ∑ j, ∫ z,
        TimeDependentEquationUniqueness.increment Jump.advance rate
          (Function.leftLim (Y ω)) (fun x => (x i : ℝ)) j S z ∂M j ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Y ω t = X ω t := by
  letI : IsProbabilityMeasure α.measure := α.probability
  exact PrescribedJumpProcess.ae_unique_of_separating_equations (Jump D)
    control.function (finite_sublevels control) Jump.advance rate bounds id 0 M ξ
    (measurable_timeRate κ q v T hv hCoupling hT) measurable_id hM hξ P hPoisson hIndependent
    α.measure hLaw (affineConstant control B) (affineConstant_nonnegative control B hB)
    (function_nonnegative control) (fun x j t _ => timeRate_nonnegative κ q v T j t x) hInitial
    (fun x t _ => clamped_generator_affine_bound control v T hT B hB hEnv t x)
    (fun i : Fin D => fun x : State D => (x i : ℝ))
    (fun x y h => by
      funext i
      have hh : (x i : ℝ) = (y i : ℝ) := h i
      exact_mod_cast hh) Y hcadlag hzero heq

/-- The marginal curve is genuinely Wasserstein-continuous. Its value at zero
is α, regardless of the prescribed environment's value at zero. -/
def outputCurve : C(Icc (0 : ℝ) T, MomentLaw κ D) :=
  DeterministicEnvironmentGeneralLaw.outputCurve control hActivity v T hT hv α hCoupling B hB hEnv hInitial

theorem outputCurve_measure (s : Icc (0 : ℝ) T) :
    (outputCurve control hActivity v T hT hv hCoupling α B hB hEnv hInitial s).measure =
      P.map (fun ω => X ω s) :=
  (process_map control hActivity v T hT hv M ξ hCoupling hM hξ P hPoisson hIndependent α hLaw s).symm

omit hM hξ [IsProbabilityMeasure P] hPoisson hIndependent hLaw in
theorem outputCurve_initial : outputCurve control hActivity v T hT hv hCoupling α B hB hEnv hInitial
    ⟨0,le_rfl,hT⟩ = α :=
  DeterministicEnvironmentGeneralLaw.outputCurve_initial control hActivity v T hT hv α hCoupling B hB hEnv hInitial

/-- Genuine supplied-space Ψ integrability and the explicit affine-exponential bound. -/
theorem process_moment_bounds (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun ω => control.function (X ω s)) P ∧
    (∫ ω, control.function (X ω s) ∂P) ≤
      DeterministicEnvironmentGeneralLaw.momentBound control α B s := by
  have hc := DeterministicEnvironmentGeneralLaw.integrable_lyapunov_at
    control hActivity v T hT hv α hCoupling B hB hEnv hInitial s hs
  have hp := measurePreserving_record (Jump D) M ξ P hM hPoisson hξ hIndependent
  rw [hLaw] at hp
  refine ⟨(hp.integrable_comp hc.aestronglyMeasurable).mpr hc, ?_⟩
  have he := integral_map hp.measurable.aemeasurable
    (show AEStronglyMeasurable
      (fun p => control.function (DeterministicEnvironmentProcess.process control hActivity v T hT hv id p s))
      (P.map rec) from hp.map_eq.symm ▸ hc.aestronglyMeasurable)
  rw [hp.map_eq] at he
  exact he.symm.trans_le (DeterministicEnvironmentGeneralLaw.lyapunov_expectation_le
    control hActivity v T hT hv α hCoupling B hB hEnv hInitial s hs)

/-- The uniform estimate in Proposition 4.2, with an explicit finite constant. -/
theorem uniform_moment_bound (s : ℝ) (hs : s ∈ Icc 0 T) :
    (∫ ω, control.function (X ω s) ∂P) ≤
      Real.exp (affineConstant control B * T) * (1 + ∫ x, control.function x ∂α.measure) := by
  have h := (process_moment_bounds control hActivity v T hT hv M ξ hCoupling hM hξ P
    hPoisson hIndependent α hLaw B hB hEnv hInitial s hs.1).2
  have hm := DeterministicEnvironmentGeneralLaw.momentBound_mono control α B hB hs.2
  unfold DeterministicEnvironmentGeneralLaw.momentBound at h hm
  nlinarith

/-- The supplied-space marginals solve the original prescribed-rate equation. -/
theorem isSolution : FiniteJumpForward.IsSolution Jump.advance (fun j s x => q.rate j x (v s))
    α.measure (fun s => P.map (fun ω => X ω s)) T := by
  have he : (fun s => P.map (fun ω => X ω s)) =
      DeterministicEnvironmentGeneralForward.actualLaw control hActivity v T hT hv α :=
    funext (process_map control hActivity v T hT hv M ξ hCoupling hM hξ P hPoisson hIndependent α hLaw)
  rw [he]
  exact DeterministicEnvironmentGeneralForward.isSolution control hActivity v T hT hv α hCoupling B hB hEnv hInitial

/-- Uniqueness holds even among probability weak solutions without an extra
candidate moment bound, hence in the paper's stated moment class. -/
theorem law_unique (p : ℝ → Measure (State D))
    (hp : FiniteJumpForward.IsSolution Jump.advance (fun j s x => q.rate j x (v s)) α.measure p T) :
    EqOn (fun s => P.map (fun ω => X ω s)) p (Icc 0 T) := by
  intro s hs
  change P.map (fun ω => X ω s) = p s
  rw [process_map control hActivity v T hT hv M ξ hCoupling hM hξ P hPoisson hIndependent α hLaw]
  exact DeterministicEnvironmentForwardUniqueness.law_eq_solution
    control hActivity α v T hT hv hCoupling B hB hEnv hInitial p hp s hs

/-- Genuine whole-horizon crossings satisfy the stopped Lyapunov tail bound. -/
theorem crossing_probability_le (R S : ℝ) (hR : 0 < R) (hS : 0 ≤ S) :
    P (GlobalLyapunovExit.crossingEvent control.function X R S) ≤
      ENNReal.ofReal (2 * ((1 + ∫ x, control.function x ∂α.measure) *
        Real.exp (affineConstant control B * S)) / R) := by
  letI : IsProbabilityMeasure α.measure := α.probability
  have hc := GlobalLyapunovExit.measure_crossing_le control.function (finite_sublevels control)
    Jump.advance rate bounds id 0 α.measure (measurable_timeRate κ q v T hv hCoupling hT)
    measurable_id (affineConstant control B) (affineConstant_nonnegative control B hB)
    (function_nonnegative control) (fun x j t _ => timeRate_nonnegative κ q v T j t x) hInitial
    (fun x t _ => clamped_generator_affine_bound control v T hT B hB hEnv t x) R S hR hS
  have hm := Measure.le_map_apply (μ := P) (measurable_record (Jump D) M ξ hM hξ).aemeasurable
    (GlobalLyapunovExit.crossingEvent control.function
      (DeterministicEnvironmentProcess.process control hActivity v T hT hv id) R S)
  rw [record_map (Jump D) M ξ P hM hPoisson hξ hIndependent,hLaw] at hm
  exact hm.trans hc

end CarryingCapacity.PrescribedDeterministicEnvironment
