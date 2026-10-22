import CarryingCapacity.PrescribedPoissonFiltration
import CarryingCapacity.NonlinearGlobalCounting
import CarryingCapacity.TimeDependentEquationUniqueness

/-!
# The nonlinear all-time process on prescribed Poisson measures

Reconstruction retains the prescribed initial state and adds no randomness.
The actual marginal law is identified before writing the accepted equation,
which uses the supplied measures and the genuine left state. The realization
is adapted to the completed right-continuous natural filtration of its inputs.
Pathwise uniqueness below compares solutions with this same deterministic
marginal environment; it does not assume that an arbitrary candidate law has
already been identified with that environment.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal Topology BigOperators

namespace CarryingCapacity.PrescribedNonlinearProcess
open PrescribedPoissonRealization

variable {Ω : Type*} [MeasurableSpace Ω]
  {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)
  (M : Jump D → Ω → Measure (ℝ × ℝ)) (ξ : Ω → State D)

local notation "v" => NonlinearGlobalProcess.environment control hActivity ν hCoupling hMoment
local notation "rec" => record (Jump D) M ξ

/-- A single actual all-time path driven by the original prescribed input. -/
def process (ω : Ω) (t : ℝ) : State D :=
  NonlinearGlobalProcess.process control hActivity ν hCoupling hMoment (rec ω) t

def preState (ω : Ω) (t : ℝ) : State D :=
  NonlinearGlobalCounting.preState control hActivity ν hCoupling hMoment (rec ω) t

/-- No truncation remains in the supplied-noise accepted integrand. -/
def increment (f : State D → ℝ) (j : Jump D) (T : ℝ) (ω : Ω) (z : ℝ × ℝ) : ℝ :=
  if z.1 ∈ Ioc 0 T ∧ z.2 ≤ q.rate j
      (preState control hActivity ν hCoupling hMoment M ξ ω z.1) (v z.1)
  then f (Jump.advance j (preState control hActivity ν hCoupling hMoment M ξ ω z.1)) -
    f (preState control hActivity ν hCoupling hMoment M ξ ω z.1) else 0

local notation "X" => process control hActivity ν hCoupling hMoment M ξ
local notation "Z" => preState control hActivity ν hCoupling hMoment M ξ
local notation "H" => increment control hActivity ν hCoupling hMoment M ξ

omit [MeasurableSpace Ω] in
theorem increment_eq_canonical (f : State D → ℝ) (j : Jump D) (T : ℝ)
    (ω : Ω) (z : ℝ × ℝ) : H f j T ω z =
      NonlinearGlobalCounting.horizonIncrement control hActivity ν hCoupling hMoment f j T (rec ω,z) :=
  (NonlinearGlobalCounting.horizonIncrement_apply control hActivity ν hCoupling hMoment f j T (rec ω) z).symm

variable (hM : ∀ j, Measurable (M j)) (hξ : Measurable ξ)
include hM hξ

section JointMeasurability
attribute [local irreducible] PrescribedPoissonRealization.record NonlinearGlobalProcess.process

theorem measurable_process : Measurable (fun p : Ω × ℝ => X p.1 p.2) := by
  have hm : Measurable (fun p : Ω × ℝ => (rec p.1,p.2)) :=
    ((measurable_record (Jump D) M ξ hM hξ).comp measurable_fst).prodMk measurable_snd
  exact (NonlinearGlobalProcess.measurable_process control hActivity ν hCoupling hMoment).comp hm

end JointMeasurability

variable (P : Measure Ω) [IsProbabilityMeasure P]
  (hPoisson : PoissonObservationLaw.HasDisjointLaws P (Jump D) M)
  (hIndependent : IndepFun ξ (fun ω => fun j => M j ω) P)
include hPoisson hIndependent

theorem adapted_process : Adapted
    (UsualFiltration.filtration P (PrescribedPoissonFiltration.rawFiltration (Jump D) M ξ hM hξ))
    (fun t ω => X ω t) := by
  intro t
  exact (PrescribedPoissonFiltration.measurable_realized_at (Jump D) M ξ P hM hPoisson hξ hIndependent
    _ t (NonlinearGlobalProcess.adapted_process control hActivity ν hCoupling hMoment t).measurable).stronglyMeasurable

variable (hLaw : P.map ξ = ν.measure)
include hLaw

section MarginalTransfer
attribute [local irreducible] PrescribedPoissonRealization.record NonlinearGlobalProcess.process

/-- The actual supplied-space path has the constructed nonlinear marginal law. -/
theorem process_map (t : ℝ) (ht : 0 ≤ t) : P.map (fun ω => X ω t) = (v t).measure := by
  have hm : Measurable (fun p : CommonInitialNoise.Sample (State D) (Jump D) =>
      NonlinearGlobalProcess.process control hActivity ν hCoupling hMoment p t) :=
    (NonlinearGlobalProcess.measurable_process control hActivity ν hCoupling hMoment).comp
      (measurable_id.prodMk measurable_const)
  calc
    _ = (P.map rec).map (fun p => NonlinearGlobalProcess.process control hActivity ν hCoupling hMoment p t) :=
      (Measure.map_map hm (measurable_record (Jump D) M ξ hM hξ)).symm
    _ = (CommonInitialNoise.law ν.measure (Jump D)).map
        (fun p => NonlinearGlobalProcess.process control hActivity ν hCoupling hMoment p t) := by
      rw [record_map (Jump D) M ξ P hM hPoisson hξ hIndependent,hLaw]
    _ = _ := (NonlinearGlobalProcess.environment_measure_eq_marginal
      control hActivity ν hCoupling hMoment t ht).symm

end MarginalTransfer

theorem ae_initial : ∀ᵐ ω ∂P, X ω 0 = ξ ω := by
  have h := NonlinearGlobalCounting.ae_initial control hActivity ν hCoupling hMoment
  rw [← hLaw] at h
  exact ae_record (Jump D) M ξ P hM hPoisson hξ hIndependent h

theorem ae_cadlag : ∀ᵐ ω ∂P,
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (X ω) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : State D, Tendsto (X ω) (𝓝[<] t) (𝓝 y)) := by
  have h := NonlinearGlobalProcess.ae_process_cadlag control hActivity ν hCoupling hMoment
  rw [← hLaw] at h
  exact ae_record (Jump D) M ξ P hM hPoisson hξ hIndependent h

theorem ae_tendsto_preState : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
    Tendsto (X ω) (𝓝[<] t) (𝓝 (Z ω t)) := by
  have h := NonlinearGlobalCounting.ae_tendsto_preState control hActivity ν hCoupling hMoment
  rw [← hLaw] at h
  exact ae_record (Jump D) M ξ P hM hPoisson hξ hIndependent h

theorem ae_integrable_increment : ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (f : State D → ℝ) (j : Jump D),
    Integrable (H f j T ω) (M j ω) := by
  have hc := NonlinearGlobalCounting.ae_integrable_horizonIncrement control hActivity ν hCoupling hMoment
  rw [← hLaw] at hc
  filter_upwards [ae_record (Jump D) M ξ P hM hPoisson hξ hIndependent hc,
    ae_countingMeasure_noise (Jump D) M P hM hPoisson] with ω hi hm
  intro T f j
  have h := hi T f j
  rw [show (rec ω).2 = noise (Jump D) M ω from rfl,hm j] at h
  exact h.congr (Eventually.of_forall (fun z =>
    (increment_eq_canonical control hActivity ν hCoupling hMoment M ξ f j T ω z).symm))

/-- The genuine nonlinear equation uses its own actual marginal environment,
identified by `process_map`, and the supplied measures themselves. -/
theorem ae_counting_identity (f : State D → ℝ) : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
    f (X ω T) - f (ξ ω) = ∑ j, ∫ z, H f j T ω z ∂M j ω := by
  have hc := NonlinearGlobalCounting.ae_counting_identity control hActivity ν hCoupling hMoment f
  rw [← hLaw] at hc
  filter_upwards [ae_record (Jump D) M ξ P hM hPoisson hξ hIndependent hc,
    ae_countingMeasure_noise (Jump D) M P hM hPoisson] with ω hi hm
  intro T
  refine (hi T).trans ?_
  apply Finset.sum_congr rfl
  intro j _
  rw [show (rec ω).2 = noise (Jump D) M ω from rfl,hm j]
  exact integral_congr_ae (Eventually.of_forall (fun z =>
    (increment_eq_canonical control hActivity ν hCoupling hMoment M ξ f j T ω z).symm))

theorem ae_finite_activity : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ times : Finset ℝ,
    (times : Set ℝ) ⊆ Ioc 0 T ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
      (∀ u ∈ times, u ∉ Ioc s t) → X ω s = X ω t := by
  have hc := NonlinearGlobalCounting.ae_finite_activity control hActivity ν hCoupling hMoment
  rw [← hLaw] at hc
  exact ae_record (Jump D) M ξ P hM hPoisson hξ hIndependent hc

section MomentTransfer
attribute [local irreducible] PrescribedPoissonRealization.record NonlinearGlobalProcess.process

/-- Genuine initial-moment control transfers to the actual supplied-space path. -/
theorem process_moment_bounds (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω => control.function (X ω t)) P ∧
    (∫ ω, control.function (X ω t) ∂P) ≤
      LyapunovFlowSpace.exponentialEnvelope (∫ x, control.function x ∂ν.measure)
        (DeterministicEnvironmentLyapunov.driftConstant control) t := by
  have hc := NonlinearGlobalProcess.process_moment_bounds control hActivity ν hCoupling hMoment t ht
  have hp := measurePreserving_record (Jump D) M ξ P hM hPoisson hξ hIndependent
  rw [hLaw] at hp
  refine ⟨(hp.integrable_comp hc.1.aestronglyMeasurable).mpr hc.1,?_⟩
  have he := integral_map hp.measurable.aemeasurable
    (show AEStronglyMeasurable
      (fun p => control.function (NonlinearGlobalProcess.process control hActivity ν hCoupling hMoment p t))
      (P.map rec) from hp.map_eq.symm ▸ hc.1.aestronglyMeasurable)
  rw [hp.map_eq] at he
  exact he.symm.trans_le hc.2.1

end MomentTransfer

/-- Uniqueness among cadlag paths driven by the same measures and the already
identified nonlinear marginal environment. The candidate needs no additional
moment or activity hypothesis. -/
theorem ae_unique_for_environment (Y : Ω → ℝ → State D)
    (hcadlag : ∀ᵐ ω ∂P,
      (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (Y ω) (Ici t) t) ∧
      (∀ t : ℝ, 0 < t → ∃ y : State D, Tendsto (Y ω) (𝓝[<] t) (𝓝 y)))
    (hzero : ∀ᵐ ω ∂P, Y ω 0 = ξ ω)
    (heq : ∀ i : Fin D, ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      (Y ω T i : ℝ) - (ξ ω i : ℝ) =
        ∑ j, ∫ z, TimeDependentEquationUniqueness.increment Jump.advance
          (fun j t x => q.rate j x (v t)) (Function.leftLim (Y ω)) (fun x => (x i : ℝ)) j T z ∂M j ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Y ω t = X ω t := by
  have hactual := ae_all_iff.mpr (fun i : Fin D => ae_counting_identity
    control hActivity ν hCoupling hMoment M ξ hM hξ P hPoisson hIndependent hLaw (fun x => (x i : ℝ)))
  filter_upwards [hcadlag,hzero,ae_all_iff.mpr heq,
    ae_cadlag control hActivity ν hCoupling hMoment M ξ hM hξ P hPoisson hIndependent hLaw,
    ae_initial control hActivity ν hCoupling hMoment M ξ hM hξ P hPoisson hIndependent hLaw,
    ae_tendsto_preState control hActivity ν hCoupling hMoment M ξ hM hξ P hPoisson hIndependent hLaw,
    hactual] with ω hc hz hEq ha hazero hapre haEq
  have hxpre : ∀ t : ℝ, 0 < t → Tendsto (Y ω) (𝓝[<] t) (𝓝 (Function.leftLim (Y ω) t)) := by
    intro t ht
    obtain ⟨y,hy⟩ := hc.2 t ht
    rw [leftLim_eq_of_tendsto (neBot_iff.mp inferInstance) hy]
    exact hy
  apply TimeDependentEquationUniqueness.eq_of_separating_counting_equations
    (fun i : Fin D => fun x : State D => (x i : ℝ))
    (fun x y hxy => by
      funext i
      have h : (x i : ℝ) = (y i : ℝ) := hxy i
      exact_mod_cast h)
    Jump.advance (fun j t x => q.rate j x (v t)) (fun j => M j ω) (Y ω) (X ω)
    (Function.leftLim (Y ω)) (Z ω) hc.1 ha.1 hxpre hapre (hz.trans hazero.symm)
  · intro i T hT
    rw [hz]
    exact hEq i ⟨T,hT⟩
  · intro i T hT
    rw [hazero]
    exact haEq i ⟨T,hT⟩

end CarryingCapacity.PrescribedNonlinearProcess
