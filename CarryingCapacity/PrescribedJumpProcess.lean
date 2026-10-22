import CarryingCapacity.PrescribedPoissonFiltration
import CarryingCapacity.TimeDependentNonexplosion
import CarryingCapacity.TimeDependentGlobalUniqueness

/-!
# Strong nonexplosive jump solutions driven by prescribed Poisson measures

The supplied noise satisfies the standard independent Poisson count laws.
Finite Lyapunov sublevels, local rate bounds and the affine drift condition
give the actual solution without a supplied nonexplosion or equation premise.
The solution is a measurable function of the original initial record and
measures, adapted to their completed right-continuous natural filtration.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal NNReal BigOperators

namespace CarryingCapacity.PrescribedJumpProcess
open PrescribedPoissonRealization

variable {Ω A E : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [DecidableEq E] [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (J : Type) [Fintype J]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (hbounded : ∀ n : ℕ, ∃ C : ℝ,
    ∀ x ∈ LyapunovLocalization.active V hfinite n, ∀ j t, rate j t x ≤ C)
  (initial : A → E) (e : E)
  (M : J → Ω → Measure (ℝ × ℝ)) (ξ : Ω → A)

/-- The constructed path on the original probability space. -/
def process (ω : Ω) (t : ℝ) : E :=
  TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e (record J M ξ ω) t

def preState (ω : Ω) (t : ℝ) : E :=
  TimeDependentGlobalCounting.preState V hfinite jump rate hbounded initial e (record J M ξ ω) t

/-- The actual threshold integrand using the constructed pre-jump state. -/
def increment (f : E → ℝ) (j : J) (T : ℝ) (ω : Ω) (z : ℝ × ℝ) : ℝ :=
  TimeDependentEquationUniqueness.increment jump rate
    (preState J V hfinite jump rate hbounded initial e M ξ ω) f j T z

variable (hRate : ∀ j x, Measurable (fun t => rate j t x))
  (hinit : Measurable initial) (hM : ∀ j, Measurable (M j)) (hξ : Measurable ξ)
include hRate hinit hM hξ

section JointMeasurability
attribute [local irreducible] PrescribedPoissonRealization.record TimeDependentGlobalProcess.process

theorem measurable_process : Measurable
    (fun p : Ω × ℝ => process J V hfinite jump rate hbounded initial e M ξ p.1 p.2) := by
  have hm : Measurable (fun p : Ω × ℝ => (record J M ξ p.1,p.2)) :=
    ((measurable_record J M ξ hM hξ).comp measurable_fst).prodMk measurable_snd
  exact (TimeDependentGlobalProcess.measurable_process
    V hfinite jump rate hbounded initial e hRate hinit).comp hm

end JointMeasurability

variable (P : Measure Ω) [IsProbabilityMeasure P]
  (hPoisson : PoissonObservationLaw.HasDisjointLaws P J M)
  (hIndependent : IndepFun ξ (fun ω => fun j => M j ω) P)
include hPoisson hIndependent

theorem measurable_process_at (t : ℝ) :
    Measurable[UsualFiltration.usualAt P (PrescribedPoissonFiltration.rawFiltration J M ξ hM hξ) t]
      (fun ω => process J V hfinite jump rate hbounded initial e M ξ ω t) :=
  PrescribedPoissonFiltration.measurable_realized_at J M ξ P hM hPoisson hξ hIndependent
    _ t (TimeDependentGlobalProcess.measurable_process_at V hfinite jump rate hbounded initial e hRate hinit t)

theorem adapted_process : Adapted
    (UsualFiltration.filtration P (PrescribedPoissonFiltration.rawFiltration J M ξ hM hξ))
    (fun t ω => process J V hfinite jump rate hbounded initial e M ξ ω t) :=
  fun t => (measurable_process_at J V hfinite jump rate hbounded initial e M ξ
    hRate hinit hM hξ P hPoisson hIndependent t).stronglyMeasurable

variable (μ : Measure A) [IsProbabilityMeasure μ] (hLaw : P.map ξ = μ)
include hLaw

omit hRate hinit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [BorelSpace E] [IsProbabilityMeasure μ] in
theorem ae_initial : ∀ᵐ ω ∂P,
    process J V hfinite jump rate hbounded initial e M ξ ω 0 = initial (ξ ω) := by
  have hc := TimeDependentGlobalProcess.ae_process_zero V hfinite jump rate hbounded initial e μ
  rw [← hLaw] at hc
  exact ae_record J M ξ P hM hPoisson hξ hIndependent hc

variable (b : ℝ) (hb : 0 ≤ b) (hVnonnegative : ∀ x, 0 ≤ V x)
  (hRateNonnegative : ∀ x j t, 0 ≤ t → 0 ≤ rate j t x)
  (hInitialMoment : Integrable (fun a => V (initial a)) μ)
  (hDrift : ∀ x t, 0 ≤ t →
    (∑ j, rate j t x * (V (jump j x) - V x)) ≤ b * (1 + V x))
include hb hVnonnegative hRateNonnegative hInitialMoment hDrift

/-- Cadlag paths are obtained on the original space from the constructed law. -/
theorem ae_cadlag : ∀ᵐ ω ∂P,
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt
      (process J V hfinite jump rate hbounded initial e M ξ ω) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : E, Tendsto
      (process J V hfinite jump rate hbounded initial e M ξ ω) (𝓝[<] t) (𝓝 y)) := by
  have hc := TimeDependentNonexplosion.ae_global_cadlag V hfinite jump rate hbounded initial e μ
    hRate hinit b hb hVnonnegative hRateNonnegative hInitialMoment hDrift
  rw [← hLaw] at hc
  exact ae_record J M ξ P hM hPoisson hξ hIndependent hc

theorem ae_tendsto_preState : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → Tendsto
    (process J V hfinite jump rate hbounded initial e M ξ ω) (𝓝[<] t)
      (𝓝 (preState J V hfinite jump rate hbounded initial e M ξ ω t)) := by
  have hc := TimeDependentGlobalCounting.ae_tendsto_preState V hfinite jump rate hbounded initial e μ
    (TimeDependentNonexplosion.ae_exhaustive V hfinite jump rate hbounded initial e μ
      hRate hinit b hb hVnonnegative hRateNonnegative hInitialMoment hDrift)
  rw [← hLaw] at hc
  exact ae_record J M ξ P hM hPoisson hξ hIndependent hc

theorem ae_integrable_increment : ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (f : E → ℝ) (j : J),
    Integrable (increment J V hfinite jump rate hbounded initial e M ξ f j T ω) (M j ω) := by
  have hc := TimeDependentGlobalCounting.ae_integrable_horizonIncrement
    V hfinite jump rate hbounded initial e μ
    (TimeDependentNonexplosion.ae_exhaustive V hfinite jump rate hbounded initial e μ
      hRate hinit b hb hVnonnegative hRateNonnegative hInitialMoment hDrift)
  rw [← hLaw] at hc
  filter_upwards [ae_record J M ξ P hM hPoisson hξ hIndependent hc,
    ae_countingMeasure_noise J M P hM hPoisson] with ω hi hm
  intro T f j
  have h := hi T f j
  rw [TimeDependentGlobalUniqueness.horizonIncrement_eq_increment,
    show (record J M ξ ω).2 = noise J M ω from rfl, hm j] at h
  exact h

/-- The supplied measures themselves drive the genuine accepted-increment
equation, with actual pathwise integrability proved separately above. -/
theorem ae_counting_identity (f : E → ℝ) : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
    f (process J V hfinite jump rate hbounded initial e M ξ ω T) - f (initial (ξ ω)) =
      ∑ j, ∫ z, increment J V hfinite jump rate hbounded initial e M ξ f j T ω z ∂M j ω := by
  have hc := TimeDependentGlobalCounting.ae_testFunction_counting_identity
    V hfinite jump rate hbounded initial e μ f
    (TimeDependentNonexplosion.ae_exhaustive V hfinite jump rate hbounded initial e μ
      hRate hinit b hb hVnonnegative hRateNonnegative hInitialMoment hDrift)
  rw [← hLaw] at hc
  filter_upwards [ae_record J M ξ P hM hPoisson hξ hIndependent hc,
    ae_countingMeasure_noise J M P hM hPoisson] with ω hi hm
  intro T
  calc
    _ = ∑ j, ∫ z, TimeDependentGlobalCounting.horizonIncrement
        V hfinite jump rate hbounded initial e f j T (record J M ξ ω,z)
          ∂MarkedNoise.countingMeasure j (record J M ξ ω).2 := hi T
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [TimeDependentGlobalUniqueness.horizonIncrement_eq_increment,
        show (record J M ξ ω).2 = noise J M ω from rfl, hm j]
      rfl

/-- Finitely many actual events contain all changes on every bounded horizon. -/
theorem ae_finite_activity : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ times : Finset ℝ,
    (times : Set ℝ) ⊆ Ioc 0 T ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
      (∀ u ∈ times, u ∉ Ioc s t) →
        process J V hfinite jump rate hbounded initial e M ξ ω s =
          process J V hfinite jump rate hbounded initial e M ξ ω t := by
  have hc := TimeDependentNonexplosion.ae_global_finite_activity
    V hfinite jump rate hbounded initial e μ hRate hinit b hb hVnonnegative
      hRateNonnegative hInitialMoment hDrift
  rw [← hLaw] at hc
  filter_upwards [ae_record J M ξ P hM hPoisson hξ hIndependent hc] with ω hω
  intro T
  obtain ⟨n,hn,he⟩ := hω T
  exact ⟨_,hn,he⟩

/-- A candidate with the same supplied measures, genuine left limits, initial
state and separating counting equations is indistinguishable from the actual
solution. No candidate moment or finite-activity assumption is required. -/
theorem ae_unique_of_separating_equations [DiscreteTopology E]
    {I : Type*} [Countable I] (test : I → E → ℝ)
    (hseparate : ∀ x y : E, (∀ i, test i x = test i y) → x = y)
    (X : Ω → ℝ → E)
    (hcadlag : ∀ᵐ ω ∂P,
      (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (X ω) (Ici t) t) ∧
      (∀ t : ℝ, 0 < t → ∃ y : E, Tendsto (X ω) (𝓝[<] t) (𝓝 y)))
    (hzero : ∀ᵐ ω ∂P, X ω 0 = initial (ξ ω))
    (heq : ∀ i : I, ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      test i (X ω T) - test i (initial (ξ ω)) =
        ∑ j, ∫ z, TimeDependentEquationUniqueness.increment jump rate
          (Function.leftLim (X ω)) (test i) j T z ∂M j ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      X ω t = process J V hfinite jump rate hbounded initial e M ξ ω t := by
  have hactual := ae_all_iff.mpr (fun i : I => ae_counting_identity
    J V hfinite jump rate hbounded initial e M ξ hRate hinit hM hξ P hPoisson hIndependent
      μ hLaw b hb hVnonnegative hRateNonnegative hInitialMoment hDrift (test i))
  filter_upwards [hcadlag,hzero,ae_all_iff.mpr heq,
    ae_cadlag J V hfinite jump rate hbounded initial e M ξ hRate hinit hM hξ P hPoisson
      hIndependent μ hLaw b hb hVnonnegative hRateNonnegative hInitialMoment hDrift,
    ae_initial J V hfinite jump rate hbounded initial e M ξ hM hξ P hPoisson hIndependent μ hLaw,
    ae_tendsto_preState J V hfinite jump rate hbounded initial e M ξ hRate hinit hM hξ P hPoisson
      hIndependent μ hLaw b hb hVnonnegative hRateNonnegative hInitialMoment hDrift,
    hactual] with ω hc hz hEq ha hazero hapre haEq
  have hxpre : ∀ t : ℝ, 0 < t → Tendsto (X ω) (𝓝[<] t) (𝓝 (Function.leftLim (X ω) t)) := by
    intro t ht
    obtain ⟨y,hy⟩ := hc.2 t ht
    rw [leftLim_eq_of_tendsto (neBot_iff.mp inferInstance) hy]
    exact hy
  apply TimeDependentEquationUniqueness.eq_of_separating_counting_equations test hseparate
    jump rate (fun j => M j ω) (X ω)
    (process J V hfinite jump rate hbounded initial e M ξ ω)
    (Function.leftLim (X ω)) (preState J V hfinite jump rate hbounded initial e M ξ ω)
    hc.1 ha.1 hxpre hapre (hz.trans hazero.symm)
  · intro i T hT
    rw [hz]
    exact hEq i ⟨T,hT⟩
  · intro i T hT
    rw [hazero]
    exact haEq i ⟨T,hT⟩

end CarryingCapacity.PrescribedJumpProcess
