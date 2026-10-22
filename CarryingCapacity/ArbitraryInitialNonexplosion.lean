import CarryingCapacity.ActualGlobalCounting
import CarryingCapacity.ActualGlobalUniqueness

/-!
# Nonexplosion for arbitrary independent initial laws

The Lyapunov argument is first applied to each deterministic state. Countability
puts all those conclusions on one full noise event. The actual constructions
depend on an initial record only through its sampled state, so this event lifts
to every independent initial law, without an initial Lyapunov moment.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.ArbitraryInitialNonexplosion
open CommonInitialNoise LyapunovLocalization

section Substitution
variable {A E J : Type*} [DecidableEq E] [Fintype J]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → E → ℝ) (initial : A → E)

/-- Actual local paths depend on the initial record only through its state. -/
theorem path_initial_substitution (n : ℕ) (p : Sample A J) (t : ℝ) :
    path V hfinite jump rate initial n p t =
      path V hfinite jump rate id n (initial p.1, p.2) t := rfl

/-- The same substitution is exact for the genuine first exit. -/
theorem exit_initial_substitution (n : ℕ) (p : Sample A J) :
    exit V hfinite jump rate initial n p =
      exit V hfinite jump rate id n (initial p.1, p.2) := rfl

variable [TopologicalSpace E] (e : E)

/-- The total global construction has the same exact initial-state substitution. -/
theorem process_initial_substitution (p : Sample A J) (t : ℝ) :
    GlobalLocalizedProcess.process V hfinite jump rate initial e p t =
      GlobalLocalizedProcess.process V hfinite jump rate id e (initial p.1, p.2) t := rfl

/-- The strict-past representative also depends only on the sampled initial state. -/
theorem preState_initial_substitution (p : Sample A J) (t : ℝ) :
    GlobalLocalizedCountingIdentity.preState V hfinite jump rate initial e p t =
      GlobalLocalizedCountingIdentity.preState V hfinite jump rate id e (initial p.1, p.2) t := rfl

end Substitution

section General
variable {A E J : Type*} [MeasurableSpace A] [DecidableEq E] [Fintype J]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → E → ℝ) (initial : A → E) (e : E)
  (b : ℝ) (hb : 0 ≤ b) (hVnonneg : ∀ x, 0 ≤ V x)
  (hq : ∀ x j, 0 ≤ rate j x)
  (hdrift : ∀ x, (∑ j, rate j x * (V (jump j x) - V x)) ≤ b * (1 + V x))
include hb hVnonneg hq hdrift

/-- One full noise event provides nonexplosion for every deterministic state.
The only moment estimate used is the automatically finite value V(x). -/
theorem ae_noise_exhaustive : ∀ᵐ ω ∂MarkedNoise.law J, ∀ x : E, ∀ T : ℝ≥0, ∃ n : ℕ,
    (T : ℝ≥0∞) < exit V hfinite jump rate id n (x,ω) := by
  apply ae_all_iff.mpr
  intro x
  have hx := ActualNonexplosion.ae_exhaustive V hfinite jump rate id x (Measure.dirac x)
    measurable_id b hb hVnonneg hq (integrable_dirac) hdrift
  have hh := Measure.ae_ae_of_ae_prod hx
  simpa only [ae_dirac_eq, eventually_pure] using hh

variable (μ : Measure A)

/-- Actual exit exhaustion for any independent initial law. No initial moment,
probability, or initial-map measurability premise is needed for this path property. -/
theorem ae_exhaustive : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n : ℕ,
    (T : ℝ≥0∞) < exit V hfinite jump rate initial n p := by
  filter_upwards [ae_noise μ (ae_noise_exhaustive V hfinite jump rate b hb hVnonneg hq hdrift)]
    with p hp
  exact hp (initial p.1)

/-- Every finite horizon agrees with sufficiently large actual finite localizations. -/
theorem ae_agrees_on_horizon : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n, ∀ m, n ≤ m →
    ∀ t : ℝ, 0 ≤ t → t ≤ T →
      GlobalLocalizedProcess.process V hfinite jump rate initial e p t =
        path V hfinite jump rate initial m p t :=
  GlobalLocalizedProcess.ae_agrees_on_horizon V hfinite jump rate initial e μ
    (ae_exhaustive V hfinite jump rate initial b hb hVnonneg hq hdrift μ)

/-- The actual process is cadlag without an integrable initial Lyapunov value. -/
theorem ae_cadlag : ∀ᵐ p ∂law μ J,
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt
      (GlobalLocalizedProcess.process V hfinite jump rate initial e p) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : E, Tendsto
      (GlobalLocalizedProcess.process V hfinite jump rate initial e p) (𝓝[<] t) (𝓝 y)) :=
  GlobalLocalizedProcess.ae_process_cadlag V hfinite jump rate initial e μ
    (ae_exhaustive V hfinite jump rate initial b hb hVnonneg hq hdrift μ)

/-- All changes occur at finitely many actual proposal times on each bounded horizon. -/
theorem ae_finite_activity : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
    (GlobalLocalizedActivity.horizonTimes V hfinite rate n p T : Set ℝ) ⊆ Ioc 0 T ∧
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
      (∀ u ∈ GlobalLocalizedActivity.horizonTimes V hfinite rate n p T, u ∉ Ioc s t) →
      GlobalLocalizedProcess.process V hfinite jump rate initial e p s =
        GlobalLocalizedProcess.process V hfinite jump rate initial e p t :=
  GlobalLocalizedActivity.ae_finite_activity V hfinite jump rate initial e μ
    (ae_exhaustive V hfinite jump rate initial b hb hVnonneg hq hdrift μ)

/-- The unrestricted actual counting integrands are pathwise integrable for
all finite horizons and all test functions, with no initial moment premise. -/
theorem ae_integrable_horizonIncrement : ∀ᵐ p ∂law μ J,
    ∀ (T : ℝ≥0) (f : E → ℝ) (j : J),
      Integrable (fun q => GlobalLocalizedCountingIdentity.horizonIncrement
        V hfinite jump rate initial e f j T (p,q)) (MarkedNoise.countingMeasure j p.2) :=
  GlobalLocalizedCountingIdentity.ae_integrable_horizonIncrement V hfinite jump rate initial e μ
    (ae_exhaustive V hfinite jump rate initial b hb hVnonneg hq hdrift μ)

/-- The actual unrestricted test-function counting equation for arbitrary
independent initial laws. -/
theorem ae_counting_identity (f : E → ℝ) : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0,
    f (GlobalLocalizedProcess.process V hfinite jump rate initial e p T) - f (initial p.1) =
      ∑ j : J, ∫ q, GlobalLocalizedCountingIdentity.horizonIncrement
        V hfinite jump rate initial e f j T (p,q) ∂MarkedNoise.countingMeasure j p.2 :=
  GlobalLocalizedCountingIdentity.ae_testFunction_counting_identity V hfinite jump rate initial e μ f
    (ae_exhaustive V hfinite jump rate initial b hb hVnonneg hq hdrift μ)

/-- Pathwise uniqueness also needs no initial moment: a countable separating
family of genuine candidate equations suffices. -/
theorem ae_candidate_eq_process_of_separating_tests [DiscreteTopology E]
    {I : Type*} [Countable I] (test : I → E → ℝ)
    (hseparate : ∀ x y : E, (∀ i, test i x = test i y) → x = y)
    (X : Sample A J → ℝ → E)
    (hcadlag : ∀ᵐ p ∂law μ J,
      (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (X p) (Ici t) t) ∧
      (∀ t : ℝ, 0 < t → ∃ y : E, Tendsto (X p) (𝓝[<] t) (𝓝 y)))
    (hzero : ∀ᵐ p ∂law μ J, X p 0 = initial p.1)
    (heq : ∀ i : I, ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0,
      test i (X p T) - test i (initial p.1) =
        ∑ j : J, ∫ q, GlobalCountingUniqueness.candidateIncrement jump rate X e
          (test i) j T (p,q) ∂MarkedNoise.countingMeasure j p.2) :
    ∀ᵐ p ∂law μ J, ∀ t : ℝ, 0 ≤ t →
      X p t = GlobalLocalizedProcess.process V hfinite jump rate initial e p t :=
  GlobalCountingUniqueness.ae_candidate_eq_process_of_separating_tests
    V hfinite jump rate initial e μ test hseparate
    (ae_exhaustive V hfinite jump rate initial b hb hVnonneg hq hdrift μ)
    X hcadlag hzero heq

end General

section Configuration
open ConfigurationLocalization
variable {A : Type*} [MeasurableSpace A] {N D : ℕ}
  {κ : MomentScale} {q : Rates D (MomentLaw κ D)} (control : LyapunovControl κ q)
  (hN : 0 < N) (initial : A → Configuration N D) (μ : Measure A)

/-- The actual empirical system is nonexplosive for every independent initial law. -/
theorem configuration_exhaustive : ∀ᵐ p ∂law μ (Label N D), ∀ T : ℝ≥0, ∃ n : ℕ,
    (T : ℝ≥0∞) < ConfigurationLocalization.exit control hN initial n p :=
  ae_exhaustive (lyapunov control) (finite_sublevel control hN) jump (rate κ q hN)
    initial (2 * driftConstant control)
    (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
    (lyapunov_nonnegative control) (fun z j => rate_nonnegative κ q hN j z)
    (ConfigurationNonexplosion.generator_affine_bound control hN) μ

/-- Cadlag paths for the actual empirical system, without an initial moment. -/
theorem configuration_cadlag : ∀ᵐ p ∂law μ (Label N D),
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt
      (ConfigurationNonexplosion.process control hN initial p) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : Configuration N D, Tendsto
      (ConfigurationNonexplosion.process control hN initial p) (𝓝[<] t) (𝓝 y)) :=
  GlobalLocalizedProcess.ae_process_cadlag (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q hN) initial 0 μ (configuration_exhaustive control hN initial μ)

/-- The empirical counting equation holds for every real configuration test. -/
theorem configuration_counting_identity (f : Configuration N D → ℝ) :
    ∀ᵐ p ∂law μ (Label N D), ∀ T : ℝ≥0,
      f (ConfigurationNonexplosion.process control hN initial p T) - f (initial p.1) =
        ∑ j : Label N D, ∫ r, GlobalLocalizedCountingIdentity.horizonIncrement
          (lyapunov control) (finite_sublevel control hN) jump (rate κ q hN)
          initial 0 f j T (p,r) ∂MarkedNoise.countingMeasure j p.2 :=
  GlobalLocalizedCountingIdentity.ae_testFunction_counting_identity (lyapunov control)
    (finite_sublevel control hN) jump (rate κ q hN) initial 0 μ f
      (configuration_exhaustive control hN initial μ)

/-- The original particle-coordinate equations give pathwise uniqueness for
arbitrary independent initial laws, with no moment assumption. -/
theorem configuration_eq_of_coordinate_equations
    (X : Sample A (Label N D) → ℝ → Configuration N D)
    (hcadlag : ∀ᵐ p ∂law μ (Label N D),
      (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (X p) (Ici t) t) ∧
      (∀ t : ℝ, 0 < t → ∃ y : Configuration N D, Tendsto (X p) (𝓝[<] t) (𝓝 y)))
    (hzero : ∀ᵐ p ∂law μ (Label N D), X p 0 = initial p.1)
    (heq : ∀ i : Fin N × Fin D, ∀ᵐ p ∂law μ (Label N D), ∀ T : ℝ≥0,
      (X p T i.1 i.2 : ℝ) - (initial p.1 i.1 i.2 : ℝ) =
        ∑ j : Label N D, ∫ r, GlobalCountingUniqueness.candidateIncrement jump (rate κ q hN) X 0
          (ActualGlobalUniqueness.ConfigurationCoordinates.test i) j T (p,r)
            ∂MarkedNoise.countingMeasure j p.2) :
    ∀ᵐ p ∂law μ (Label N D), ∀ t : ℝ, 0 ≤ t →
      X p t = ConfigurationNonexplosion.process control hN initial p t :=
  GlobalCountingUniqueness.ae_candidate_eq_process_of_separating_tests
    (lyapunov control) (finite_sublevel control hN) jump (rate κ q hN) initial 0 μ
    ActualGlobalUniqueness.ConfigurationCoordinates.test
    ActualGlobalUniqueness.ConfigurationCoordinates.separate
    (configuration_exhaustive control hN initial μ) X hcadlag hzero heq

end Configuration
end CarryingCapacity.ArbitraryInitialNonexplosion
