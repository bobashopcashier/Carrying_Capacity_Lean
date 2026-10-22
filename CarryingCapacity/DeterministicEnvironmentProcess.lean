import CarryingCapacity.DeterministicEnvironmentLyapunov
import CarryingCapacity.TimeDependentNonexplosion
import CarryingCapacity.TimeDependentGlobalMoment
import CarryingCapacity.TimeDependentGlobalActivity
import CarryingCapacity.TimeDependentGlobalCounting
import CarryingCapacity.TimeDependentGlobalUniqueness

/-!
# The actual global process in a prescribed moment-law environment

The process is the common-noise limit of canonical spatial frozen paths, with
rate cutoffs derived from the activity assumption. Coupling regularity gives
time measurability. A genuine bounded Lyapunov moment of the prescribed curve
and the stated LyapunovControl derive actual exit exhaustion and global moment
bounds; none of these stochastic conclusions is assumed.

The environment is held at its endpoints outside the selected horizon.
This module does not assert a forward-law uniqueness or invariant-map result.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal Topology BigOperators

namespace CarryingCapacity.DeterministicEnvironmentProcess
open CommonInitialNoise DeterministicEnvironmentLyapunov DeterministicEnvironmentFrozen

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))
  {A : Type*} [MeasurableSpace A] (initial : A → State D)

/-- The actual frozen approximation at a canonical spatial level. -/
def localizedPath (n : ℕ) (p : Sample A (Jump D)) (t : ℝ) : State D :=
  TimeDependentLocalization.path control.function (finite_sublevels control) Jump.advance
    (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv) initial n p t

/-- The genuine exit of the same localized path. -/
def exit (n : ℕ) (p : Sample A (Jump D)) : ℝ≥0∞ :=
  TimeDependentLocalization.exit control.function (finite_sublevels control) Jump.advance
    (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv) initial n p

/-- The actual all-sample measurable limit of the spatial localizations.
The definition has no environmental Lyapunov bound or initial moment input. -/
def process (p : Sample A (Jump D)) (t : ℝ) : State D :=
  TimeDependentGlobalProcess.process control.function (finite_sublevels control) Jump.advance
    (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv) initial 0 p t

/-- Its joint measurability follows from the paper's rate coupling assumption. -/
theorem measurable_process (hCoupling : MomentCouplingBound κ q) (hinit : Measurable initial) :
    Measurable (fun p : Sample A (Jump D) × ℝ => process control hActivity v T hT hv initial p.1 p.2) :=
  TimeDependentGlobalProcess.measurable_process control.function (finite_sublevels control)
    Jump.advance (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv)
      initial 0 (DeterministicEnvironmentFrozen.measurable_timeRate κ q v T hv hCoupling hT) hinit

/-- Every actual time evaluation is measurable in the raw initial/noise history. -/
theorem measurable_process_at (hCoupling : MomentCouplingBound κ q) (hinit : Measurable initial)
    (t : ℝ) : Measurable[filtration A (Jump D) t]
      (fun p => process control hActivity v T hT hv initial p t) :=
  TimeDependentGlobalProcess.measurable_process_at control.function (finite_sublevels control)
    Jump.advance (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv)
      initial 0 (DeterministicEnvironmentFrozen.measurable_timeRate κ q v T hv hCoupling hT) hinit t

theorem adapted_process (hCoupling : MomentCouplingBound κ q) (hinit : Measurable initial) :
    Adapted (filtration A (Jump D))
      (fun t p => process control hActivity v T hT hv initial p t) :=
  fun t => (measurable_process_at control hActivity v T hT hv initial hCoupling hinit t).stronglyMeasurable

/-- Correct initial value holds without an initial moment or environmental bound. -/
theorem ae_initial (μ : Measure A) : ∀ᵐ p ∂law μ (Jump D),
    process control hActivity v T hT hv initial p 0 = initial p.1 :=
  TimeDependentGlobalProcess.ae_process_zero control.function (finite_sublevels control)
    Jump.advance (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv) initial 0 μ

/-- The actual global path has exactly the prescribed pushed-forward initial law. -/
theorem initial_law (μ : Measure A) [IsProbabilityMeasure μ] (hinit : Measurable initial) :
    (law μ (Jump D)).map (fun p => process control hActivity v T hT hv initial p 0) = μ.map initial :=
  TimeDependentGlobalProcess.process_zero_law control.function (finite_sublevels control)
    Jump.advance (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv)
      initial 0 μ hinit

variable (μ : Measure A) [IsProbabilityMeasure μ]
  (hCoupling : MomentCouplingBound κ q) (hinit : Measurable initial)
  (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ t ∈ Icc 0 T, LyapunovFlowSpace.lyapunovIntegral control.function (v t) ≤ ENNReal.ofReal B)
  (hInitial : Integrable (fun a => control.function (initial a)) μ)
include hCoupling hinit hB hEnv hInitial

/-- Reciprocal tails for the actual first exits, with every stochastic bound
derived from the exact paper assumptions. -/
theorem exit_probability_le (n : ℕ) (S : ℝ) (hS : 0 ≤ S) :
    (law μ (Jump D)) {p | exit control hActivity v T hT hv initial n p ≤ ENNReal.ofReal S} ≤
      ENNReal.ofReal ((1 + ∫ a, control.function (initial a) ∂μ) *
        Real.exp (affineConstant control B * S) - 1) / ((n + 1 : ℕ) : ℝ≥0∞) :=
  TimeDependentNonexplosion.exit_probability_le control.function (finite_sublevels control)
    Jump.advance (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv)
      initial 0 μ (DeterministicEnvironmentFrozen.measurable_timeRate κ q v T hv hCoupling hT)
      hinit (affineConstant control B) (affineConstant_nonnegative control B hB)
      (function_nonnegative control) (fun x j t _ => timeRate_nonnegative κ q v T j t x) hInitial
      (fun x t _ => clamped_generator_affine_bound control v T hT B hB hEnv t x) n S hS

/-- Genuine exits exhaust every finite horizon almost surely. -/
theorem ae_exhaustive : ∀ᵐ p ∂law μ (Jump D), ∀ S : ℝ≥0, ∃ n : ℕ,
    (S : ℝ≥0∞) < exit control hActivity v T hT hv initial n p :=
  TimeDependentNonexplosion.ae_exhaustive control.function (finite_sublevels control)
    Jump.advance (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv)
      initial 0 μ (DeterministicEnvironmentFrozen.measurable_timeRate κ q v T hv hCoupling hT)
      hinit (affineConstant control B) (affineConstant_nonnegative control B hB)
      (function_nonnegative control) (fun x j t _ => timeRate_nonnegative κ q v T j t x) hInitial
      (fun x t _ => clamped_generator_affine_bound control v T hT B hB hEnv t x)

/-- The actual global path agrees throughout each finite horizon with every
sufficiently high canonical frozen path. -/
theorem ae_agrees_on_horizon : ∀ᵐ p ∂law μ (Jump D), ∀ S : ℝ≥0, ∃ n, ∀ m, n ≤ m →
    ∀ t : ℝ, 0 ≤ t → t ≤ S → process control hActivity v T hT hv initial p t =
      localizedPath control hActivity v T hT hv initial m p t :=
  TimeDependentGlobalProcess.ae_agrees_on_horizon control.function (finite_sublevels control)
    Jump.advance (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv)
      initial 0 μ (ae_exhaustive control hActivity v T hT hv initial μ hCoupling hinit B hB hEnv hInitial)

/-- Nonexplosion yields actual right-continuous paths with left limits. -/
theorem ae_cadlag : ∀ᵐ p ∂law μ (Jump D),
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt
      (process control hActivity v T hT hv initial p) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : State D, Tendsto
      (process control hActivity v T hT hv initial p) (𝓝[<] t) (𝓝 y)) :=
  TimeDependentGlobalProcess.ae_process_cadlag control.function (finite_sublevels control)
    Jump.advance (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv)
      initial 0 μ (ae_exhaustive control hActivity v T hT hv initial μ hCoupling hinit B hB hEnv hInitial)

/-- Only finitely many actual proposals can change the global path on a
bounded horizon; no finite-activity premise is supplied. -/
theorem ae_finite_activity : ∀ᵐ p ∂law μ (Jump D), ∀ S : ℝ≥0, ∃ times : Finset ℝ,
    (times : Set ℝ) ⊆ Ioc 0 S ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ S →
      (∀ u ∈ times, u ∉ Ioc s t) →
        process control hActivity v T hT hv initial p s = process control hActivity v T hT hv initial p t := by
  filter_upwards [TimeDependentGlobalActivity.ae_finite_activity control.function (finite_sublevels control)
    Jump.advance (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv)
      initial 0 μ (ae_exhaustive control hActivity v T hT hv initial μ hCoupling hinit B hB hEnv hInitial)]
    with p hp
  intro S
  obtain ⟨n, hn, he⟩ := hp S
  exact ⟨_, hn, he⟩

/-- The actual global Lyapunov value is integrable at every nonnegative time. -/
theorem integrable_lyapunov (S : ℝ) (hS : 0 ≤ S) :
    Integrable (fun p => control.function (process control hActivity v T hT hv initial p S)) (law μ (Jump D)) :=
  TimeDependentGlobalMoment.integrable control.function (finite_sublevels control)
    Jump.advance (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv)
      initial 0 μ (DeterministicEnvironmentFrozen.measurable_timeRate κ q v T hv hCoupling hT)
      hinit (affineConstant control B) (affineConstant_nonnegative control B hB)
      (function_nonnegative control) (fun x j t _ => timeRate_nonnegative κ q v T j t x) hInitial
      (fun x t _ => clamped_generator_affine_bound control v T hT B hB hEnv t x) S hS

/-- Fatou transfers the finite-level bound to the genuine extended global moment. -/
theorem lyapunov_lintegral_le (S : ℝ) (hS : 0 ≤ S) :
    (∫⁻ p, ENNReal.ofReal (control.function (process control hActivity v T hT hv initial p S))
      ∂law μ (Jump D)) ≤ ENNReal.ofReal ((1 + ∫ a, control.function (initial a) ∂μ) *
        Real.exp (affineConstant control B * S) - 1) :=
  TimeDependentGlobalMoment.lintegral_le control.function (finite_sublevels control)
    Jump.advance (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv)
      initial 0 μ (DeterministicEnvironmentFrozen.measurable_timeRate κ q v T hv hCoupling hT)
      hinit (affineConstant control B) (affineConstant_nonnegative control B hB)
      (function_nonnegative control) (fun x j t _ => timeRate_nonnegative κ q v T j t x) hInitial
      (fun x t _ => clamped_generator_affine_bound control v T hT B hB hEnv t x) S hS

/-- The same explicit bound holds for the ordinary global expectation. -/
theorem lyapunov_expectation_le (S : ℝ) (hS : 0 ≤ S) :
    (∫ p, control.function (process control hActivity v T hT hv initial p S) ∂law μ (Jump D)) ≤
      (1 + ∫ a, control.function (initial a) ∂μ) * Real.exp (affineConstant control B * S) - 1 :=
  TimeDependentGlobalMoment.expectation_le control.function (finite_sublevels control)
    Jump.advance (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv)
      initial 0 μ (DeterministicEnvironmentFrozen.measurable_timeRate κ q v T hv hCoupling hT)
      hinit (affineConstant control B) (affineConstant_nonnegative control B hB)
      (function_nonnegative control) (fun x j t _ => timeRate_nonnegative κ q v T j t x) hInitial
      (fun x t _ => clamped_generator_affine_bound control v T hT B hB hEnv t x) S hS

end CarryingCapacity.DeterministicEnvironmentProcess

namespace CarryingCapacity.DeterministicEnvironmentProcess
open CommonInitialNoise DeterministicEnvironmentLyapunov LyapunovFlowSpace

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T)
  (v : ManuscriptCurves control.function ν (driftConstant control) T hT)

include v in
/-- The prescribed initial law has a genuine Lyapunov moment as a consequence
of membership in the manuscript curve space. -/
theorem manuscript_initial_integrable : Integrable control.function ν.measure := by
  have hi := manuscriptExtension_integrable_and_bound control ν (driftConstant control) T
    (driftConstant_nonnegative control) hT v 0
  rw [manuscriptExtension_initial] at hi
  exact hi.1

/-- The actual global path associated with a manuscript candidate curve,
initialized with that curve's prescribed initial law on the actual product. -/
def manuscriptProcess (p : Sample (State D) (Jump D)) (t : ℝ) : State D :=
  process control hActivity (manuscriptExtension control ν (driftConstant control) T hT v)
    T hT (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn id p t

/-- Genuine canonical exits of the manuscript-curve process. -/
def manuscriptExit (n : ℕ) (p : Sample (State D) (Jump D)) : ℝ≥0∞ :=
  exit control hActivity (manuscriptExtension control ν (driftConstant control) T hT v)
    T hT (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn id n p

theorem manuscript_initial_law :
    (law ν.measure (Jump D)).map (fun p => manuscriptProcess control hActivity ν T hT v p 0) = ν.measure := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  simpa only [Measure.map_id] using initial_law control hActivity
    (manuscriptExtension control ν (driftConstant control) T hT v) T hT
      (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn
        id ν.measure measurable_id

variable (hCoupling : MomentCouplingBound κ q)
include hCoupling

/-- The actual manuscript-curve path is jointly measurable. -/
theorem measurable_manuscriptProcess : Measurable
    (fun p : Sample (State D) (Jump D) × ℝ => manuscriptProcess control hActivity ν T hT v p.1 p.2) :=
  measurable_process control hActivity (manuscriptExtension control ν (driftConstant control) T hT v)
    T hT (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn
      id hCoupling measurable_id

/-- The curve constraint supplies the environmental moment hypothesis and the
initial moment, so its global exit exhaustion has no extra moment premise. -/
theorem manuscript_exhaustive : ∀ᵐ p ∂law ν.measure (Jump D), ∀ S : ℝ≥0, ∃ n : ℕ,
    (S : ℝ≥0∞) < manuscriptExit control hActivity ν T hT v n p := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact ae_exhaustive control hActivity (manuscriptExtension control ν (driftConstant control) T hT v)
    T hT (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn
      id ν.measure hCoupling measurable_id (manuscriptBound control ν (driftConstant control) T)
      (manuscriptBound_nonnegative control ν (driftConstant control) T (driftConstant_nonnegative control) hT)
      (fun s _ => manuscriptExtension_bound control ν (driftConstant control) T
        (driftConstant_nonnegative control) hT v s)
      (manuscript_initial_integrable control ν T hT v)

/-- The actual process obtained from a manuscript candidate curve is càdlàg. -/
theorem manuscript_cadlag : ∀ᵐ p ∂law ν.measure (Jump D),
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt
      (manuscriptProcess control hActivity ν T hT v p) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : State D, Tendsto
      (manuscriptProcess control hActivity ν T hT v p) (𝓝[<] t) (𝓝 y)) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact ae_cadlag control hActivity (manuscriptExtension control ν (driftConstant control) T hT v)
    T hT (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn
      id ν.measure hCoupling measurable_id (manuscriptBound control ν (driftConstant control) T)
      (manuscriptBound_nonnegative control ν (driftConstant control) T (driftConstant_nonnegative control) hT)
      (fun s _ => manuscriptExtension_bound control ν (driftConstant control) T
        (driftConstant_nonnegative control) hT v s)
      (manuscript_initial_integrable control ν T hT v)

/-- The realized manuscript-curve process has finite genuine Lyapunov moments. -/
theorem manuscript_integrable_lyapunov (S : ℝ) (hS : 0 ≤ S) :
    Integrable (fun p => control.function (manuscriptProcess control hActivity ν T hT v p S))
      (law ν.measure (Jump D)) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact integrable_lyapunov control hActivity (manuscriptExtension control ν (driftConstant control) T hT v)
    T hT (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn
      id ν.measure hCoupling measurable_id (manuscriptBound control ν (driftConstant control) T)
      (manuscriptBound_nonnegative control ν (driftConstant control) T (driftConstant_nonnegative control) hT)
      (fun s _ => manuscriptExtension_bound control ν (driftConstant control) T
        (driftConstant_nonnegative control) hT v s)
      (manuscript_initial_integrable control ν T hT v) S hS

/-- The proved global affine-exponential estimate for this actual law-curve
application. This coarse bound is not an invariant-envelope assertion. -/
theorem manuscript_expectation_le (S : ℝ) (hS : 0 ≤ S) :
    (∫ p, control.function (manuscriptProcess control hActivity ν T hT v p S) ∂law ν.measure (Jump D)) ≤
      (1 + ∫ x, control.function x ∂ν.measure) *
        Real.exp (affineConstant control (manuscriptBound control ν (driftConstant control) T) * S) - 1 := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact lyapunov_expectation_le control hActivity
    (manuscriptExtension control ν (driftConstant control) T hT v)
    T hT (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn
      id ν.measure hCoupling measurable_id (manuscriptBound control ν (driftConstant control) T)
      (manuscriptBound_nonnegative control ν (driftConstant control) T (driftConstant_nonnegative control) hT)
      (fun s _ => manuscriptExtension_bound control ν (driftConstant control) T
        (driftConstant_nonnegative control) hT v s)
      (manuscript_initial_integrable control ν T hT v) S hS

end CarryingCapacity.DeterministicEnvironmentProcess

namespace CarryingCapacity.DeterministicEnvironmentProcess
open CommonInitialNoise DeterministicEnvironmentLyapunov DeterministicEnvironmentFrozen

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))
  {A : Type*} [MeasurableSpace A] (initial : A → State D)

/-- The actual predictable pre-jump version of the global environment process. -/
def preState (p : Sample A (Jump D)) (t : ℝ) : State D :=
  TimeDependentGlobalCounting.preState control.function (finite_sublevels control) Jump.advance
    (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv) initial 0 p t

/-- Actual accepted increments on a time horizon, with no spatial indicator or height cap. -/
def horizonIncrement (F : State D → ℝ) (j : Jump D) (S : ℝ) :
    Sample A (Jump D) × (ℝ × ℝ) → ℝ :=
  TimeDependentGlobalCounting.horizonIncrement control.function (finite_sublevels control) Jump.advance
    (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv) initial 0 F j S

omit [MeasurableSpace A] in
/-- On the selected horizon the no-cutoff threshold uses the original
prescribed environment, without endpoint clamping changing any rate. -/
theorem horizonIncrement_apply_on_horizon (F : State D → ℝ) (j : Jump D)
    (S : ℝ) (hS : S ≤ T) (p : Sample A (Jump D)) (z : ℝ × ℝ) :
    horizonIncrement control hActivity v T hT hv initial F j S (p,z) =
      if z.1 ∈ Ioc 0 S ∧ z.2 ≤ q.rate j (preState control hActivity v T hT hv initial p z.1) (v z.1)
      then F (Jump.advance j (preState control hActivity v T hT hv initial p z.1)) -
        F (preState control hActivity v T hT hv initial p z.1) else 0 := by
  change TimeDependentGlobalCounting.horizonIncrement _ _ _ _ _ _ _ _ _ _ _ = _
  rw [TimeDependentGlobalCounting.horizonIncrement_apply]
  by_cases hz : z.1 ∈ Ioc 0 S
  · simp only [hz, true_and, timeRate_eq κ q v T j z.1 ⟨hz.1.le, hz.2.trans hS⟩]
    rfl
  · simp only [hz, false_and, ↓reduceIte]

/-- Predictability is proved on every sample, independently of moment and exit estimates. -/
theorem measurable_horizonIncrement (hCoupling : MomentCouplingBound κ q)
    (hinit : Measurable initial) (F : State D → ℝ) (j : Jump D) (S : ℝ) :
    Measurable[PredictableSets.predictable (filtration A (Jump D))]
      (horizonIncrement control hActivity v T hT hv initial F j S) :=
  TimeDependentGlobalCounting.measurable_horizonIncrement control.function (finite_sublevels control)
    Jump.advance (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv)
      initial 0 (DeterministicEnvironmentFrozen.measurable_timeRate κ q v T hv hCoupling hT) hinit F j S

variable (μ : Measure A) [IsProbabilityMeasure μ]
  (hCoupling : MomentCouplingBound κ q) (hinit : Measurable initial)
  (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ t ∈ Icc 0 T, LyapunovFlowSpace.lyapunovIntegral control.function (v t) ≤ ENNReal.ofReal B)
  (hInitial : Integrable (fun a => control.function (initial a)) μ)
include hCoupling hinit hB hEnv hInitial

/-- The predictable version is the actual global path's left limit, simultaneously
at every positive time, with exhaustion already derived from the paper hypotheses. -/
theorem ae_preState_eq_leftLim : ∀ᵐ p ∂law μ (Jump D), ∀ t : ℝ, 0 < t →
    preState control hActivity v T hT hv initial p t =
      Function.leftLim (process control hActivity v T hT hv initial p) t :=
  TimeDependentGlobalCounting.ae_preState_eq_leftLim control.function (finite_sublevels control)
    Jump.advance (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv)
      initial 0 μ (ae_exhaustive control hActivity v T hT hv initial μ hCoupling hinit B hB hEnv hInitial)

/-- Actual pathwise integrability of every test increment on every finite horizon. -/
theorem ae_integrable_horizonIncrement : ∀ᵐ p ∂law μ (Jump D), ∀ (S : ℝ≥0) (F : State D → ℝ) (j : Jump D),
    Integrable (fun z => horizonIncrement control hActivity v T hT hv initial F j S (p,z))
      (MarkedNoise.countingMeasure j p.2) :=
  TimeDependentGlobalCounting.ae_integrable_horizonIncrement control.function (finite_sublevels control)
    Jump.advance (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv)
      initial 0 μ (ae_exhaustive control hActivity v T hT hv initial μ hCoupling hinit B hB hEnv hInitial)

/-- The actual global path solves the no-cutoff counting equation, with no
counting identity or exhaustion supplied as a hypothesis. -/
theorem ae_counting_identity (F : State D → ℝ) : ∀ᵐ p ∂law μ (Jump D), ∀ S : ℝ≥0,
    F (process control hActivity v T hT hv initial p S) - F (initial p.1) =
      ∑ j, ∫ z, horizonIncrement control hActivity v T hT hv initial F j S (p,z)
        ∂MarkedNoise.countingMeasure j p.2 :=
  TimeDependentGlobalCounting.ae_testFunction_counting_identity control.function (finite_sublevels control)
    Jump.advance (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv)
      initial 0 μ F (ae_exhaustive control hActivity v T hT hv initial μ hCoupling hinit B hB hEnv hInitial)

/-- On the original horizon the equation is exactly the manuscript's
unrestricted event-time rate threshold. -/
theorem ae_counting_identity_on_horizon (F : State D → ℝ) : ∀ᵐ p ∂law μ (Jump D),
    ∀ S : ℝ≥0, (S : ℝ) ≤ T →
    F (process control hActivity v T hT hv initial p S) - F (initial p.1) =
      ∑ j, ∫ z : ℝ × ℝ,
        (if z.1 ∈ Ioc 0 (S : ℝ) ∧ z.2 ≤ q.rate j (preState control hActivity v T hT hv initial p z.1) (v z.1)
        then F (Jump.advance j (preState control hActivity v T hT hv initial p z.1)) -
          F (preState control hActivity v T hT hv initial p z.1) else 0)
        ∂MarkedNoise.countingMeasure j p.2 := by
  filter_upwards [ae_counting_identity control hActivity v T hT hv initial μ hCoupling hinit B hB hEnv hInitial F]
    with p hp
  intro S hS
  rw [hp S]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_congr_ae (Eventually.of_forall (fun z =>
    horizonIncrement_apply_on_horizon control hActivity v T hT hv initial F j S hS p z))

/-- All particle-coordinate counting equations hold on one common event. -/
theorem ae_coordinate_counting_identity : ∀ᵐ p ∂law μ (Jump D), ∀ i : Fin D, ∀ S : ℝ≥0,
    ((process control hActivity v T hT hv initial p S) i : ℝ) - (initial p.1 i : ℝ) =
      ∑ j, ∫ z, horizonIncrement control hActivity v T hT hv initial (fun x => (x i : ℝ)) j S (p,z)
        ∂MarkedNoise.countingMeasure j p.2 :=
  ae_all_iff.mpr (fun i =>
    ae_counting_identity control hActivity v T hT hv initial μ hCoupling hinit B hB hEnv hInitial
      (fun x => (x i : ℝ)))

end CarryingCapacity.DeterministicEnvironmentProcess

namespace CarryingCapacity.DeterministicEnvironmentProcess
open CommonInitialNoise DeterministicEnvironmentLyapunov DeterministicEnvironmentFrozen

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))
  {A : Type*} [MeasurableSpace A] (initial : A → State D)
  (μ : Measure A) [IsProbabilityMeasure μ]
  (hCoupling : MomentCouplingBound κ q) (hinit : Measurable initial)
  (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ t ∈ Icc 0 T, LyapunovFlowSpace.lyapunovIntegral control.function (v t) ≤ ENNReal.ofReal B)
  (hInitial : Integrable (fun a => control.function (initial a)) μ)
include hCoupling hinit hB hEnv hInitial

/-- Pathwise uniqueness for the actual endpoint-clamped environment, using
only the finite particle-coordinate equations of a candidate. The candidate
has no moment, finite-activity, localization or measurability premise. -/
theorem ae_eq_of_coordinate_equations (X : Sample A (Jump D) → ℝ → State D)
    (hcadlag : ∀ᵐ p ∂law μ (Jump D),
      (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (X p) (Ici t) t) ∧
      (∀ t : ℝ, 0 < t → ∃ y : State D, Tendsto (X p) (𝓝[<] t) (𝓝 y)))
    (hzero : ∀ᵐ p ∂law μ (Jump D), X p 0 = initial p.1)
    (heq : ∀ i : Fin D, ∀ᵐ p ∂law μ (Jump D), ∀ S : ℝ≥0,
      (X p S i : ℝ) - (initial p.1 i : ℝ) =
        ∑ j, ∫ z, TimeDependentGlobalUniqueness.candidateIncrement Jump.advance
          (timeRate κ q v T) X 0 (fun x => (x i : ℝ)) j S (p,z)
            ∂MarkedNoise.countingMeasure j p.2) :
    ∀ᵐ p ∂law μ (Jump D), ∀ t : ℝ, 0 ≤ t →
      X p t = process control hActivity v T hT hv initial p t := by
  apply TimeDependentGlobalUniqueness.ae_candidate_eq_process_of_separating_tests
    control.function (finite_sublevels control) Jump.advance (timeRate κ q v T)
    (exists_uniform_rate_bounds control v T hT hActivity hv) initial 0 μ
    (fun i : Fin D => fun x : State D => (x i : ℝ))
  · intro x y hxy
    funext i
    exact_mod_cast hxy i
  · exact ae_exhaustive control hActivity v T hT hv initial μ hCoupling hinit B hB hEnv hInitial
  · exact hcadlag
  · exact hzero
  · exact heq

end CarryingCapacity.DeterministicEnvironmentProcess
