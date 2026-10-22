import CarryingCapacity.TimeDependentLyapunovBound
import CarryingCapacity.TimeDependentInitialExit
import CarryingCapacity.TimeDependentGlobalActivity

/-!
# Actual time-dependent Lyapunov non-explosion and global patch

The hypotheses are finite Lyapunov sublevels, nonnegative rates, an affine
bound on the unfrozen generator, and an integrable initial Lyapunov value.
Dynkin and Gronwall give uniform actual frozen expectations. The genuine exits
therefore exhaust every finite horizon almost surely, so the measurable common-
noise patch agrees with one frozen construction throughout each finite horizon.
There are no exit, expectation, or exhaustion assumptions in the conclusions.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.TimeDependentNonexplosion
open CommonInitialNoise LyapunovLocalization TimeDependentLocalization

variable {A E J : Type*} [MeasurableSpace A] [DecidableEq E] [Fintype J]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (hbounded : ∀ n : ℕ, ∃ C : ℝ, ∀ x ∈ active V hfinite n, ∀ j t, rate j t x ≤ C)
  (initial : A → E) (e : E)
  (μ : Measure A) [IsProbabilityMeasure μ]
  (hRate : ∀ j x, Measurable (fun t => rate j t x)) (hinit : Measurable initial) (b : ℝ) (hb : 0 ≤ b)
  (hVnonneg : ∀ x, 0 ≤ V x) (hq : ∀ x j t, 0 ≤ t → 0 ≤ rate j t x)
  (hV : Integrable (fun a => V (initial a)) μ)
  (hdrift : ∀ x t, 0 ≤ t → (∑ j, rate j t x * (V (jump j x) - V x)) ≤ b * (1 + V x))

/-- The deterministic affine-exponential bound from the actual initial law. -/
def exponentialBound (T : ℝ) : ℝ :=
  (1 + ∫ a, V (initial a) ∂μ) * Real.exp (b * T) - 1

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E]
  [IsProbabilityMeasure μ] in
/-- The prescribed initial value holds without an initial moment or any
Lyapunov drift assumption. -/
theorem ae_global_initial : ∀ᵐ p ∂law μ J,
    TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p 0 = initial p.1 :=
  TimeDependentGlobalProcess.ae_process_zero V hfinite jump rate hbounded initial e μ

include e hRate hinit hV

/-- Future localized integrability follows from the initial moment and the
proved finite-active-region counting identity. -/
theorem integrable_localized_value (n : ℕ) (T : ℝ) :
    Integrable (fun p => V (path V hfinite jump rate hbounded initial n p T)) (law μ J) :=
  TimeDependentDynkin.integrable_testFunction (active V hfinite n) jump rate initial μ hRate hinit
    (rateBound V hfinite rate hbounded n) e V T hV

include b hb hVnonneg hq hdrift

/-- Uniform expectation control is derived, rather than imposed on the actual paths. -/
theorem localized_expectation_le (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    (∫ p, V (path V hfinite jump rate hbounded initial n p T) ∂law μ J) ≤
      exponentialBound V initial μ b T := by
  exact TimeDependentLyapunovBound.expectation_le_exp_sub_one (active V hfinite n) jump rate initial
    μ hRate hinit (rateBound V hfinite rate hbounded n) e V b hb hVnonneg
    (fun x _ j t ht => hq x j t ht)
    (fun x hx j t _ => rate_le_bound V hfinite rate hbounded n x hx j t) hV
    (fun t ht x hx => by
      simpa only [TimeDependentGeneratorIntegral.frozenGenerator, FrozenProcess.frozenGenerator, if_pos hx]
        using hdrift x t ht) T hT

/-- Explicit reciprocal tail bound for the genuine first exit of each actual
integer-sublevel frozen construction. -/
theorem exit_probability_le (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    (law μ J) {p | exit V hfinite jump rate hbounded initial n p ≤ ENNReal.ofReal T} ≤
      ENNReal.ofReal (exponentialBound V initial μ b T) / ((n + 1 : ℕ) : ℝ≥0∞) := by
  simpa only [ENNReal.ofReal_natCast] using
    TimeDependentInitialExit.measure_firstExit_le_of_expectation_le μ (active V hfinite n)
      jump rate initial V hVnonneg ((n + 1 : ℕ) : ℝ) (rateBound V hfinite rate hbounded n) T
      (exponentialBound V initial μ b T) (by positivity) hT
      (fun x => by simpa only [Nat.cast_add, Nat.cast_one] using mem_active V hfinite n x)
      (integrable_localized_value V hfinite jump rate hbounded initial e μ hRate hinit hV n T)
      (localized_expectation_le V hfinite jump rate hbounded initial e μ hRate hinit b hb hVnonneg hq hV hdrift n T hT)

/-- The actual localization exits exhaust every finite nonnegative horizon
on one probability-one event, as a consequence of the Lyapunov assumptions. -/
theorem ae_exhaustive : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n : ℕ,
    (T : ℝ≥0∞) < exit V hfinite jump rate hbounded initial n p := by
  apply Freezing.ae_exhaustive_of_reciprocal_bounds (law μ J)
    (exit V hfinite jump rate hbounded initial)
    (fun k => ENNReal.ofReal (exponentialBound V initial μ b k))
    (fun _ => ENNReal.ofReal_ne_top)
  intro k n
  simpa only [ENNReal.ofReal_natCast] using
    exit_probability_le V hfinite jump rate hbounded initial e μ hRate hinit b hb hVnonneg hq hV hdrift n k
      (Nat.cast_nonneg k)

/-- On each finite horizon the actual measurable global patch is eventually
identical to all sufficiently high localization levels. -/
theorem ae_global_agrees_on_horizon : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n, ∀ m, n ≤ m →
    ∀ t : ℝ, 0 ≤ t → t ≤ T →
      TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p t =
        path V hfinite jump rate hbounded initial m p t :=
  TimeDependentGlobalProcess.ae_agrees_on_horizon V hfinite jump rate hbounded initial e μ
    (ae_exhaustive V hfinite jump rate hbounded initial e μ hRate hinit b hb hVnonneg hq hV hdrift)

/-- The actual global patch has right-continuous paths and left limits,
with exhaustion supplied by the model hypotheses rather than assumed. -/
theorem ae_global_cadlag : ∀ᵐ p ∂law μ J,
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt
      (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : E, Tendsto
      (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p) (𝓝[<] t) (𝓝 y)) :=
  TimeDependentGlobalProcess.ae_process_cadlag V hfinite jump rate hbounded initial e μ
    (ae_exhaustive V hfinite jump rate hbounded initial e μ hRate hinit b hb hVnonneg hq hV hdrift)

/-- Every finite horizon has finitely many actual proposal times containing
all changes of the nonexplosive global path. -/
theorem ae_global_finite_activity : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
    (TimeDependentGlobalActivity.horizonTimes V hfinite rate hbounded n p T : Set ℝ) ⊆ Ioc 0 T ∧
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
      (∀ u ∈ TimeDependentGlobalActivity.horizonTimes V hfinite rate hbounded n p T,
        u ∉ Ioc s t) →
      TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p s =
        TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p t :=
  TimeDependentGlobalActivity.ae_finite_activity V hfinite jump rate hbounded initial e μ
    (ae_exhaustive V hfinite jump rate hbounded initial e μ hRate hinit b hb hVnonneg hq hV hdrift)

/-- The actual finite-horizon path has finite range, derived from localization. -/
theorem ae_global_finite_range : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n, ∀ t : ℝ, 0 ≤ t → t ≤ T →
    TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p t ∈
      insert (initial p.1) (Freezing.oneStepEnlargement (active V hfinite n) jump) :=
  TimeDependentGlobalActivity.ae_finite_range_on_horizon V hfinite jump rate hbounded initial e μ
    (ae_exhaustive V hfinite jump rate hbounded initial e μ hRate hinit b hb hVnonneg hq hV hdrift)

end CarryingCapacity.TimeDependentNonexplosion
