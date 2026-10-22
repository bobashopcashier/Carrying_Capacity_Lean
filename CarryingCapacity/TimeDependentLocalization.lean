import CarryingCapacity.LyapunovLocalization
import CarryingCapacity.TimeDependentFrozenExit
import CarryingCapacity.TimeDependentInitial

/-!
# Actual spatial localization for time-dependent rates

Each positive integer Lyapunov sublevel is finite. A supplied upper bound for
the time-dependent rates on each sublevel determines a positive height cutoff.
The paths are the actual initialized chronological constructions, all using
the same noise. Their genuine exits are monotone and their stopped paths are
compatible, as consequences of the proved frozen-path construction.

Only the numerical rate bounds are hypotheses; no process, compatibility,
exit, or measurability conclusion is assumed. For a fixed construction horizon,
the deterministic environment supplies these bounds after time clamping.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical ENNReal

namespace CarryingCapacity.TimeDependentLocalization
open CommonInitialNoise LyapunovLocalization

variable {A E J : Type*} [Fintype J]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (hbounded : ∀ n : ℕ, ∃ C : ℝ,
    ∀ x ∈ active V hfinite n, ∀ j t, rate j t x ≤ C)

/-- A positive finite cutoff chosen from the actual active-region bound. -/
def rateBound (n : ℕ) : ℝ := max (Classical.choose (hbounded n)) 0 + 1

omit [Fintype J] in
theorem rateBound_pos (n : ℕ) : 0 < rateBound V hfinite rate hbounded n := by
  unfold rateBound
  have h := le_max_right (Classical.choose (hbounded n)) 0
  linarith

omit [Fintype J] in
theorem rate_le_bound (n : ℕ) (x : E) (hx : x ∈ active V hfinite n) (j : J) (t : ℝ) :
    rate j t x ≤ rateBound V hfinite rate hbounded n := by
  exact (Classical.choose_spec (hbounded n) x hx j t).trans
    ((le_max_left _ _).trans (by unfold rateBound; linarith))

variable [DecidableEq E] (initial : A → E)

/-- The actual time-dependent frozen path at spatial level n. -/
def path (n : ℕ) (p : Sample A J) (t : ℝ) : E :=
  TimeDependentInitial.process (active V hfinite n) jump rate initial
    (rateBound V hfinite rate hbounded n) p t

/-- The genuine first exit of that same constructed frozen path. -/
def exit (n : ℕ) (p : Sample A J) : ℝ≥0∞ :=
  TimeDependentFrozenExit.firstExit (active V hfinite n) jump rate
    (rateBound V hfinite rate hbounded n) (initial p.1) p.2

omit [Fintype J] in
/-- Before its actual exit, a localized state is in its Lyapunov sublevel. -/
theorem path_mem_before_exit (n : ℕ) (p : Sample A J) {t : ℝ} (ht : 0 ≤ t)
    (hbefore : ENNReal.ofReal t < exit V hfinite jump rate hbounded initial n p) :
    path V hfinite jump rate hbounded initial n p t ∈ active V hfinite n :=
  TimeDependentFrozenExit.process_mem_before_firstExit (active V hfinite n) jump rate
    (rateBound V hfinite rate hbounded n) (initial p.1) p.2 ht hbefore

variable [MeasurableSpace A] (μ : Measure A)

/-- Countably many actual levels have simultaneously increasing first exits. -/
theorem ae_exit_mono : ∀ᵐ p ∂law μ J,
    Monotone (fun n => exit V hfinite jump rate hbounded initial n p) := by
  have hh : ∀ n m : ℕ, ∀ᵐ p ∂law μ J, n ≤ m →
      exit V hfinite jump rate hbounded initial n p ≤
        exit V hfinite jump rate hbounded initial m p := by
    intro n m
    by_cases hnm : n ≤ m
    · filter_upwards [ae_noise μ
        (TimeDependentFrozenExit.ae_firstExit_mono (active V hfinite n) jump rate
          (active V hfinite m) (active_mono V hfinite hnm)
          (rateBound V hfinite rate hbounded n) (rateBound V hfinite rate hbounded m)
          (rate_le_bound V hfinite rate hbounded n) (rate_le_bound V hfinite rate hbounded m))]
        with p hp
      exact fun _ => hp (initial p.1)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hnm h))
  filter_upwards [ae_all_iff.mpr (fun n => ae_all_iff.mpr (hh n))] with p hp
  exact fun n m hnm => hp n m hnm

/-- The actual larger path stopped at the smaller actual exit equals the
smaller frozen path, including its exit jump. -/
theorem ae_stopped_compatible : ∀ᵐ p ∂law μ J, ∀ n m : ℕ, n ≤ m →
    ∀ t : ℝ, 0 ≤ t → CommonFrozenExit.stopped
      (exit V hfinite jump rate hbounded initial n p)
      (path V hfinite jump rate hbounded initial m p) t =
        path V hfinite jump rate hbounded initial n p t := by
  have hh : ∀ n m : ℕ, ∀ᵐ p ∂law μ J, n ≤ m → ∀ t : ℝ, 0 ≤ t →
      CommonFrozenExit.stopped (exit V hfinite jump rate hbounded initial n p)
        (path V hfinite jump rate hbounded initial m p) t =
          path V hfinite jump rate hbounded initial n p t := by
    intro n m
    by_cases hnm : n ≤ m
    · filter_upwards [ae_noise μ
        (TimeDependentFrozenExit.ae_stopped_nested (active V hfinite n) jump rate
          (active V hfinite m) (active_mono V hfinite hnm)
          (rateBound V hfinite rate hbounded n) (rateBound V hfinite rate hbounded m)
          (rate_le_bound V hfinite rate hbounded n) (rate_le_bound V hfinite rate hbounded m))]
        with p hp
      exact fun _ => hp (initial p.1)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hnm h))
  exact ae_all_iff.mpr (fun n => ae_all_iff.mpr (hh n))

/-- Compatibility is valid through the exit time, not just strictly before it. -/
theorem ae_compatible : ∀ᵐ p ∂law μ J, ∀ n m : ℕ, n ≤ m →
    ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t ≤ exit V hfinite jump rate hbounded initial n p →
      path V hfinite jump rate hbounded initial m p t =
        path V hfinite jump rate hbounded initial n p t := by
  filter_upwards [ae_stopped_compatible V hfinite jump rate hbounded initial μ] with p hp
  intro n m hnm t ht hbefore
  have he := hp n m hnm t ht
  by_cases htop : exit V hfinite jump rate hbounded initial n p = ⊤
  · simpa only [CommonFrozenExit.stopped, htop, ↓reduceIte] using he
  · have ht' : t ≤ (exit V hfinite jump rate hbounded initial n p).toReal := by
      simpa only [ENNReal.toReal_ofReal ht] using ENNReal.toReal_mono htop hbefore
    simpa only [CommonFrozenExit.stopped, htop, ↓reduceIte, min_eq_left ht'] using he

section Measurability
variable [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  (hRate : ∀ j x, Measurable (fun t => rate j t x)) (hinit : Measurable initial)
include hRate hinit

omit μ in
theorem measurable_path (n : ℕ) : Measurable
    (fun p : Sample A J × ℝ => path V hfinite jump rate hbounded initial n p.1 p.2) :=
  TimeDependentInitial.measurable_process (active V hfinite n) jump rate initial hRate hinit
    (rateBound V hfinite rate hbounded n)

omit μ in
theorem measurable_path_at (n : ℕ) (t : ℝ) :
    Measurable[filtration A J t] (fun p => path V hfinite jump rate hbounded initial n p t) :=
  TimeDependentInitial.measurable_process_at (active V hfinite n) jump rate initial hRate hinit
    (rateBound V hfinite rate hbounded n) t

end Measurability
end CarryingCapacity.TimeDependentLocalization
