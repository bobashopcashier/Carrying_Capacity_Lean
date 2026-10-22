import CarryingCapacity.CommonInitialStopping
import CarryingCapacity.ThinningKernel

/-!
# Actual frozen paths on increasing Lyapunov sublevels

The active region at index n is exactly {V < n+1}. Its rate bound is chosen
from the proved finite-set bound. All levels use the same initial record and
the same marked noise. Countable intersections give simultaneous exit
monotonicity and stopped compatibility for the actual family.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical ENNReal

namespace CarryingCapacity.LyapunovLocalization
open CommonInitialNoise

variable {A E J : Type*} [Fintype J]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)

/-- Positive integer thresholds, indexed from zero for reciprocal tail bounds. -/
def active (n : ℕ) : Finset E := (hfinite (n + 1)).toFinset

@[simp] theorem mem_active (n : ℕ) (x : E) :
    x ∈ active V hfinite n ↔ V x < (n : ℝ) + 1 := Set.Finite.mem_toFinset _

theorem active_mono : Monotone (active V hfinite) := by
  intro n m hnm x hx
  rw [mem_active] at hx ⊢
  exact hx.trans_le (by exact_mod_cast Nat.add_le_add_right hnm 1)

theorem exists_active (x : E) : ∃ n, x ∈ active V hfinite n := by
  obtain ⟨n, hn⟩ := exists_nat_gt (V x)
  exact ⟨n, (mem_active V hfinite n x).mpr (by linarith)⟩

variable (jump : J → E → E) (rate : J → E → ℝ)

/-- A finite positive bound derived from the actual rates on the active set. -/
def rateBound (n : ℕ) : ℝ :=
  Classical.choose (FrozenProcess.exists_positive_rate_bound (active V hfinite n) rate)

theorem rateBound_pos (n : ℕ) : 0 < rateBound V hfinite rate n :=
  (Classical.choose_spec (FrozenProcess.exists_positive_rate_bound (active V hfinite n) rate)).1

theorem rate_le_bound (n : ℕ) (x : E) (hx : x ∈ active V hfinite n) (j : J) :
    rate j x ≤ rateBound V hfinite rate n :=
  (Classical.choose_spec (FrozenProcess.exists_positive_rate_bound (active V hfinite n) rate)).2 x hx j

variable [DecidableEq E] (initial : A → E)

/-- The actual finite-cutoff process at a positive integer Lyapunov level. -/
def path (n : ℕ) (p : Sample A J) (t : ℝ) : E :=
  process (active V hfinite n) jump rate initial (rateBound V hfinite rate n) p t

/-- The genuine first exit of that same process. -/
def exit (n : ℕ) (p : Sample A J) : ℝ≥0∞ :=
  firstExit (active V hfinite n) jump rate initial (rateBound V hfinite rate n) p

variable [MeasurableSpace A] (μ : Measure A)

theorem ae_exit_mono : ∀ᵐ p ∂law μ J,
    Monotone (fun n => exit V hfinite jump rate initial n p) := by
  have hh : ∀ n m : ℕ, ∀ᵐ p ∂law μ J, n ≤ m →
      exit V hfinite jump rate initial n p ≤ exit V hfinite jump rate initial m p := by
    intro n m
    by_cases hnm : n ≤ m
    · filter_upwards [ae_firstExit_mono (active V hfinite n) jump rate initial μ
        (active V hfinite m) (active_mono V hfinite hnm)
        (rateBound V hfinite rate n) (rateBound V hfinite rate m)
        (rate_le_bound V hfinite rate n) (rate_le_bound V hfinite rate m)] with p hp
      exact fun _ => hp
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hnm h))
  filter_upwards [ae_all_iff.mpr (fun n => ae_all_iff.mpr (hh n))] with p hp
  exact fun n m hnm => hp n m hnm

theorem ae_stopped_compatible : ∀ᵐ p ∂law μ J, ∀ n m : ℕ, n ≤ m →
    ∀ t : ℝ, 0 ≤ t → CommonFrozenExit.stopped
      (exit V hfinite jump rate initial n p) (path V hfinite jump rate initial m p) t =
        path V hfinite jump rate initial n p t := by
  have hh : ∀ n m : ℕ, ∀ᵐ p ∂law μ J, n ≤ m → ∀ t : ℝ, 0 ≤ t →
      CommonFrozenExit.stopped (exit V hfinite jump rate initial n p)
        (path V hfinite jump rate initial m p) t = path V hfinite jump rate initial n p t := by
    intro n m
    by_cases hnm : n ≤ m
    · filter_upwards [ae_stopped_nested (active V hfinite n) jump rate initial μ
        (active V hfinite m) (active_mono V hfinite hnm)
        (rateBound V hfinite rate n) (rateBound V hfinite rate m)
        (rate_le_bound V hfinite rate n) (rate_le_bound V hfinite rate m)] with p hp
      exact fun _ => hp
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hnm h))
  exact ae_all_iff.mpr (fun n => ae_all_iff.mpr (hh n))

/-- Agreement includes the first exit jump, not only times strictly before it. -/
theorem ae_compatible : ∀ᵐ p ∂law μ J, ∀ n m : ℕ, n ≤ m →
    ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t ≤ exit V hfinite jump rate initial n p →
      path V hfinite jump rate initial m p t = path V hfinite jump rate initial n p t := by
  filter_upwards [ae_stopped_compatible V hfinite jump rate initial μ] with p hp
  intro n m hnm t ht hbefore
  have he := hp n m hnm t ht
  by_cases htop : exit V hfinite jump rate initial n p = ⊤
  · simpa only [CommonFrozenExit.stopped, htop, ↓reduceIte] using he
  · have ht' : t ≤ (exit V hfinite jump rate initial n p).toReal := by
      simpa only [ENNReal.toReal_ofReal ht] using ENNReal.toReal_mono htop hbefore
    simpa only [CommonFrozenExit.stopped, htop, ↓reduceIte, min_eq_left ht'] using he

section Measurability
variable [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  (hinit : Measurable initial)
include hinit

omit μ in
theorem measurable_path (n : ℕ) : Measurable
    (fun p : Sample A J × ℝ => path V hfinite jump rate initial n p.1 p.2) :=
  measurable_process (active V hfinite n) jump rate initial hinit (rateBound V hfinite rate n)

omit μ in
theorem measurable_path_at (n : ℕ) (t : ℝ) :
    Measurable[filtration A J t] (fun p => path V hfinite jump rate initial n p t) :=
  measurable_process_at (active V hfinite n) jump rate initial hinit (rateBound V hfinite rate n) t

theorem aemeasurable_exit (n : ℕ) :
    AEMeasurable (exit V hfinite jump rate initial n) (law μ J) :=
  CommonInitialStopping.aemeasurable_firstExit μ (active V hfinite n) jump rate initial
    hinit (rateBound V hfinite rate n)

end Measurability
end CarryingCapacity.LyapunovLocalization
