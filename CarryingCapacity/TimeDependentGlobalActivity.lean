import CarryingCapacity.TimeDependentGlobalProcess
import CarryingCapacity.GlobalLocalizedActivity

/-!
# Finite activity of the actual time-dependent global patch

Exhaustion of the genuine canonical exit times selects one frozen cutoff for
an entire bounded horizon. The actual chronological box at that cutoff is a
finite list, and every value of the global path is the recursion through its
time-filtered prefix. Its finite set of proposal times therefore contains
all possible changes, including the retained exit jump.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal Topology

namespace CarryingCapacity.TimeDependentGlobalActivity
open CommonInitialNoise TimeDependentLocalization ChronologicalEvents
open LyapunovLocalization (active)
open GlobalLocalizedActivity (filter_time_eq_of_no_event)

variable {A E J : Type*} [DecidableEq E] [Fintype J]
  [TopologicalSpace E] [PolishSpace E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (hbounded : ∀ n : ℕ, ∃ C : ℝ,
    ∀ x ∈ active V hfinite n, ∀ j t, rate j t x ≤ C)
  (initial : A → E) (e : E)

/-- The actual finite proposal list used at a localization level and horizon. -/
def horizonList (n : ℕ) (p : Sample A J) (T : ℝ) : List (Event J) :=
  boxedList (p.2, T, rateBound V hfinite rate hbounded n)

/-- The finite times of those actual proposals, including rejected ones. -/
def horizonTimes (n : ℕ) (p : Sample A J) (T : ℝ) : Finset ℝ :=
  ((horizonList V hfinite rate hbounded n p T).map
    (fun i => (MarkedNoise.point i.1 p.2 i.2).1)).toFinset

omit [Fintype J] [DecidableEq E] [TopologicalSpace E] [PolishSpace E] in
theorem mem_horizonTimes (n : ℕ) (p : Sample A J) (T t : ℝ) :
    t ∈ horizonTimes V hfinite rate hbounded n p T ↔ ∃ i ∈ horizonList V hfinite rate hbounded n p T,
      (MarkedNoise.point i.1 p.2 i.2).1 = t := by
  simp only [horizonTimes, List.mem_toFinset, List.mem_map]

variable [MeasurableSpace A] (μ : Measure A)

/-- A single actual finite marked list generates every global path value on
the horizon, with the physical-height acceptance rule evaluated at the actual event time. -/
theorem ae_run_on_horizon
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rate hbounded initial n p) :
    ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n, ∀ t : ℝ, 0 ≤ t → t ≤ T →
      TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p t =
        Freezing.run (active V hfinite n) jump (TimeDependentFrozenProcess.eventDecode rate p.2)
          (initial p.1) ((horizonList V hfinite rate hbounded n p T).filter
            (fun i => decide ((MarkedNoise.point i.1 p.2 i.2).1 ≤ t))) := by
  filter_upwards [TimeDependentGlobalProcess.ae_agrees_on_horizon
    V hfinite jump rate hbounded initial e μ hexhaust,
    ae_noise μ (ae_boxedList_time_filter (J := J))] with p hp hfilter
  intro T
  obtain ⟨n, hn⟩ := hp T
  refine ⟨n, fun t ht htT => ?_⟩
  rw [hn n le_rfl t ht htT]
  change TimeDependentFrozenProcess.runBox (active V hfinite n) jump rate (initial p.1)
    (p.2, t, rateBound V hfinite rate hbounded n) = _
  rw [TimeDependentFrozenProcess.runBox, horizonList, hfilter t T _ htT]

omit [DecidableEq E] [TopologicalSpace E] [PolishSpace E] in
/-- The candidate change times really are positive proposal times within
the specified horizon. The statement is simultaneous in every level and time. -/
theorem ae_horizonTimes_subset : ∀ᵐ p ∂law μ J, ∀ n : ℕ, ∀ T : ℝ,
    (horizonTimes V hfinite rate hbounded n p T : Set ℝ) ⊆ Ioc 0 T := by
  filter_upwards [ae_noise μ (ae_boxedList_mem (J := J)),
    ae_noise μ (MarkedNoise.ae_positive_points (J := J))] with p hmem hpos
  intro n T t ht
  obtain ⟨i, hi, rfl⟩ := (mem_horizonTimes V hfinite rate hbounded n p T t).mp ht
  exact ⟨(hpos i.1 i.2).1, ((hmem T _ i).mp hi).1⟩

/-- On every bounded horizon, all changes of the actual global path occur
among a finite set of actual proposal times. This is derived from the finite
list recursion, rather than supplied as a path assumption. -/
theorem ae_finite_activity
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rate hbounded initial n p) :
    ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (horizonTimes V hfinite rate hbounded n p T : Set ℝ) ⊆ Ioc 0 T ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        (∀ u ∈ horizonTimes V hfinite rate hbounded n p T, u ∉ Ioc s t) →
        TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p s =
          TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p t := by
  filter_upwards [ae_run_on_horizon V hfinite jump rate hbounded initial e μ hexhaust,
    ae_horizonTimes_subset V hfinite rate hbounded μ] with p hp htimes
  intro T
  obtain ⟨n, hn⟩ := hp T
  refine ⟨n, htimes n T, ?_⟩
  intro s t hs hst htT hno
  rw [hn s hs (hst.trans htT), hn t (hs.trans hst) htT]
  congr 1
  apply filter_time_eq_of_no_event _ _ hst
  intro i hi
  exact hno _ ((mem_horizonTimes V hfinite rate hbounded n p T _).mpr ⟨i, hi, rfl⟩)

/-- A finite deterministic enlargement for the selected cutoff, together
with the sampled initial state, contains the entire global finite-horizon path. -/
theorem ae_finite_range_on_horizon
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rate hbounded initial n p) :
    ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n, ∀ t : ℝ, 0 ≤ t → t ≤ T →
      TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p t ∈
        insert (initial p.1) (Freezing.oneStepEnlargement (active V hfinite n) jump) := by
  filter_upwards [ae_run_on_horizon V hfinite jump rate hbounded initial e μ hexhaust] with p hp
  intro T
  obtain ⟨n, hn⟩ := hp T
  refine ⟨n, fun t ht htT => ?_⟩
  rw [hn t ht htT, Finset.mem_insert]
  exact (Freezing.run_mem_or_eq_initial (active V hfinite n) jump
    (TimeDependentFrozenProcess.eventDecode rate p.2) (initial p.1) _).symm

end CarryingCapacity.TimeDependentGlobalActivity
