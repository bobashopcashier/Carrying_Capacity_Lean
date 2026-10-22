import CarryingCapacity.LyapunovLocalization
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# A measurable common-noise patch of actual localized paths

The process is defined on every sample by the limit of its finite-level paths.
Its joint measurability and adaptedness follow from those of the approximants.
Almost-sure compatibility identifies that limit before any finite-level exit.
An explicit exhaustion hypothesis then gives agreement on every finite horizon
and cadlag paths. The Lyapunov estimate supplies exhaustion in the next layer.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace CarryingCapacity.GlobalLocalizedProcess
open CommonInitialNoise LyapunovLocalization

variable {A E J : Type*} [DecidableEq E] [Fintype J]
  [TopologicalSpace E] [PolishSpace E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → E → ℝ) (initial : A → E) (e : E)

/-- A total measurable candidate, identified with the unique patch on good paths. -/
def process (p : Sample A J) (t : ℝ) : E :=
  letI : Nonempty E := ⟨e⟩
  limUnder atTop (fun n : ℕ => path V hfinite jump rate initial n p t)

section Measurability
variable [MeasurableSpace A] [Countable E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [BorelSpace E] (hinit : Measurable initial)
include hinit

theorem measurable_process : Measurable
    (fun p : Sample A J × ℝ => process V hfinite jump rate initial e p.1 p.2) := by
  letI : Nonempty E := ⟨e⟩
  exact (StronglyMeasurable.limUnder (l := atTop)
    (fun n => (measurable_path V hfinite jump rate initial hinit n).stronglyMeasurable)).measurable

theorem measurable_process_at (t : ℝ) :
    Measurable[filtration A J t] (fun p => process V hfinite jump rate initial e p t) := by
  letI : MeasurableSpace (Sample A J) := filtration A J t
  letI : Nonempty E := ⟨e⟩
  exact (StronglyMeasurable.limUnder (l := atTop)
    (fun n => (measurable_path_at V hfinite jump rate initial hinit n t).stronglyMeasurable)).measurable

/-- Strong adaptedness in the actual initial-plus-noise history. -/
theorem adapted_process : Adapted (filtration A J)
    (fun t p => process V hfinite jump rate initial e p t) :=
  fun t => (measurable_process_at V hfinite jump rate initial e hinit t).stronglyMeasurable

end Measurability

variable [MeasurableSpace A] (μ : Measure A)

/-- Compatibility alone identifies the global limit through a localized exit. -/
theorem ae_eq_path : ∀ᵐ p ∂law μ J, ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
    ENNReal.ofReal t ≤ exit V hfinite jump rate initial n p →
      process V hfinite jump rate initial e p t = path V hfinite jump rate initial n p t := by
  filter_upwards [ae_compatible V hfinite jump rate initial μ] with p hp
  intro n t ht hbefore
  unfold process
  apply Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with m hm
  exact (hp n m hm t ht hbefore).symm

/-- The prescribed initial value holds for the actual patched process. -/
theorem ae_process_zero : ∀ᵐ p ∂law μ J,
    process V hfinite jump rate initial e p 0 = initial p.1 := by
  filter_upwards [ae_eq_path V hfinite jump rate initial e μ,
    CommonInitialNoise.ae_process_zero (active V hfinite 0) jump rate initial μ] with p hp hzero
  exact (hp 0 0 le_rfl (by simp)).trans (hzero (rateBound V hfinite rate 0))

section InitialLaw
variable [MeasurableSpace E]

/-- The global process has exactly the prescribed pushed-forward initial law. -/
theorem process_zero_law [IsProbabilityMeasure μ] (hinit : Measurable initial) :
    (law μ J).map (fun p => process V hfinite jump rate initial e p 0) = μ.map initial := by
  rw [Measure.map_congr (ae_process_zero V hfinite jump rate initial e μ)]
  change (law μ J).map (initial ∘ Prod.fst) = μ.map initial
  rw [← Measure.map_map hinit measurable_fst, map_initial]

end InitialLaw

/-- The exhaustion premise concerns the genuine exits of the constructed paths. -/
theorem ae_agrees_on_horizon
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rate initial n p) :
    ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n, ∀ m, n ≤ m →
      ∀ t : ℝ, 0 ≤ t → t ≤ T →
        process V hfinite jump rate initial e p t = path V hfinite jump rate initial m p t := by
  filter_upwards [ae_eq_path V hfinite jump rate initial e μ,
    ae_exit_mono V hfinite jump rate initial μ, hexhaust] with p hp hmono hex
  intro T
  obtain ⟨n, hn⟩ := hex T
  refine ⟨n, fun m hnm t ht htT => hp m t ht ?_⟩
  calc
    ENNReal.ofReal t ≤ (T : ℝ≥0∞) := by
      simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal htT
    _ ≤ exit V hfinite jump rate initial n p := hn.le
    _ ≤ exit V hfinite jump rate initial m p := hmono hnm

/-- Agreement with a frozen path on a neighborhood transfers its cadlag property. -/
theorem ae_process_cadlag
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rate initial n p) :
    ∀ᵐ p ∂law μ J,
      (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt
        (process V hfinite jump rate initial e p) (Ici t) t) ∧
      (∀ t : ℝ, 0 < t → ∃ y : E, Tendsto
        (process V hfinite jump rate initial e p) (𝓝[<] t) (𝓝 y)) := by
  have hf : ∀ n : ℕ, ∀ᵐ p ∂law μ J,
      (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt
        (path V hfinite jump rate initial n p) (Ici t) t) ∧
      (∀ t : ℝ, 0 < t → ∃ y : E, Tendsto
        (path V hfinite jump rate initial n p) (𝓝[<] t) (𝓝 y)) := by
    intro n
    filter_upwards [CommonInitialNoise.ae_process_cadlag
      (active V hfinite n) jump rate initial μ] with p hp
    exact hp (rateBound V hfinite rate n)
  filter_upwards [ae_agrees_on_horizon V hfinite jump rate initial e μ hexhaust,
    ae_all_iff.mpr hf] with p hp hregular
  constructor
  · intro t ht
    obtain ⟨n, hn⟩ := hp ⟨t + 1, by linarith⟩
    have he : process V hfinite jump rate initial e p t =
        path V hfinite jump rate initial n p t := hn n le_rfl t ht (by simp)
    rw [ContinuousWithinAt, he]
    apply (hregular n).1 t ht |>.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t < t + 1 by linarith))] with s hs hst
    exact (hn n le_rfl s (ht.trans hs) hst.le).symm
  · intro t ht
    obtain ⟨n, hn⟩ := hp ⟨t + 1, by linarith⟩
    obtain ⟨y, hy⟩ := (hregular n).2 t ht
    refine ⟨y, hy.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht)] with s hs hs0
    exact (hn n le_rfl s hs0.le (by exact (le_of_lt hs).trans (by change t ≤ t + 1; linarith))).symm

end CarryingCapacity.GlobalLocalizedProcess
