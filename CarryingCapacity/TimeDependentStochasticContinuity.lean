import CarryingCapacity.TimeDependentGlobalProcess
import CarryingCapacity.TimeDependentPreStateTime

/-!
# Continuity at each deterministic time for the actual process

Every indexed arrival has a nonatomic law. A countable intersection therefore
excludes proposals at a fixed deterministic time. The actual frozen paths are
locally constant near such a time, using their chronological left and right
lists. Agreement on a bounded horizon transfers this continuity to the global
patch under genuine exit exhaustion. The null event may depend on the fixed
time; the statement does not assert continuous sample paths.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical Topology ENNReal NNReal

namespace CarryingCapacity.TimeDependentStochasticContinuity
open MarkedNoise ChronologicalEvents
open FrozenPreStateTime (proposalTimes)

variable {J : Type*}

/-- Every actual indexed marked point avoids a fixed deterministic time on one event. -/
theorem ae_points_ne_time [Countable J] (t : ℝ) : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ (j : J) (p : ℕ × ℕ), (point j ω p).1 ≠ t := by
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro p
  have hm : Measurable (fun ω : MarkedNoise.Sample J => (point j ω p).1) :=
    (measurable_point j p).fst
  letI : NoAtoms (Measure.map (fun ω : MarkedNoise.Sample J => (point j ω p).1)
      (MarkedNoise.law J)) := by
    change NoAtoms (Measure.map (fun ω : MarkedNoise.Sample J =>
      CountableJumpProcess.arrival (ω (j, p.1)).1 (p.2 + 1)) (MarkedNoise.law J))
    rw [MarkedNoise.arrival_map]
    exact PoissonIncrements.arrival_noAtoms 1 (by norm_num) p.2
  have hnull : (Measure.map (fun ω : MarkedNoise.Sample J => (point j ω p).1)
      (MarkedNoise.law J)) {t} = 0 := measure_singleton t
  rw [Measure.map_apply hm (measurableSet_singleton t)] at hnull
  exact ae_iff.mpr (by simpa only [not_not, mem_preimage, mem_singleton_iff] using hnull)

/-- Fixed-time nullity has sample-law quantifiers, unlike time-almost-everywhere nullity. -/
theorem ae_not_proposalTimes [Fintype J] (t : ℝ) :
    ∀ᵐ ω ∂MarkedNoise.law J, t ∉ proposalTimes ω := by
  filter_upwards [ae_points_ne_time (J := J) t] with ω hω
  rintro ⟨e, he⟩
  exact hω e.1 e.2 he

section Frozen
variable {E : Type*} [DecidableEq E] [Fintype J]
  (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)

/-- At a fixed time the actual frozen path is constant on a genuine two-sided
neighborhood, simultaneously in its cutoff and initial state. -/
theorem ae_frozen_locally_constant (t : ℝ) : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C x, ∃ a b : ℝ, a < t ∧ t < b ∧ ∀ u ∈ Ioo a b,
      TimeDependentFrozenProcess.process active jump rate C x ω u =
        TimeDependentFrozenProcess.process active jump rate C x ω t := by
  filter_upwards [ae_not_proposalTimes (J := J) t,
    TimeDependentPreStateTime.ae_process_eq_leftProcess_off_proposalTimes active jump rate,
    TimeDependentJumpIdentity.ae_process_eq_leftProcess_on_left active jump rate,
    TimeDependentFrozenProcess.ae_process_right_constant active jump rate]
    with ω hnot he hleft hright
  intro C x
  obtain ⟨a, ha, hl⟩ := hleft C x t
  obtain ⟨b, hb, hr⟩ := hright C x t
  refine ⟨a, b, ha, hb, ?_⟩
  intro u hu
  by_cases hut : u < t
  · exact (hl u ⟨hu.1.le, hut⟩).trans (he C x t hnot).symm
  · exact hr u ⟨le_of_not_gt hut, hu.2⟩

variable [TopologicalSpace E]

/-- The fixed-time continuity is derived from the actual event list, without
any continuity or measurability condition on the time-dependent rates. -/
theorem ae_frozen_continuousAt (t : ℝ) : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C x, ContinuousAt (TimeDependentFrozenProcess.process active jump rate C x ω) t := by
  filter_upwards [ae_frozen_locally_constant active jump rate t] with ω hω
  intro C x
  obtain ⟨a, b, ha, hb, hconst⟩ := hω C x
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhds ha hb] with u hu
  exact (hconst u hu).symm

/-- The same fixed-time event works for an arbitrary sampled initial state. -/
theorem ae_initial_continuousAt {A : Type*} [MeasurableSpace A]
    (initial : A → E) (μ : Measure A) (t : ℝ) : ∀ᵐ p ∂CommonInitialNoise.law μ J,
    ∀ C, ContinuousAt (TimeDependentInitial.process active jump rate initial C p) t := by
  filter_upwards [CommonInitialNoise.ae_noise μ (ae_frozen_continuousAt active jump rate t)]
    with p hp
  exact fun C => hp C (initial p.1)

end Frozen

section Global
open CommonInitialNoise TimeDependentLocalization
open LyapunovLocalization (active)
variable {A E : Type*} [MeasurableSpace A] [DecidableEq E] [Fintype J]
  [TopologicalSpace E] [PolishSpace E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (hbounded : ∀ n : ℕ, ∃ C : ℝ,
    ∀ x ∈ active V hfinite n, ∀ j t, rate j t x ≤ C)
  (initial : A → E) (e : E) (μ : Measure A)
  (hexhaust : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
    (T : ℝ≥0∞) < exit V hfinite jump rate hbounded initial n p)
include hexhaust

/-- At each deterministic nonnegative time, the actual global path is almost
surely continuous relative to nonnegative time. Genuine exit exhaustion is the
only stochastic input beyond the constructed common noise. -/
theorem ae_continuousWithinAt (t : ℝ) (ht : 0 ≤ t) : ∀ᵐ p ∂law μ J,
    ContinuousWithinAt
      (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p) (Ici 0) t := by
  have hf : ∀ n : ℕ, ∀ᵐ p ∂law μ J,
      ContinuousAt (path V hfinite jump rate hbounded initial n p) t := by
    intro n
    filter_upwards [ae_initial_continuousAt (active V hfinite n) jump rate initial μ t]
      with p hp
    exact hp (rateBound V hfinite rate hbounded n)
  filter_upwards [TimeDependentGlobalProcess.ae_agrees_on_horizon
      V hfinite jump rate hbounded initial e μ hexhaust, ae_all_iff.mpr hf]
    with p hp hregular
  obtain ⟨n, hn⟩ := hp ⟨t + 1, by linarith⟩
  have he : TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p t =
      path V hfinite jump rate hbounded initial n p t := hn n le_rfl t ht (by simp)
  rw [ContinuousWithinAt, he]
  apply (hregular n).continuousWithinAt.congr'
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t < t + 1 by linarith))] with s hs hst
  exact (hn n le_rfl s hs hst.le).symm

/-- A direct interface for marginal laws indexed by nonnegative time. -/
theorem ae_continuousAt_nonnegative (t : ℝ≥0) : ∀ᵐ p ∂law μ J,
    ContinuousAt (fun s : ℝ≥0 =>
      TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p s) t := by
  filter_upwards [ae_continuousWithinAt V hfinite jump rate hbounded initial e μ hexhaust t t.2]
    with p hp
  exact (continuousWithinAt_iff_continuousAt_restrict _ t.2).mp hp

/-- Along any deterministic convergent sequence of nonnegative times, the
actual global states converge almost surely to the state at its limit. -/
theorem ae_tendsto_times (t : ℝ≥0) (u : ℕ → ℝ≥0) (hu : Tendsto u atTop (𝓝 t)) :
    ∀ᵐ p ∂law μ J, Tendsto
      (fun n => TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p (u n))
      atTop (𝓝 (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p t)) := by
  filter_upwards [ae_continuousAt_nonnegative V hfinite jump rate hbounded initial e μ hexhaust t]
    with p hp
  exact hp.tendsto.comp hu

/-- At a positive deterministic time this is ordinary two-sided continuity. -/
theorem ae_continuousAt (t : ℝ) (ht : 0 < t) : ∀ᵐ p ∂law μ J,
    ContinuousAt
      (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p) t := by
  filter_upwards [ae_continuousWithinAt V hfinite jump rate hbounded initial e μ hexhaust t ht.le]
    with p hp
  exact hp.continuousAt (Ici_mem_nhds ht)

end Global
end CarryingCapacity.TimeDependentStochasticContinuity
