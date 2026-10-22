import CarryingCapacity.CommonFrozenProcess

/-!
# Regularity of the actual common-noise frozen paths

Finite event lists are locally constant under time truncation from the right,
and have a constant left truncation immediately before every time. Applying
these elementary facts to the common marked-noise boxes proves path regularity
for the defined process without assuming regularity of a proposed solution.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical Topology

namespace CarryingCapacity.CommonFrozenRegularity
open ChronologicalEvents CommonFrozenProcess

/-- A finite list acquires no new event on a sufficiently short right interval. -/
theorem filter_time_right_constant {I : Type*} (time : I → ℝ)
    (l : List I) (t : ℝ) : ∃ b, t < b ∧ ∀ u ∈ Ico t b,
      l.filter (fun e => decide (time e ≤ u)) =
        l.filter (fun e => decide (time e ≤ t)) := by
  induction l with
  | nil => exact ⟨t + 1, by linarith, by simp⟩
  | cons e l ih =>
    obtain ⟨b, hb, hl⟩ := ih
    by_cases he : time e ≤ t
    · refine ⟨b, hb, ?_⟩
      intro u hu
      simp only [List.filter_cons, decide_eq_true (he.trans hu.1),
        decide_eq_true he, Bool.true_eq, ↓reduceIte]
      rw [hl u hu]
    · refine ⟨min b (time e), lt_min hb (lt_of_not_ge he), ?_⟩
      intro u hu
      have heu : ¬ time e ≤ u := not_le.mpr (hu.2.trans_le (min_le_right _ _))
      simp only [List.filter_cons, decide_eq_false heu, decide_eq_false he,
        Bool.false_eq_true, ↓reduceIte]
      exact hl u ⟨hu.1, hu.2.trans_le (min_le_left _ _)⟩

/-- Immediately before a time, a finite list contains exactly the events whose
strict time is smaller. Events occurring at the limiting time are excluded. -/
theorem filter_time_left_constant {I : Type*} (time : I → ℝ)
    (l : List I) (t : ℝ) : ∃ b, b < t ∧ ∀ u ∈ Ico b t,
      l.filter (fun e => decide (time e ≤ u)) =
        l.filter (fun e => decide (time e < t)) := by
  induction l with
  | nil => exact ⟨t - 1, by linarith, by simp⟩
  | cons e l ih =>
    obtain ⟨b, hb, hl⟩ := ih
    by_cases he : time e < t
    · refine ⟨max b (time e), max_lt hb he, ?_⟩
      intro u hu
      have heu : time e ≤ u := (le_max_right _ _).trans hu.1
      simp only [List.filter_cons, decide_eq_true heu, decide_eq_true he,
        Bool.true_eq, ↓reduceIte]
      rw [hl u ⟨(le_max_left _ _).trans hu.1, hu.2⟩]
    · refine ⟨b, hb, ?_⟩
      intro u hu
      have heu : ¬ time e ≤ u := not_le.mpr (hu.2.trans_le (le_of_not_gt he))
      simp only [List.filter_cons, decide_eq_false heu, decide_eq_false he,
        Bool.false_eq_true, ↓reduceIte]
      exact hl u hu

variable {J : Type*} [Fintype J]

/-- Simultaneously in the cutoff and time, the actual boxed chronological list
is constant on a nonempty right interval. -/
theorem ae_boxedList_right_constant : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C t : ℝ, ∃ b, t < b ∧ ∀ u ∈ Ico t b,
      boxedList (ω, u, C) = boxedList (ω, t, C) := by
  filter_upwards [ae_boxedList_time_filter (J := J)] with ω hω
  intro C t
  obtain ⟨b, hb, hl⟩ := filter_time_right_constant
    (fun e : Event J => (MarkedNoise.point e.1 ω e.2).1)
    (boxedList (ω, t + 1, C)) t
  refine ⟨min b (t + 1), lt_min hb (by linarith), ?_⟩
  intro u hu
  have hut : u ≤ t + 1 := (hu.2.trans_le (min_le_right _ _)).le
  rw [← hω u (t + 1) C hut, ← hω t (t + 1) C (by linarith)]
  exact hl u ⟨hu.1, hu.2.trans_le (min_le_left _ _)⟩

/-- The actual list has a constant left value immediately before every time. -/
theorem ae_boxedList_left_constant : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C t : ℝ, ∃ b l, b < t ∧ ∀ u ∈ Ico b t,
      boxedList (ω, u, C) = l := by
  filter_upwards [ae_boxedList_time_filter (J := J)] with ω hω
  intro C t
  obtain ⟨b, hb, hl⟩ := filter_time_left_constant
    (fun e : Event J => (MarkedNoise.point e.1 ω e.2).1)
    (boxedList (ω, t + 1, C)) t
  refine ⟨b, (boxedList (ω, t + 1, C)).filter
    (fun e => decide ((MarkedNoise.point e.1 ω e.2).1 < t)), hb, ?_⟩
  intro u hu
  rw [← hω u (t + 1) C (by linarith [hu.2])]
  exact hl u hu

/-- No positive-time proposal has arrived at zero, for any vertical cutoff. -/
theorem ae_boxedList_zero : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C : ℝ, boxedList (ω, 0, C) = [] := by
  filter_upwards [ae_boxedList_mem (J := J), MarkedNoise.ae_positive_points (J := J)]
    with ω hm hp
  intro C
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro e he
  have hz := ((hm 0 C e).mp he).1
  exact (not_le.mpr (hp e.1 e.2).1) hz

variable {E : Type*} [DecidableEq E]
  (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)

/-- Actual frozen paths are locally constant from the right, simultaneously
for all initial states, cutoffs, and times. No bound on rates is needed for this
regularity statement at a fixed finite height cutoff. -/
theorem ae_process_right_constant : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C x t, ∃ b, t < b ∧ ∀ u ∈ Ico t b,
      process active jump rate C x ω u = process active jump rate C x ω t := by
  filter_upwards [ae_boxedList_right_constant (J := J)] with ω hω
  intro C x t
  obtain ⟨b, hb, hl⟩ := hω C t
  refine ⟨b, hb, ?_⟩
  intro u hu
  simp only [process, runBox, hl u hu]

/-- A form convenient for first-exit arguments: each state persists throughout
some interval `[t,t+δ)`. -/
theorem ae_process_right_constant_delta : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C x t, ∃ δ > 0, ∀ u ∈ Ico t (t + δ),
      process active jump rate C x ω u = process active jump rate C x ω t := by
  filter_upwards [ae_process_right_constant active jump rate] with ω hω
  intro C x t
  obtain ⟨b, hb, hl⟩ := hω C x t
  refine ⟨b - t, sub_pos.mpr hb, ?_⟩
  simpa only [add_sub_cancel] using hl

/-- Every time has a constant left interval on the actual common-noise path. -/
theorem ae_process_left_constant : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C x t, ∃ b y, b < t ∧ ∀ u ∈ Ico b t,
      process active jump rate C x ω u = y := by
  filter_upwards [ae_boxedList_left_constant (J := J)] with ω hω
  intro C x t
  obtain ⟨b, l, hb, hl⟩ := hω C t
  refine ⟨b, Freezing.run active jump (eventDecode rate ω) x l, hb, ?_⟩
  intro u hu
  simp only [process, runBox, hl u hu]

/-- The actual common-noise process starts at its prescribed initial state. -/
theorem ae_process_zero : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C x, process active jump rate C x ω 0 = x := by
  filter_upwards [ae_boxedList_zero (J := J)] with ω hω
  intro C x
  simp only [process, runBox, hω C, Freezing.run]

/-- There is a strictly positive initial interval before any state change. -/
theorem ae_process_initial_interval : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C x, ∃ δ > 0, ∀ t ∈ Ico 0 δ, process active jump rate C x ω t = x := by
  filter_upwards [ae_process_zero active jump rate,
    ae_process_right_constant active jump rate] with ω hzero hright
  intro C x
  obtain ⟨b, hb, hl⟩ := hright C x 0
  exact ⟨b, hb, fun t ht => (hl t ht).trans (hzero C x)⟩

/-- The defined paths are right continuous and have left limits on every
nonnegative time interval. The proof uses actual finite proposal lists only. -/
theorem ae_process_cadlag [TopologicalSpace E] : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C x,
      (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (process active jump rate C x ω) (Ici t) t) ∧
      (∀ t : ℝ, 0 < t → ∃ y : E,
        Tendsto (process active jump rate C x ω) (nhdsWithin t (Iio t)) (nhds y)) := by
  filter_upwards [ae_process_right_constant active jump rate,
    ae_process_left_constant active jump rate] with ω hright hleft
  intro C x
  constructor
  · intro t _
    obtain ⟨b, hbt, hb⟩ := hright C x t
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hbt)] with u hu hub
    exact (hb u ⟨hu, hub⟩).symm
  · intro t _
    obtain ⟨b, y, hbt, hb⟩ := hleft C x t
    refine ⟨y, ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hbt)] with u hu hbu
    exact (hb u ⟨le_of_lt hbu, hu⟩).symm

end CarryingCapacity.CommonFrozenRegularity
