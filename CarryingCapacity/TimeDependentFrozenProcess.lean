import CarryingCapacity.CommonFrozenRegularity

/-!
# Frozen paths with deterministic time-dependent rates

The rate is evaluated at each actual proposal time. Only measurability in time
at each label and state is required for joint process measurability. Finite
chronological recursions give finite-state confinement; deterministic bounds on
active rates give cutoff independence and nested frozen-path compatibility.
This module does not assume a stochastic equation or any path regularity.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical Topology

namespace CarryingCapacity.TimeDependentFrozenProcess
open ChronologicalEvents Freezing

variable {E J : Type*} [DecidableEq E] [Fintype J]

local instance : MeasurableSpace (List (Event J)) := ⊤
local instance : MeasurableSingletonClass (List (Event J)) := ⟨fun _ => trivial⟩

/-- The physical vertical coordinate is compared directly with the rate. -/
def eventDecode (rate : J → ℝ → E → ℝ) (ω : MarkedNoise.Sample J)
    (x : E) (e : Event J) : Option J :=
  if (MarkedNoise.point e.1 ω e.2).2 ≤ rate e.1 (MarkedNoise.point e.1 ω e.2).1 x then some e.1 else none

/-- Run the actual sorted list in a box, retaining the accepted exit jump. -/
def runBox (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)
    (x : E) (p : BoxInput J) : E :=
  Freezing.run active jump (eventDecode rate p.1) x (boxedList p)

/-- All height cutoffs are defined on one fixed marked-noise sample space. -/
def process (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)
    (C : ℝ) (x : E) (ω : MarkedNoise.Sample J) (t : ℝ) : E :=
  runBox active jump rate x (ω, t, C)

section Measurability
variable [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (hrate : ∀ j x, Measurable (fun t => rate j t x))
include hrate

omit [Fintype J] in
theorem measurable_step (e : Event J) : Measurable
    (fun p : MarkedNoise.Sample J × E =>
      frozenStep active jump (eventDecode rate p.1) p.2 e) := by
  apply measurable_from_prod_countable
  intro x
  by_cases hx : x ∈ active
  · simp only [frozenStep, hx, ↓reduceIte]
    have hh : Measurable (fun ω : MarkedNoise.Sample J =>
      if (MarkedNoise.point e.1 ω e.2).2 ≤ rate e.1 (MarkedNoise.point e.1 ω e.2).1 x then jump e.1 x else x) := measurable_const.ite
      (measurableSet_le (MarkedNoise.measurable_point e.1 e.2).snd
        ((hrate e.1 x).comp (MarkedNoise.measurable_point e.1 e.2).fst))
      measurable_const
    convert hh using 1
    funext ω
    by_cases h : (MarkedNoise.point e.1 ω e.2).2 ≤ rate e.1 (MarkedNoise.point e.1 ω e.2).1 x <;> simp [eventDecode, h]
  · simpa only [frozenStep, hx, ↓reduceIte] using
      (measurable_const : Measurable (fun _ : MarkedNoise.Sample J => x))

omit [Fintype J] in
theorem measurable_run_fixed (l : List (Event J)) : Measurable
    (fun p : MarkedNoise.Sample J × E => Freezing.run active jump (eventDecode rate p.1) p.2 l) := by
  induction l with
  | nil => exact measurable_snd
  | cons e l ih =>
    exact ih.comp (measurable_fst.prodMk (measurable_step active jump rate hrate e))

/-- Initial state, sample, time horizon, and vertical cutoff may all vary
measurably. No measurability assumption on the resulting process is used. -/
theorem measurable_runBox : Measurable
    (fun p : BoxInput J × E => runBox active jump rate p.2 p.1) := by
  have hrun : Measurable (fun p : (MarkedNoise.Sample J × E) × List (Event J) =>
      Freezing.run active jump (eventDecode rate p.1.1) p.1.2 p.2) := by
    apply measurable_from_prod_countable
    exact measurable_run_fixed active jump rate hrate
  exact hrun.comp
    ((measurable_fst.fst.prodMk measurable_snd).prodMk
      (measurable_boxedList.comp measurable_fst))

theorem measurable_process (C : ℝ) (x : E) : Measurable
    (fun p : MarkedNoise.Sample J × ℝ => process active jump rate C x p.1 p.2) :=
  (measurable_runBox active jump rate hrate).comp
    ((measurable_fst.prodMk (measurable_snd.prodMk measurable_const)).prodMk measurable_const)

end Measurability

variable (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)

/-- Each path stays in a deterministic finite one-jump enlargement or at its
initial state; this includes initial states outside the active set. -/
theorem process_mem_or_eq_initial (C : ℝ) (x : E) (ω : MarkedNoise.Sample J) (t : ℝ) :
    process active jump rate C x ω t ∈ oneStepEnlargement active jump ∨
      process active jump rate C x ω t = x :=
  run_mem_or_eq_initial active jump (eventDecode rate ω) x (boxedList (ω, t, C))

omit [Fintype J] in
theorem process_outside (C : ℝ) {x : E} (hx : x ∉ active)
    (ω : MarkedNoise.Sample J) (t : ℝ) : process active jump rate C x ω t = x :=
  run_outside active jump (eventDecode rate ω) hx _

omit [Fintype J] in
/-- Filtering the actual event identifiers above a valid rate bound has no
effect on the frozen state. -/
theorem run_filter_height (C : ℝ)
    (hbound : ∀ x ∈ active, ∀ j t, rate j t x ≤ C)
    (ω : MarkedNoise.Sample J) (x : E) (events : List (Event J)) :
    Freezing.run active jump (eventDecode rate ω) x
      (events.filter (fun e => decide ((MarkedNoise.point e.1 ω e.2).2 ≤ C))) =
      Freezing.run active jump (eventDecode rate ω) x events := by
  apply RejectedProposals.run_filter
  intro y hy e he
  have hh : C < (MarkedNoise.point e.1 ω e.2).2 := by
    simpa only [decide_eq_false_iff_not, not_le] using he
  simp only [eventDecode, if_neg (not_le.mpr ((hbound y hy e.1 (MarkedNoise.point e.1 ω e.2).1).trans_lt hh))]

/-- The process is independent of the chosen dominating vertical bound,
simultaneously for all initial states and times on the actual common noise. -/
theorem ae_process_bound_independent (C₁ C₂ : ℝ)
    (h₁ : ∀ x ∈ active, ∀ j t, rate j t x ≤ C₁)
    (h₂ : ∀ x ∈ active, ∀ j t, rate j t x ≤ C₂) :
    ∀ᵐ ω ∂MarkedNoise.law J, ∀ x t,
      process active jump rate C₁ x ω t = process active jump rate C₂ x ω t := by
  filter_upwards [ae_boxedList_height_filter (J := J)] with ω hω
  intro x t
  have h (C : ℝ) (hC : C ≤ max C₁ C₂)
      (hb : ∀ x ∈ active, ∀ j t, rate j t x ≤ C) :
      process active jump rate C x ω t = process active jump rate (max C₁ C₂) x ω t := by
    unfold process runBox
    rw [← hω t C (max C₁ C₂) hC]
    exact run_filter_height active jump rate C hb ω x _
  exact (h C₁ (le_max_left _ _) h₁).trans (h C₂ (le_max_right _ _) h₂).symm

/-- Once the actual chronological path exits, every later proposal is ignored. -/
theorem ae_process_frozen : ∀ᵐ ω ∂MarkedNoise.law J, ∀ C x s t,
    s ≤ t → process active jump rate C x ω s ∉ active →
      process active jump rate C x ω t = process active jump rate C x ω s := by
  filter_upwards [ae_boxedList_time_prefix (J := J)] with ω hω
  intro C x s t hst hout
  obtain ⟨post, hpost⟩ := hω s t C hst
  unfold process runBox at hout ⊢
  rw [← hpost, run_append]
  exact run_outside active jump (eventDecode rate ω) hout post

/-- Nested frozen paths constructed from the same actual random measures agree
at every time up to the smaller exit, including an exit jump at that time.
Different valid height bounds are allowed. The hypothesis is membership before
the proposed time, not an assumed coupling or compatibility identity. -/
theorem ae_process_agree_before_exit (large : Finset E) (hsets : active ⊆ large)
    (C₁ C₂ : ℝ) (h₁ : ∀ x ∈ active, ∀ j t, rate j t x ≤ C₁)
    (h₂ : ∀ x ∈ large, ∀ j t, rate j t x ≤ C₂) :
    ∀ᵐ ω ∂MarkedNoise.law J, ∀ x t,
      (∀ s, 0 ≤ s → s < t → process active jump rate C₁ x ω s ∈ active) →
      process large jump rate C₂ x ω t = process active jump rate C₁ x ω t := by
  have hb₂ : ∀ x ∈ active, ∀ j t, rate j t x ≤ C₂ := fun x hx => h₂ x (hsets hx)
  filter_upwards [ae_boxedList_mem (J := J), ae_boxedList_strict (J := J),
    ae_boxedList_time_filter (J := J), MarkedNoise.ae_positive_points (J := J),
    ae_process_bound_independent active jump rate C₁ C₂ h₁ hb₂]
    with ω hmem hsort hfilter hpos hbound
  intro x t hbefore
  rw [hbound x t]
  let l := boxedList (ω, t, C₂)
  have hs : l.Sorted (fun a b => (MarkedNoise.point a.1 ω a.2).1 <
      (MarkedNoise.point b.1 ω b.2).1) := hsort t C₂
  have hzero : boxedList (ω, (0 : ℝ), C₂) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro e he
    have ht := ((hmem 0 C₂ e).mp he).1
    exact (not_le_of_gt (hpos e.1 e.2).1) ht
  change Freezing.run large jump (eventDecode rate ω) x l =
    Freezing.run active jump (eventDecode rate ω) x l
  apply CommonFrozenProcess.run_eq_before_exit active jump large hsets
  intro k hk
  cases k with
  | zero =>
    have hlen : 0 < l.length := hk
    have he : l[0] ∈ boxedList (ω, t, C₂) := List.getElem_mem hlen
    have ht := ((hmem t C₂ l[0]).mp he).1
    have htpos : 0 < t := lt_of_lt_of_le (hpos l[0].1 l[0].2).1 ht
    have hh := hbefore 0 le_rfl htpos
    rw [hbound x 0] at hh
    simpa only [process, runBox, hzero, List.take_zero, run] using hh
  | succ n =>
    have hn : n < l.length := by omega
    let e := l[n]
    let s := (MarkedNoise.point e.1 ω e.2).1
    have he : e ∈ boxedList (ω, t, C₂) := List.getElem_mem hn
    have hnext : l[n+1] ∈ boxedList (ω, t, C₂) := List.getElem_mem hk
    have hlt : s < t := by
      have horder := hs.rel_get_of_lt (a := ⟨n, hn⟩) (b := ⟨n+1, hk⟩) (by simp)
      have hlast := ((hmem t C₂ l[n+1]).mp hnext).1
      exact lt_of_lt_of_le horder hlast
    have heq : boxedList (ω, s, C₂) = l.take (n + 1) := by
      rw [← hfilter s t C₂ hlt.le]
      exact CommonFrozenProcess.filter_at_get_eq_take (fun a : Event J => (MarkedNoise.point a.1 ω a.2).1) l hs n hn
    have hh := hbefore s (hpos e.1 e.2).1.le hlt
    rw [hbound x s] at hh
    simpa only [process, runBox, heq] using hh

/-- Actual frozen paths are locally constant from the right, simultaneously
for all initial states, cutoffs, and times. No bound on rates is needed for this
regularity statement at a fixed finite height cutoff. -/
theorem ae_process_right_constant : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C x t, ∃ b, t < b ∧ ∀ u ∈ Ico t b,
      process active jump rate C x ω u = process active jump rate C x ω t := by
  filter_upwards [CommonFrozenRegularity.ae_boxedList_right_constant (J := J)] with ω hω
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
  filter_upwards [CommonFrozenRegularity.ae_boxedList_left_constant (J := J)] with ω hω
  intro C x t
  obtain ⟨b, l, hb, hl⟩ := hω C t
  refine ⟨b, Freezing.run active jump (eventDecode rate ω) x l, hb, ?_⟩
  intro u hu
  simp only [process, runBox, hl u hu]

/-- The actual common-noise process starts at its prescribed initial state. -/
theorem ae_process_zero : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C x, process active jump rate C x ω 0 = x := by
  filter_upwards [CommonFrozenRegularity.ae_boxedList_zero (J := J)] with ω hω
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

end CarryingCapacity.TimeDependentFrozenProcess
