import CarryingCapacity.ChronologicalEvents
import CarryingCapacity.RejectedProposals

/-!
# Frozen paths driven by one common marked counting measure

The state is computed from the actual atoms in a bounded time-height box,
in their measurable chronological order. All cutoffs use the same sample.
The proofs below concern these defined paths; the full PRM law, compensation,
and stochastic non-explosion estimates remain separate obligations.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical

namespace CarryingCapacity.CommonFrozenProcess
open ChronologicalEvents Freezing

variable {E J : Type*} [DecidableEq E] [Fintype J]

local instance : MeasurableSpace (List (Event J)) := ⊤
local instance : MeasurableSingletonClass (List (Event J)) := ⟨fun _ => trivial⟩

/-- The physical vertical coordinate is compared directly with the rate. -/
def eventDecode (rate : J → E → ℝ) (ω : MarkedNoise.Sample J)
    (x : E) (e : Event J) : Option J :=
  if (MarkedNoise.point e.1 ω e.2).2 ≤ rate e.1 x then some e.1 else none

/-- Run the actual sorted list in a box, retaining the accepted exit jump. -/
def runBox (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)
    (x : E) (p : BoxInput J) : E :=
  Freezing.run active jump (eventDecode rate p.1) x (boxedList p)

/-- All height cutoffs are defined on one fixed marked-noise sample space. -/
def process (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)
    (C : ℝ) (x : E) (ω : MarkedNoise.Sample J) (t : ℝ) : E :=
  runBox active jump rate x (ω, t, C)

section Measurability
variable [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)

omit [Fintype J] in
theorem measurable_step (e : Event J) : Measurable
    (fun p : MarkedNoise.Sample J × E =>
      frozenStep active jump (eventDecode rate p.1) p.2 e) := by
  apply measurable_from_prod_countable
  intro x
  by_cases hx : x ∈ active
  · simp only [frozenStep, hx, ↓reduceIte]
    have hh : Measurable (fun ω : MarkedNoise.Sample J =>
      if (MarkedNoise.point e.1 ω e.2).2 ≤ rate e.1 x then jump e.1 x else x) := measurable_const.ite
      (measurableSet_le (MarkedNoise.measurable_point e.1 e.2).snd measurable_const)
      measurable_const
    convert hh using 1
    funext ω
    by_cases h : (MarkedNoise.point e.1 ω e.2).2 ≤ rate e.1 x <;> simp [eventDecode, h]
  · simpa only [frozenStep, hx, ↓reduceIte] using
      (measurable_const : Measurable (fun _ : MarkedNoise.Sample J => x))

omit [Fintype J] in
theorem measurable_run_fixed (l : List (Event J)) : Measurable
    (fun p : MarkedNoise.Sample J × E => Freezing.run active jump (eventDecode rate p.1) p.2 l) := by
  induction l with
  | nil => exact measurable_snd
  | cons e l ih =>
    exact ih.comp (measurable_fst.prodMk (measurable_step active jump rate e))

/-- Initial state, sample, time horizon, and vertical cutoff may all vary
measurably. No measurability assumption on the resulting process is used. -/
theorem measurable_runBox : Measurable
    (fun p : BoxInput J × E => runBox active jump rate p.2 p.1) := by
  have hrun : Measurable (fun p : (MarkedNoise.Sample J × E) × List (Event J) =>
      Freezing.run active jump (eventDecode rate p.1.1) p.1.2 p.2) := by
    apply measurable_from_prod_countable
    exact measurable_run_fixed active jump rate
  exact hrun.comp
    ((measurable_fst.fst.prodMk measurable_snd).prodMk
      (measurable_boxedList.comp measurable_fst))

theorem measurable_process (C : ℝ) (x : E) : Measurable
    (fun p : MarkedNoise.Sample J × ℝ => process active jump rate C x p.1 p.2) :=
  (measurable_runBox active jump rate).comp
    ((measurable_fst.prodMk (measurable_snd.prodMk measurable_const)).prodMk measurable_const)

end Measurability

variable (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)

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
    (hbound : ∀ x ∈ active, ∀ j, rate j x ≤ C)
    (ω : MarkedNoise.Sample J) (x : E) (events : List (Event J)) :
    Freezing.run active jump (eventDecode rate ω) x
      (events.filter (fun e => decide ((MarkedNoise.point e.1 ω e.2).2 ≤ C))) =
      Freezing.run active jump (eventDecode rate ω) x events := by
  apply RejectedProposals.run_filter
  intro y hy e he
  have hh : C < (MarkedNoise.point e.1 ω e.2).2 := by
    simpa only [decide_eq_false_iff_not, not_le] using he
  simp only [eventDecode, if_neg (not_le.mpr ((hbound y hy e.1).trans_lt hh))]

/-- The process is independent of the chosen dominating vertical bound,
simultaneously for all initial states and times on the actual common noise. -/
theorem ae_process_bound_independent (C₁ C₂ : ℝ)
    (h₁ : ∀ x ∈ active, ∀ j, rate j x ≤ C₁)
    (h₂ : ∀ x ∈ active, ∀ j, rate j x ≤ C₂) :
    ∀ᵐ ω ∂MarkedNoise.law J, ∀ x t,
      process active jump rate C₁ x ω t = process active jump rate C₂ x ω t := by
  filter_upwards [ae_boxedList_height_filter (J := J)] with ω hω
  intro x t
  have h (C : ℝ) (hC : C ≤ max C₁ C₂)
      (hb : ∀ x ∈ active, ∀ j, rate j x ≤ C) :
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

omit [Fintype J] in
/-- Finite chronological recursions with nested active sets agree through the
first exit jump. The condition concerns only strictly shorter prefixes. -/
theorem run_eq_before_exit {M : Type*} (large : Finset E) (hsets : active ⊆ large)
    (decode : E → M → Option J) (x : E) (events : List M)
    (hbefore : ∀ k < events.length,
      Freezing.run active jump decode x (events.take k) ∈ active) :
    Freezing.run large jump decode x events = Freezing.run active jump decode x events := by
  induction events generalizing x with
  | nil => rfl
  | cons e events ih =>
    have hx : x ∈ active := by simpa only [List.take_zero, run] using hbefore 0 (by simp)
    have hs := FrozenCompatibility.step_eq active large jump decode hsets hx e
    simp only [run, hs]
    apply ih
    intro k hk
    simpa only [List.take_succ_cons, run] using hbefore (k + 1) (by simpa using hk)

/-- Filtering a strictly ordered event list at its n-th time gives exactly the
first n+1 events, including the event at that time. -/
theorem filter_at_get_eq_take {I : Type*} (time : I → ℝ) (l : List I)
    (hs : l.Sorted (fun a b => time a < time b)) (n : ℕ) (hn : n < l.length) :
    l.filter (fun e => decide (time e ≤ time l[n])) = l.take (n + 1) := by
  induction l generalizing n with
  | nil => simp at hn
  | cons a l ih =>
    have hp := List.sorted_cons.mp hs
    cases n with
    | zero =>
      simp only [List.getElem_cons_zero, List.take_succ_cons, List.take_zero]
      rw [List.filter_cons_of_pos (by simp)]
      congr 1
      apply List.filter_eq_nil_iff.mpr
      intro b hb
      simpa only [decide_eq_true_eq, not_le] using hp.1 b hb
    | succ n =>
      have hn' : n < l.length := Nat.lt_of_succ_lt_succ hn
      have ha := hp.1 l[n] (List.getElem_mem hn')
      simp only [List.getElem_cons_succ, List.take_succ_cons]
      rw [List.filter_cons_of_pos (by simpa only [decide_eq_true_eq] using ha.le)]
      exact congrArg (List.cons a) (ih hp.2 n hn')

/-- Nested frozen paths constructed from the same actual random measures agree
at every time up to the smaller exit, including an exit jump at that time.
Different valid height bounds are allowed. The hypothesis is membership before
the proposed time, not an assumed coupling or compatibility identity. -/
theorem ae_process_agree_before_exit (large : Finset E) (hsets : active ⊆ large)
    (C₁ C₂ : ℝ) (h₁ : ∀ x ∈ active, ∀ j, rate j x ≤ C₁)
    (h₂ : ∀ x ∈ large, ∀ j, rate j x ≤ C₂) :
    ∀ᵐ ω ∂MarkedNoise.law J, ∀ x t,
      (∀ s, 0 ≤ s → s < t → process active jump rate C₁ x ω s ∈ active) →
      process large jump rate C₂ x ω t = process active jump rate C₁ x ω t := by
  have hb₂ : ∀ x ∈ active, ∀ j, rate j x ≤ C₂ := fun x hx => h₂ x (hsets hx)
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
  apply run_eq_before_exit active jump large hsets
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
      exact filter_at_get_eq_take (fun a : Event J => (MarkedNoise.point a.1 ω a.2).1) l hs n hn
    have hh := hbefore s (hpos e.1 e.2).1.le hlt
    rw [hbound x s] at hh
    simpa only [process, runBox, heq] using hh

end CarryingCapacity.CommonFrozenProcess
