import CarryingCapacity.FrozenProcess

/-!
# Compatibility of actual frozen recursions on common proposals

For nested active sets, the recursions driven by the same proposal sequence
agree through the first exit from the smaller set, including the accepted exit
jump. The smaller recursion then remains at that state. This derives the
compatibility property from the recursion instead of assuming it as a field.
With a common locally finite clock, the actual continuous-time paths agree
after stopping the larger one at the smaller exit arrival. This does not yet
couple distinct cutoff event lists or prove that the exit is a stopping time.
-/

noncomputable section
open scoped Classical

namespace CarryingCapacity.FrozenCompatibility
open FrozenProcess
open CountableJumpProcess

variable {E J M : Type*} [DecidableEq E]
  (small large : Finset E) (jump : J → E → E) (decode : E → M → Option J)

/-- Both updates make exactly the same decision while in the smaller active set. -/
theorem step_eq (hsets : small ⊆ large) {x : E} (hx : x ∈ small) (mark : M) :
    Freezing.frozenStep large jump decode x mark =
      Freezing.frozenStep small jump decode x mark := by
  simp [Freezing.frozenStep, hx, hsets hx]

/-- Agreement includes the update that first leaves the smaller active set. -/
theorem stateAfter_eq_before_exit (hsets : small ⊆ large) (x : E) (marks : ℕ → M)
    (n : ℕ) (hbefore : ∀ k < n, stateAfter small jump decode x marks k ∈ small) :
    stateAfter large jump decode x marks n = stateAfter small jump decode x marks n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := hbefore n (Nat.lt_succ_self n)
    have heq := ih (fun k hk => hbefore k (Nat.lt_succ_of_lt hk))
    simp only [stateAfter, heq]
    exact step_eq small large jump decode hsets hn (marks n)

/-- First exit in proposal index, with infinity when the recursion never exits. -/
def exitIndex (x : E) (marks : ℕ → M) : WithTop ℕ :=
  if h : ∃ n, stateAfter small jump decode x marks n ∉ small then (Nat.find h : WithTop ℕ)
  else ⊤

theorem le_exitIndex_iff (x : E) (marks : ℕ → M) (n : ℕ) :
    (n : WithTop ℕ) ≤ exitIndex small jump decode x marks ↔
      ∀ k < n, stateAfter small jump decode x marks k ∈ small := by
  unfold exitIndex
  split_ifs with h
  · norm_cast
    constructor
    · intro hn k hk
      exact not_not.mp (Nat.find_min h (hk.trans_le hn))
    · intro hn
      by_contra hnot
      exact Nat.find_spec h (hn (Nat.find h) (Nat.lt_of_not_ge hnot))
  · simp only [le_top, true_iff]
    have ha : ∀ k, stateAfter small jump decode x marks k ∈ small := by
      simpa only [not_exists, not_not] using h
    exact fun k _ => ha k

/-- Actual recursions are compatible up to and including their smaller exit index. -/
theorem stateAfter_eq_of_le_exitIndex (hsets : small ⊆ large) (x : E) (marks : ℕ → M)
    (n : ℕ) (hn : (n : WithTop ℕ) ≤ exitIndex small jump decode x marks) :
    stateAfter large jump decode x marks n = stateAfter small jump decode x marks n :=
  stateAfter_eq_before_exit small large jump decode hsets x marks n
    ((le_exitIndex_iff small jump decode x marks n).mp hn)

/-- Exits of the actual nested frozen recursions are nondecreasing. -/
theorem exitIndex_mono (hsets : small ⊆ large) (x : E) (marks : ℕ → M) :
    exitIndex small jump decode x marks ≤ exitIndex large jump decode x marks := by
  by_contra hnot
  have hlt := lt_of_not_ge hnot
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  have hsmall : (n : WithTop ℕ) < exitIndex small jump decode x marks := by rwa [← hn] at hlt
  have hbefore := (le_exitIndex_iff small jump decode x marks (n + 1)).mp
    (by
      cases he : exitIndex small jump decode x marks with
      | top => simp [he]
      | coe m =>
        have hh : n < m := by simpa [he] using hsmall
        exact WithTop.coe_le_coe.mpr (Nat.succ_le_of_lt hh))
  have hx := hbefore n (Nat.lt_succ_self n)
  have heq := stateAfter_eq_before_exit small large jump decode hsets x marks n
    (fun k hk => hbefore k (Nat.lt_succ_of_lt hk))
  have hout : stateAfter large jump decode x marks n ∉ large := by
    unfold exitIndex at hn
    split_ifs at hn with hex
    · have hn' : Nat.find hex = n := WithTop.coe_injective hn.symm
      simpa [hn'] using Nat.find_spec hex
    · exact False.elim (WithTop.top_ne_coe hn.symm)
  apply hout
  rw [heq]
  exact hsets hx

/-- When the smaller exit is finite, its value is retained at every later proposal. -/
theorem stateAfter_stopped (hsets : small ⊆ large) (x : E) (marks : ℕ → M)
    (r : ℕ) (hr : exitIndex small jump decode x marks = (r : WithTop ℕ)) (n : ℕ) :
    stateAfter large jump decode x marks (min n r) = stateAfter small jump decode x marks n := by
  have hout : stateAfter small jump decode x marks r ∉ small := by
    unfold exitIndex at hr
    split_ifs at hr with hex
    · have hr' : Nat.find hex = r := WithTop.coe_injective hr
      simpa [hr'] using Nat.find_spec hex
    · exact False.elim (WithTop.top_ne_coe hr)
  by_cases hn : n ≤ r
  · rw [min_eq_left hn]
    apply stateAfter_eq_of_le_exitIndex small large jump decode hsets x marks n
    simpa [hr] using hn
  · rw [min_eq_right (Nat.le_of_not_ge hn),
      stateAfter_frozen small jump decode x marks (Nat.le_of_not_ge hn) hout]
    apply stateAfter_eq_of_le_exitIndex small large jump decode hsets x marks r
    rw [hr]

/-- On one common locally finite clock, stopping the larger path at the smaller
exit arrival gives the smaller frozen path. The exit index comes from the actual
recursion; this does not assume path compatibility or a stopping-time property. -/
theorem process_stopped_at_exitArrival (hsets : small ⊆ large)
    (x : E) (ω : ClockSpace × (ℕ → M))
    (hmono : StrictMono (arrival ω.1))
    (hfin : ∀ T : ℝ, {n : ℕ | arrival ω.1 n ≤ T}.Finite)
    (r : ℕ) (hr : exitIndex small jump decode x ω.2 = (r : WithTop ℕ))
    (t : ℝ) :
    process large jump decode x ω (min t (arrival ω.1 r)) =
      process small jump decode x ω t := by
  have hc : proposalCount ω.1 (arrival ω.1 r) = r :=
    proposalCount_between hmono le_rfl (hmono (Nat.lt_succ_self r))
  have hm : proposalCount ω.1 (min t (arrival ω.1 r)) =
      min (proposalCount ω.1 t) r := by
    rw [(proposalCount_mono hfin).map_min, hc]
  unfold process
  rw [hm]
  exact stateAfter_stopped small large jump decode hsets x ω.2 r hr _

end CarryingCapacity.FrozenCompatibility
