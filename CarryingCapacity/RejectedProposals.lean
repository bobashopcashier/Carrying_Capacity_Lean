import CarryingCapacity.FrozenCompatibility

/-!
# Removing proposals rejected everywhere in the active set

The common marked-noise construction supplies ordered lists
with different vertical bounds. Filtering out marks above a valid rate bound
does not change the actual frozen recursion, even after its exit jump.
-/

noncomputable section
open scoped Classical

namespace CarryingCapacity.RejectedProposals
open Freezing

variable {E J M : Type*} [DecidableEq E]
  (active : Finset E) (jump : J → E → E) (decode : E → M → Option J)

theorem frozenStep_rejected (keep : M → Bool)
    (hreject : ∀ x ∈ active, ∀ m, keep m = false → decode x m = none)
    (x : E) (m : M) (hm : keep m = false) :
    frozenStep active jump decode x m = x := by
  by_cases hx : x ∈ active
  · simp [frozenStep, hx, hreject x hx m hm]
  · exact frozenStep_outside active jump decode hx m

/-- Every deleted proposal is rejected while active and is ignored after exit.
Consequently deletion preserves the full final state, including any overshoot. -/
theorem run_filter (keep : M → Bool)
    (hreject : ∀ x ∈ active, ∀ m, keep m = false → decode x m = none)
    (x : E) (marks : List M) :
    run active jump decode x (marks.filter keep) = run active jump decode x marks := by
  induction marks generalizing x with
  | nil => rfl
  | cons m marks ih =>
    cases hm : keep m with
    | false =>
      simp only [List.filter_cons, hm, Bool.false_eq_true, ↓reduceIte, run]
      rw [frozenStep_rejected active jump decode keep hreject x m hm]
      exact ih x
    | true =>
      simp only [List.filter_cons, hm, ↓reduceIte, run]
      exact ih _

/-- Decode a physical vertical mark directly, without normalizing by a cutoff. -/
def heightDecode (rate : J → E → ℝ) (x : E) (p : J × ℝ) : Option J :=
  if p.2 ≤ rate p.1 x then some p.1 else none

/-- The physical thinning rule ignores all marks above any valid rate bound. -/
theorem run_filter_height (rate : J → E → ℝ) (C : ℝ)
    (hbound : ∀ x ∈ active, ∀ j, rate j x ≤ C)
    (x : E) (marks : List (J × ℝ)) :
    run active jump (heightDecode rate) x (marks.filter (fun p => decide (p.2 ≤ C))) =
      run active jump (heightDecode rate) x marks := by
  apply run_filter active jump (heightDecode rate)
  intro y hy p hp
  have hheight : C < p.2 := by simpa only [decide_eq_false_iff_not, not_le] using hp
  simp only [heightDecode, if_neg (not_le.mpr ((hbound y hy p.1).trans_lt hheight))]

/-- Two different upper bounds produce the same frozen path at every prefix of
the common chronological list. It is enough that each bound dominates active rates. -/
theorem run_height_bounds (rate : J → E → ℝ) (C₁ C₂ : ℝ)
    (h₁ : ∀ x ∈ active, ∀ j, rate j x ≤ C₁)
    (h₂ : ∀ x ∈ active, ∀ j, rate j x ≤ C₂)
    (x : E) (marks : List (J × ℝ)) :
    run active jump (heightDecode rate) x (marks.filter (fun p => decide (p.2 ≤ C₁))) =
      run active jump (heightDecode rate) x (marks.filter (fun p => decide (p.2 ≤ C₂))) := by
  rw [run_filter_height active jump rate C₁ h₁, run_filter_height active jump rate C₂ h₂]

end CarryingCapacity.RejectedProposals
