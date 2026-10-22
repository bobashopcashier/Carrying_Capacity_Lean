import Mathlib

/-!
# Causal uniqueness for discrete right-continuous paths

Right continuity in a discrete state space makes a path locally constant to
the right. The infimum of a nonempty disagreement set therefore cannot be a
point where agreement on the strict past forces agreement at the point.
This gives a deterministic uniqueness principle without a finite-activity or
bounded-rate hypothesis.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace CarryingCapacity.DiscreteCausalUniqueness

variable {E : Type*} [TopologicalSpace E] [DiscreteTopology E]

/-- A discrete right-continuous path is constant on a nonempty right interval. -/
theorem exists_right_constant (X : ℝ → E) (t : ℝ)
    (hX : ContinuousWithinAt X (Ici t) t) :
    ∃ b : ℝ, t < b ∧ ∀ s ∈ Ico t b, X s = X t := by
  have h : {s | X s = X t} ∈ 𝓝[≥] t :=
    hX ((isOpen_discrete ({X t} : Set E)).mem_nhds (by simp))
  exact mem_nhdsGE_iff_exists_Ico_subset.mp h

/-- The strict-past extension principle determines a pair of discrete
right-continuous paths on all nonnegative times. -/
theorem eq_of_strictPast (X Y : ℝ → E)
    (hX : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt X (Ici t) t)
    (hY : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt Y (Ici t) t)
    (hcausal : ∀ t : ℝ, 0 ≤ t →
      (∀ s : ℝ, 0 ≤ s → s < t → X s = Y s) → X t = Y t) :
    ∀ t : ℝ, 0 ≤ t → X t = Y t := by
  intro t ht
  by_contra hne
  let D : Set ℝ := {s | 0 ≤ s ∧ X s ≠ Y s}
  have hD : D.Nonempty := ⟨t, ht, hne⟩
  have hbelow : BddBelow D := ⟨0, fun s hs => hs.1⟩
  let a : ℝ := sInf D
  have ha : 0 ≤ a := le_csInf hD (fun s hs => hs.1)
  have hprior : ∀ s : ℝ, 0 ≤ s → s < a → X s = Y s := by
    intro s hs hsa
    by_contra hneq
    exact (not_le_of_gt hsa) (csInf_le hbelow ⟨hs, hneq⟩)
  have hea : X a = Y a := hcausal a ha hprior
  obtain ⟨b, hab, hb⟩ := exists_right_constant X a (hX a ha)
  obtain ⟨c, hac, hc⟩ := exists_right_constant Y a (hY a ha)
  have hbound : min b c ≤ a := by
    apply le_csInf hD
    intro s hs
    by_contra hlt
    have has : a ≤ s := csInf_le hbelow hs
    have hsmin : s < min b c := lt_of_not_ge hlt
    exact hs.2 ((hb s ⟨has, hsmin.trans_le (min_le_left _ _)⟩).trans
      (hea.trans (hc s ⟨has, hsmin.trans_le (min_le_right _ _)⟩).symm))
  exact (not_le_of_gt (lt_min hab hac)) hbound

end CarryingCapacity.DiscreteCausalUniqueness
