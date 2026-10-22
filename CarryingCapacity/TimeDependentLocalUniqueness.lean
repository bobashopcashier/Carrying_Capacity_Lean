import CarryingCapacity.TimeDependentEquationUniqueness

/-!
# Counting-equation uniqueness on a finite interval

Only equations and agreement of the rates on the comparison interval are
needed. The paths may use different continuations afterwards. The first
disagreement argument includes the right endpoint of the interval.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical Topology BigOperators

namespace CarryingCapacity.TimeDependentLocalUniqueness
open CountingEquationUniqueness TimeDependentEquationUniqueness

variable {E J : Type*} [TopologicalSpace E] [DiscreteTopology E]

/-- The strict-past extension principle also determines a finite closed prefix. -/
theorem eqOn_of_strictPast (X Y : ℝ → E) (T : ℝ)
    (hX : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt X (Ici t) t)
    (hY : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt Y (Ici t) t)
    (hcausal : ∀ t ∈ Icc 0 T,
      (∀ s : ℝ, 0 ≤ s → s < t → X s = Y s) → X t = Y t) :
    EqOn X Y (Icc 0 T) := by
  intro t ht
  by_contra hne
  let B : Set ℝ := {s | s ∈ Icc 0 T ∧ X s ≠ Y s}
  have hB : B.Nonempty := ⟨t, ht, hne⟩
  have hbelow : BddBelow B := ⟨0, fun s hs => hs.1.1⟩
  let a : ℝ := sInf B
  have ha : 0 ≤ a := le_csInf hB (fun s hs => hs.1.1)
  have haT : a ≤ T := (csInf_le hbelow ⟨ht, hne⟩).trans ht.2
  have hprior : ∀ s : ℝ, 0 ≤ s → s < a → X s = Y s := by
    intro s hs hsa
    by_contra hneq
    exact (not_le_of_gt hsa) (csInf_le hbelow ⟨⟨hs, hsa.le.trans haT⟩, hneq⟩)
  have hea : X a = Y a := hcausal a ⟨ha, haT⟩ hprior
  obtain ⟨b, hab, hb⟩ := DiscreteCausalUniqueness.exists_right_constant X a (hX a ha)
  obtain ⟨c, hac, hc⟩ := DiscreteCausalUniqueness.exists_right_constant Y a (hY a ha)
  have hbound : min b c ≤ a := by
    apply le_csInf hB
    intro s hs
    by_contra hlt
    have has : a ≤ s := csInf_le hbelow hs
    have hsmin : s < min b c := lt_of_not_ge hlt
    exact hs.2 ((hb s ⟨has, hsmin.trans_le (min_le_left _ _)⟩).trans
      (hea.trans (hc s ⟨has, hsmin.trans_le (min_le_right _ _)⟩).symm))
  exact (not_le_of_gt (lt_min hab hac)) hbound

variable [Fintype J]

/-- Two actual equations with rates equal on the interval have identical
paths there. No restriction is imposed on either continuation after `T`. -/
theorem eqOn_of_separating_counting_equations {I : Type*} (test : I → E → ℝ)
    (hseparate : ∀ x y : E, (∀ i, test i x = test i y) → x = y)
    (jump : J → E → E) (rate₁ rate₂ : J → ℝ → E → ℝ)
    (N : J → Measure (ℝ × ℝ)) (X Y xpre ypre : ℝ → E) (T : ℝ)
    (hrate : ∀ j t x, t ∈ Icc 0 T → rate₁ j t x = rate₂ j t x)
    (hX : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt X (Ici t) t)
    (hY : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt Y (Ici t) t)
    (hx : ∀ t : ℝ, 0 < t → Tendsto X (𝓝[<] t) (𝓝 (xpre t)))
    (hy : ∀ t : ℝ, 0 < t → Tendsto Y (𝓝[<] t) (𝓝 (ypre t)))
    (hzero : X 0 = Y 0)
    (heqX : ∀ i t, t ∈ Icc 0 T → test i (X t) - test i (X 0) =
      ∑ j : J, ∫ z, TimeDependentEquationUniqueness.increment jump rate₁ xpre (test i) j t z ∂N j)
    (heqY : ∀ i t, t ∈ Icc 0 T → test i (Y t) - test i (Y 0) =
      ∑ j : J, ∫ z, TimeDependentEquationUniqueness.increment jump rate₂ ypre (test i) j t z ∂N j) :
    EqOn X Y (Icc 0 T) := by
  apply eqOn_of_strictPast X Y T hX hY
  intro t ht hprior
  have hpre : ∀ r ∈ Ioc (0 : ℝ) t, xpre r = ypre r :=
    leftLimit_eq_of_strictPast X Y xpre ypre hx hy t hprior
  apply hseparate
  intro i
  have hi (j : J) : TimeDependentEquationUniqueness.increment jump rate₁ xpre (test i) j t =
      TimeDependentEquationUniqueness.increment jump rate₂ ypre (test i) j t := by
    funext z
    by_cases hz : z.1 ∈ Ioc 0 t
    · simp only [TimeDependentEquationUniqueness.increment, hz, true_and, hpre z.1 hz,
        hrate j z.1 (ypre z.1) ⟨hz.1.le, hz.2.trans ht.2⟩]
    · simp only [TimeDependentEquationUniqueness.increment, hz, false_and, ↓reduceIte]
  have hi' : test i (X t) - test i (X 0) = test i (Y t) - test i (Y 0) := by
    rw [heqX i t ht, heqY i t ht]
    apply Finset.sum_congr rfl
    intro j _
    rw [hi j]
  rw [hzero] at hi'
  linarith

end CarryingCapacity.TimeDependentLocalUniqueness
