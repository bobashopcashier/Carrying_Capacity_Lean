import CarryingCapacity.TimeDependentEquationUniqueness

/-!
# Causal uniqueness using only equations through a finite horizon

A comparison at time `T` requires the equations and path regularity only on
`[0,T]`. This local form is useful when a sample-dependent finite rate bound
is known only up to a stopping time. No artificial continuation or candidate
activity bound is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical Topology BigOperators

namespace CarryingCapacity.FiniteHorizonCountingUniqueness
open DiscreteCausalUniqueness TimeDependentEquationUniqueness CountingEquationUniqueness

variable {E J : Type*} [TopologicalSpace E] [DiscreteTopology E]

/-- The strict-past extension argument localized to an actual finite interval. -/
theorem eqOn_of_strictPast (X Y : ℝ → E) (T : ℝ)
    (hX : ∀ t ∈ Ico 0 T, ContinuousWithinAt X (Ici t) t)
    (hY : ∀ t ∈ Ico 0 T, ContinuousWithinAt Y (Ici t) t)
    (hcausal : ∀ t ∈ Icc 0 T,
      (∀ s : ℝ, 0 ≤ s → s < t → X s = Y s) → X t = Y t) :
    EqOn X Y (Icc 0 T) := by
  intro t ht
  by_contra hne
  let D : Set ℝ := {s | s ∈ Icc 0 T ∧ X s ≠ Y s}
  have hD : D.Nonempty := ⟨t, ht, hne⟩
  have hbelow : BddBelow D := ⟨0, fun s hs => hs.1.1⟩
  let a : ℝ := sInf D
  have ha : 0 ≤ a := le_csInf hD (fun s hs => hs.1.1)
  have haT : a ≤ T := (csInf_le hbelow ⟨ht,hne⟩).trans ht.2
  have hprior : ∀ s : ℝ, 0 ≤ s → s < a → X s = Y s := by
    intro s hs hsa
    by_contra hneq
    exact (not_le_of_gt hsa) (csInf_le hbelow ⟨⟨hs,hsa.le.trans haT⟩,hneq⟩)
  have hea : X a = Y a := hcausal a ⟨ha,haT⟩ hprior
  have haTlt : a < T := by
    by_contra hn
    have hat : a = t := le_antisymm (csInf_le hbelow ⟨ht,hne⟩)
      (ht.2.trans (le_of_not_gt hn))
    exact hne (hat ▸ hea)
  obtain ⟨b, hab, hb⟩ := exists_right_constant X a (hX a ⟨ha,haTlt⟩)
  obtain ⟨c, hac, hc⟩ := exists_right_constant Y a (hY a ⟨ha,haTlt⟩)
  have hbound : min b c ≤ a := by
    apply le_csInf hD
    intro s hs
    by_contra hlt
    have has : a ≤ s := csInf_le hbelow hs
    have hsmin : s < min b c := lt_of_not_ge hlt
    exact hs.2 ((hb s ⟨has, hsmin.trans_le (min_le_left _ _)⟩).trans
      (hea.trans (hc s ⟨has, hsmin.trans_le (min_le_right _ _)⟩).symm))
  exact (not_le_of_gt (lt_min hab hac)) hbound

variable [Fintype J]

/-- Actual separating coordinate equations determine the paths on `[0,T]`.
Integrals are compared pointwise; no desired paired equation is assumed. -/
theorem eqOn_of_separating_counting_equations {I : Type*} (test : I → E → ℝ)
    (hseparate : ∀ x y : E, (∀ i, test i x = test i y) → x = y)
    (jump : J → E → E) (rate : J → ℝ → E → ℝ)
    (N : J → Measure (ℝ × ℝ)) (X Y xpre ypre : ℝ → E) (T : ℝ)
    (hX : ∀ t ∈ Ico 0 T, ContinuousWithinAt X (Ici t) t)
    (hY : ∀ t ∈ Ico 0 T, ContinuousWithinAt Y (Ici t) t)
    (hx : ∀ t ∈ Ioc 0 T, Tendsto X (𝓝[<] t) (𝓝 (xpre t)))
    (hy : ∀ t ∈ Ioc 0 T, Tendsto Y (𝓝[<] t) (𝓝 (ypre t)))
    (hzero : X 0 = Y 0)
    (heqX : ∀ (i : I) (t : ℝ), t ∈ Icc 0 T →
      test i (X t) - test i (X 0) = ∑ j : J, ∫ z,
        TimeDependentEquationUniqueness.increment jump rate xpre (test i) j t z ∂N j)
    (heqY : ∀ (i : I) (t : ℝ), t ∈ Icc 0 T →
      test i (Y t) - test i (Y 0) = ∑ j : J, ∫ z,
        TimeDependentEquationUniqueness.increment jump rate ypre (test i) j t z ∂N j) :
    EqOn X Y (Icc 0 T) := by
  apply eqOn_of_strictPast X Y T hX hY
  intro t ht hprior
  have hpre : ∀ s ∈ Ioc (0 : ℝ) t, xpre s = ypre s := by
    intro s hs
    apply tendsto_nhds_unique (hx s ⟨hs.1,hs.2.trans ht.2⟩)
    apply (hy s ⟨hs.1,hs.2.trans ht.2⟩).congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hs.1)] with u hus hu0
    exact (hprior u hu0.le (hus.trans_le hs.2)).symm
  apply hseparate
  intro i
  have hi (j : J) : TimeDependentEquationUniqueness.increment jump rate xpre (test i) j t =
      TimeDependentEquationUniqueness.increment jump rate ypre (test i) j t := by
    funext z
    by_cases hz : z.1 ∈ Ioc 0 t
    · simp only [TimeDependentEquationUniqueness.increment, hz, true_and, hpre z.1 hz]
    · simp only [TimeDependentEquationUniqueness.increment, hz, false_and, ↓reduceIte]
  have he : test i (X t) - test i (X 0) = test i (Y t) - test i (Y 0) := by
    rw [heqX i t ht, heqY i t ht]
    exact Finset.sum_congr rfl (fun j _ => by rw [hi j])
  rw [hzero] at he
  linarith

end CarryingCapacity.FiniteHorizonCountingUniqueness
