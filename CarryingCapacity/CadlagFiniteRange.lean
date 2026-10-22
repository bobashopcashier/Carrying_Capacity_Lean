import CarryingCapacity.CadlagCompactBounds
import CarryingCapacity.DiscreteCausalUniqueness

/-!
# Finite compact-time ranges of discrete càdlàg paths

Discrete left limits and right continuity give a finite two-state cover near
each time. Compactness gives a finite range on a bounded horizon. The actual
left states belong to that same finite range. These are derived path facts,
not extra finite-activity assumptions on a candidate jump equation.
-/

noncomputable section
open Set Filter
open scoped Classical Topology

namespace CarryingCapacity.CadlagFiniteRange
open RandomEnvironmentCompensation

variable {E : Type*} [TopologicalSpace E] [DiscreteTopology E] [DecidableEq E]

theorem exists_local_finite_range (X : ℝ → E) (hX : CadlagNonnegative X)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ a b : ℝ, ∃ G : Finset E, a < t ∧ t < b ∧
      ∀ s ∈ Ioo a b, 0 ≤ s → X s ∈ G := by
  obtain ⟨b,htb,hb⟩ := DiscreteCausalUniqueness.exists_right_constant X t (hX.1 t ht)
  by_cases ht0 : t = 0
  · refine ⟨t-1,b,{X t},by linarith,htb,?_⟩
    intro s hs hs0
    simpa only [Finset.mem_singleton] using hb s ⟨ht0 ▸ hs0,hs.2⟩
  · obtain ⟨y,hy⟩ := hX.2 t (lt_of_le_of_ne ht (Ne.symm ht0))
    have he : {s | X s = y} ∈ 𝓝[<] t :=
      hy ((isOpen_discrete ({y} : Set E)).mem_nhds (by simp))
    obtain ⟨a,hat,ha⟩ : ∃ a : ℝ, a < t ∧ Ioo a t ⊆ {s | X s = y} :=
      mem_nhdsLT_iff_exists_Ioo_subset.mp he
    refine ⟨a,b,{X t,y},hat,htb,?_⟩
    intro s hs _
    by_cases hst : s < t
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (ha ⟨hs.1,hst⟩)
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl (hb s ⟨le_of_not_gt hst,hs.2⟩)

theorem exists_finite_range (X : ℝ → E) (hX : CadlagNonnegative X) (T : ℝ) :
    ∃ G : Finset E, ∀ s ∈ Icc 0 T, X s ∈ G := by
  choose a b G ha hb hG using
    (fun t : Icc (0 : ℝ) T => exists_local_finite_range X hX t t.2.1)
  obtain ⟨K,hK⟩ := isCompact_Icc.elim_finite_subcover
    (fun t : Icc (0 : ℝ) T => Ioo (a t) (b t)) (fun _ => isOpen_Ioo)
    (by intro t ht; exact mem_iUnion.mpr ⟨⟨t,ht⟩,ha ⟨t,ht⟩,hb ⟨t,ht⟩⟩)
  refine ⟨K.biUnion G,?_⟩
  intro s hs
  obtain ⟨t,htK,hst⟩ := mem_iUnion₂.mp (hK hs)
  exact Finset.mem_biUnion.mpr ⟨t,htK,hG t s hst hs.1⟩

/-- The left state at the horizon is included, even if the terminal jump
leaves all states previously visited. -/
theorem exists_finite_range_with_left (X L : ℝ → E) (hX : CadlagNonnegative X)
    (hL : ∀ t : ℝ, 0 < t → Tendsto X (𝓝[<] t) (𝓝 (L t))) (T : ℝ) :
    ∃ G : Finset E, (∀ s ∈ Icc 0 T, X s ∈ G) ∧ ∀ s ∈ Ioc 0 T, L s ∈ G := by
  obtain ⟨G,hG⟩ := exists_finite_range X hX T
  refine ⟨G,hG,?_⟩
  intro s hs
  have he : ∀ᶠ t in 𝓝[<] s, X t = L s :=
    hL s hs.1 ((isOpen_discrete ({L s} : Set E)).mem_nhds (by simp))
  have hm : ∀ᶠ t in 𝓝[<] s, X t ∈ G := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hs.1)] with t ht ht0
    exact hG t ⟨ht0.le,ht.le.trans hs.2⟩
  obtain ⟨t,ht,hmem⟩ := (he.and hm).exists
  exact ht ▸ hmem

end CarryingCapacity.CadlagFiniteRange
