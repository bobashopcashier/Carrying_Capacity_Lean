import Mathlib

/-!
# Finite time-grid refinement of Boolean rectangle combinations

A finite Boolean expression in lower time-height rectangles depends on time
only through finitely many threshold comparisons. Sorting those thresholds
inside a bounded horizon produces cells on which every vertical section is
constant. No stochastic-law premise is used in this deterministic refinement.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical

namespace CarryingCapacity.TimeGridRefinement

/-- The time coordinate is observed only through the listed thresholds. -/
def DeterminedBy (K : Finset ℝ) (S : Set (ℝ × ℝ)) : Prop :=
  ∀ s t : ℝ, (∀ r ∈ K, s ≤ r ↔ t ≤ r) →
    ∀ h : ℝ, (s, h) ∈ S ↔ (t, h) ∈ S

/-- Finite threshold dependence is preserved by taking the generated algebra. -/
theorem exists_thresholds_of_mem_algebra (𝒜 : Set (Set (ℝ × ℝ)))
    (hbase : ∀ S ∈ 𝒜, ∃ K, DeterminedBy K S)
    (S : Set (ℝ × ℝ)) (hS : S ∈ generateSetAlgebra 𝒜) :
    ∃ K, DeterminedBy K S := by
  induction hS with
  | base S hS => exact hbase S hS
  | empty => exact ⟨∅, by intro s t h h'; simp⟩
  | compl S _ ih =>
    obtain ⟨K, hK⟩ := ih
    exact ⟨K, fun s t h h' => not_congr (hK s t h h')⟩
  | union S U _ _ ihS ihU =>
    obtain ⟨K, hK⟩ := ihS
    obtain ⟨L, hL⟩ := ihU
    refine ⟨K ∪ L, ?_⟩
    intro s t h h'
    exact or_congr (hK s t (fun r hr => h r (Finset.mem_union_left _ hr)) h')
      (hL s t (fun r hr => h r (Finset.mem_union_right _ hr)) h')

/-- A lower rectangle has just one relevant time threshold. -/
theorem lowerRectangle_determined (a b : ℝ) : DeterminedBy {a} (Iic a ×ˢ Iic b) := by
  intro s t h h'
  exact and_congr (h a (by simp)) Iff.rfl

/-- The adjacent cells of a monotone finite grid cover its endpoint interval. -/
theorem mem_grid_iff {q : ℕ} (u : Fin (q + 1) → ℝ) (hu : Monotone u) (t : ℝ) :
    t ∈ Ioc (u 0) (u (Fin.last q)) ↔
      ∃ a : Fin q, t ∈ Ioc (u a.castSucc) (u a.succ) := by
  constructor
  · intro ht
    let F : Finset (Fin (q + 1)) := Finset.univ.filter (fun i => t ≤ u i)
    have hF : F.Nonempty := ⟨Fin.last q, by simp [F, ht.2]⟩
    let i : Fin (q + 1) := F.min' hF
    have hi : t ≤ u i := (Finset.mem_filter.mp (Finset.min'_mem F hF)).2
    have hi0 : i ≠ 0 := by
      intro he
      rw [he] at hi
      exact (not_le_of_gt ht.1) hi
    obtain ⟨a, ha⟩ := Fin.exists_succ_eq.mpr hi0
    refine ⟨a, ?_, ha ▸ hi⟩
    by_contra hn
    have hmem : a.castSucc ∈ F := by simp [F, le_of_not_gt hn]
    have hle : i ≤ a.castSucc := Finset.min'_le F _ hmem
    rw [← ha] at hle
    exact (not_le_of_gt (Fin.castSucc_lt_succ a)) hle
  · rintro ⟨a, ha⟩
    exact ⟨lt_of_le_of_lt (hu (Fin.zero_le _)) ha.1,
      ha.2.trans (hu (Fin.le_last _))⟩

/-- Sort the thresholds between zero and the horizon, retaining both endpoints.
Every original threshold comparison is constant within every resulting cell. -/
theorem exists_threshold_grid (K : Finset ℝ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ q : ℕ, ∃ u : Fin (q + 1) → ℝ,
      StrictMono u ∧ u 0 = 0 ∧ u (Fin.last q) = T ∧
      ∀ r ∈ K, ∀ a : Fin q, ∀ t ∈ Ioc (u a.castSucc) (u a.succ),
        t ≤ r ↔ u a.succ ≤ r := by
  let L : Finset ℝ := (insert 0 (insert T K)).filter (fun r => 0 ≤ r ∧ r ≤ T)
  have h0 : 0 ∈ L := by simp [L, hT]
  have hlast : T ∈ L := by simp [L, hT]
  have hcard : L.card = (L.card - 1) + 1 := by
    have hp : 0 < L.card := Finset.card_pos.mpr ⟨0, h0⟩
    omega
  let u : Fin ((L.card - 1) + 1) → ℝ := L.orderEmbOfFin hcard
  have hmono : StrictMono u := (L.orderEmbOfFin hcard).strictMono
  have hmem (i) : u i ∈ L := L.orderEmbOfFin_mem hcard i
  have hrange : Set.range u = (L : Set ℝ) := L.range_orderEmbOfFin hcard
  have hindex (r : ℝ) (hr : r ∈ L) : ∃ i, u i = r := by
    have : r ∈ Set.range u := by rw [hrange]; exact hr
    exact this
  have hu0 : u 0 = 0 := by
    apply le_antisymm
    · obtain ⟨i, hi⟩ := hindex 0 h0
      exact (hmono.monotone (Fin.zero_le i)).trans_eq hi
    · exact (Finset.mem_filter.mp (hmem 0)).2.1
  have hulast : u (Fin.last (L.card - 1)) = T := by
    apply le_antisymm
    · exact (Finset.mem_filter.mp (hmem _)).2.2
    · obtain ⟨i, hi⟩ := hindex T hlast
      exact hi.symm.trans_le (hmono.monotone (Fin.le_last i))
  refine ⟨L.card - 1, u, hmono, hu0, hulast, ?_⟩
  intro r hr a t ht
  have ht0 : 0 < t := lt_of_le_of_lt
    (by simpa only [hu0] using hmono.monotone (Fin.zero_le a.castSucc)) ht.1
  have husT : u a.succ ≤ T := (hmono.monotone (Fin.le_last _)).trans_eq hulast
  by_cases hr0 : 0 ≤ r
  · by_cases hrT : r ≤ T
    · have hrL : r ∈ L := by simp [L, hr, hr0, hrT]
      obtain ⟨i, hi⟩ := hindex r hrL
      constructor
      · intro htr
        by_contra hn
        have hii : i < a.succ := hmono.lt_iff_lt.mp (hi ▸ lt_of_not_ge hn)
        have hile : i ≤ a.castSucc := by
          change i.val ≤ a.val
          change i.val < a.val + 1 at hii
          omega
        exact (not_le_of_gt ht.1) (htr.trans (hi.symm.trans_le (hmono.monotone hile)))
      · exact fun h => ht.2.trans h
    · exact iff_of_true (ht.2.trans (husT.trans (le_of_not_ge hrT)))
        (husT.trans (le_of_not_ge hrT))
  · have hrneg : r < 0 := lt_of_not_ge hr0
    exact iff_of_false (not_le_of_gt (hrneg.trans ht0))
      (not_le_of_gt (hrneg.trans (ht0.trans_le ht.2)))

/-- Different adjacent cells are disjoint, even for non-strict grids. -/
theorem pairwise_grid_cells {q : ℕ} (u : Fin (q + 1) → ℝ) (hu : Monotone u) :
    Pairwise (fun a b : Fin q => Disjoint
      (Ioc (u a.castSucc) (u a.succ)) (Ioc (u b.castSucc) (u b.succ))) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro t ha hb
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have hle : a.succ ≤ b.castSucc := by
      change a.val + 1 ≤ b.val
      exact hlt
    exact (not_le_of_gt hb.1) (ha.2.trans (hu hle))
  · have hle : b.succ ≤ a.castSucc := by
      change b.val + 1 ≤ a.val
      exact hgt
    exact (not_le_of_gt ha.1) (hb.2.trans (hu hle))

/-- A finite disjoint family with finite time thresholds becomes disjoint
measurable height categories on one common finite time grid. -/
theorem exists_grid_representation {ι : Type*} [Fintype ι]
    (S : ι → Set (ℝ × ℝ)) (hS : ∀ i, MeasurableSet (S i))
    (hcuts : ∀ i, ∃ K, DeterminedBy K (S i))
    (hdis : Pairwise (fun i j => Disjoint (S i) (S j)))
    (T C : ℝ) (hT : 0 ≤ T) :
    ∃ q : ℕ, ∃ u : Fin (q + 1) → ℝ, ∃ B : Fin q → ι → Set ℝ,
      Monotone u ∧ u 0 = 0 ∧ u (Fin.last q) = T ∧
      (∀ a i, MeasurableSet (B a i)) ∧ (∀ a i, B a i ⊆ Iio C) ∧
      (∀ a, Pairwise (fun i j => Disjoint (B a i) (B a j))) ∧
      ∀ i, S i ∩ (Ioc 0 T ×ˢ Iio C) =
        ⋃ a : Fin q, Ioc (u a.castSucc) (u a.succ) ×ˢ B a i := by
  choose K hK using hcuts
  let L := Finset.univ.biUnion K
  obtain ⟨q, u, hu, hu0, huT, hgrid⟩ := exists_threshold_grid L T hT
  let B : Fin q → ι → Set ℝ := fun a i =>
    (fun h : ℝ => (u a.succ, h)) ⁻¹' S i ∩ Iio C
  have he (i : ι) (a : Fin q) (t : ℝ)
      (ht : t ∈ Ioc (u a.castSucc) (u a.succ)) (h : ℝ) :
      (t, h) ∈ S i ↔ (u a.succ, h) ∈ S i := by
    apply hK i t (u a.succ)
    intro r hr
    exact hgrid r (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hr⟩) a t ht
  refine ⟨q, u, B, hu.monotone, hu0, huT, ?_, ?_, ?_, ?_⟩
  · exact fun a i => ((hS i).preimage (measurable_const.prodMk measurable_id)).inter
      measurableSet_Iio
  · exact fun a i _ h => h.2
  · intro a i j hij
    apply Set.disjoint_left.mpr
    intro h hi hj
    exact Set.disjoint_left.mp (hdis hij) hi.1 hj.1
  · intro i
    ext p
    constructor
    · rintro ⟨hSi, ht, hh⟩
      obtain ⟨a, ha⟩ := (mem_grid_iff u hu.monotone p.1).mp (by simpa [hu0, huT] using ht)
      exact mem_iUnion.mpr ⟨a, ha, (he i a p.1 ha p.2).mp hSi, hh⟩
    · intro hp
      obtain ⟨a, ha, hh⟩ := mem_iUnion.mp hp
      refine ⟨(he i a p.1 ha p.2).mpr hh.1, ?_, hh.2⟩
      simpa [hu0, huT] using (mem_grid_iff u hu.monotone p.1).mpr ⟨a, ha⟩

end CarryingCapacity.TimeGridRefinement
