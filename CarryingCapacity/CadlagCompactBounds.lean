import CarryingCapacity.RandomEnvironmentCompensation

/-!
# Genuine compact-time bounds for càdlàg rate observables

One-sided limits give local upper bounds. Compactness supplies a finite
subcover and hence a bound on the whole horizon. Thus a finite collection of
continuous rate observables along an arbitrary càdlàg environment has a
samplewise common bound, including all positive-time left limits. No rate
bound is added to the random-environment comparison assumptions.
-/

noncomputable section
open Set Filter
open scoped Classical Topology BigOperators

namespace CarryingCapacity.CadlagCompactBounds
open RandomEnvironmentCompensation

/-- A real càdlàg function is locally bounded above on the nonnegative axis. -/
theorem exists_local_upper_bound (f : ℝ → ℝ) (hf : CadlagNonnegative f)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ a b C : ℝ, a < t ∧ t < b ∧ ∀ s ∈ Ioo a b, 0 ≤ s → f s ≤ C := by
  have hr : {s : ℝ | f s < f t + 1} ∈ 𝓝[≥] t :=
    (hf.1 t ht) (Iio_mem_nhds (by linarith))
  obtain ⟨b, htb, hb⟩ : ∃ b : ℝ, t < b ∧ Ico t b ⊆ {s : ℝ | f s < f t + 1} :=
    mem_nhdsGE_iff_exists_Ico_subset.mp hr
  by_cases ht0 : t = 0
  · refine ⟨t - 1,b,f t + 1,by linarith,htb,?_⟩
    intro s hs hs0
    exact (hb ⟨ht0 ▸ hs0,hs.2⟩).le
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    obtain ⟨l,hl⟩ := hf.2 t htpos
    have hleft : {s : ℝ | f s < l + 1} ∈ 𝓝[<] t := hl (Iio_mem_nhds (by linarith))
    obtain ⟨a,hat,ha⟩ : ∃ a : ℝ, a < t ∧ Ioo a t ⊆ {s : ℝ | f s < l + 1} :=
      mem_nhdsLT_iff_exists_Ioo_subset.mp hleft
    refine ⟨a,b,max (l+1) (f t+1),hat,htb,?_⟩
    intro s hs _
    by_cases hst : s < t
    · exact (ha ⟨hs.1,hst⟩).le.trans (le_max_left _ _)
    · exact (hb ⟨le_of_not_gt hst,hs.2⟩).le.trans (le_max_right _ _)

/-- Compactness, not an integrability or uniform-bound premise, supplies the
finite horizon upper bound. The empty and zero-length horizons are included. -/
theorem exists_upper_bound (f : ℝ → ℝ) (hf : CadlagNonnegative f) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc 0 T, f s ≤ C := by
  choose a b c ha hb hc using
    (fun t : Icc (0 : ℝ) T => exists_local_upper_bound f hf t t.2.1)
  obtain ⟨K,hK⟩ := isCompact_Icc.elim_finite_subcover
    (fun t : Icc (0 : ℝ) T => Ioo (a t) (b t)) (fun _ => isOpen_Ioo)
    (by intro t ht; exact mem_iUnion.mpr ⟨⟨t,ht⟩,ha ⟨t,ht⟩,hb ⟨t,ht⟩⟩)
  refine ⟨∑ t ∈ K, max (c t) 0, Finset.sum_nonneg (fun _ _ => le_max_right _ _),?_⟩
  intro s hs
  obtain ⟨t,htK,hst⟩ := mem_iUnion₂.mp (hK hs)
  exact (hc t s hst hs.1).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun _ _ => le_max_right _ _) htK))

/-- The bound controls the actual left limits as well, including the final
horizon point. -/
theorem exists_upper_bound_with_left (f l : ℝ → ℝ) (hf : CadlagNonnegative f)
    (hl : ∀ t : ℝ, 0 < t → Tendsto f (𝓝[<] t) (𝓝 (l t))) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ s ∈ Icc 0 T, f s ≤ C) ∧ ∀ s ∈ Ioc 0 T, l s ≤ C := by
  obtain ⟨C,hC,hbound⟩ := exists_upper_bound f hf T
  refine ⟨C,hC,hbound,?_⟩
  intro s hs
  apply le_of_tendsto (hl s hs.1)
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hs.1)] with t hts ht0
  exact hbound t ⟨ht0.le,hts.le.trans hs.2⟩

/-- Continuous real observables of a càdlàg environment have simultaneous
current/left compact-time bounds. -/
theorem exists_observable_bound {M : Type*} [TopologicalSpace M]
    (U L : ℝ → M) (hU : CadlagNonnegative U)
    (hL : ∀ t : ℝ, 0 < t → Tendsto U (𝓝[<] t) (𝓝 (L t)))
    (g : M → ℝ) (hg : Continuous g) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ s ∈ Icc 0 T, g (U s) ≤ C) ∧
      ∀ s ∈ Ioc 0 T, g (L s) ≤ C := by
  apply exists_upper_bound_with_left (fun s => g (U s)) (fun s => g (L s))
  · constructor
    · exact fun t ht => hg.continuousAt.comp_continuousWithinAt (hU.1 t ht)
    · intro t ht
      obtain ⟨u,hu⟩ := hU.2 t ht
      exact ⟨g u,hg.continuousAt.tendsto.comp hu⟩
  · exact fun t ht => hg.continuousAt.tendsto.comp (hL t ht)

/-- A finite family of statewise continuous rates admits one bound, even
when the environment itself is random and has infinitely many jumps. -/
theorem exists_finite_observable_bound {M A : Type*} [TopologicalSpace M] [Fintype A]
    (U L : ℝ → M) (hU : CadlagNonnegative U)
    (hL : ∀ t : ℝ, 0 < t → Tendsto U (𝓝[<] t) (𝓝 (L t)))
    (g : A → M → ℝ) (hg : ∀ a, Continuous (g a)) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : A, ∀ s ∈ Ioc 0 T, g a (L s) ≤ C := by
  choose C hC _ hbound using (fun a => exists_observable_bound U L hU hL (g a) (hg a) T)
  refine ⟨∑ a, C a, Finset.sum_nonneg (fun a _ => hC a),?_⟩
  intro a s hs
  exact (hbound a s hs).trans (Finset.single_le_sum (fun b _ => hC b) (Finset.mem_univ a))

end CarryingCapacity.CadlagCompactBounds
