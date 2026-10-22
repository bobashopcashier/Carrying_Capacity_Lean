import CarryingCapacity.PredictableStepApproximation
import CarryingCapacity.MarkedIntensity

/-!
# Left limits of arbitrary real càdlàg rates

For a real right-continuous function with left limits, the positive times
where its left limit differs from its current value form a countable set.
The proof encodes each upward jump by rational left/right neighborhoods and
a rational separating level; each such code contains at most one jump.
Applying the same argument to the negative function treats downward jumps.
This is not restricted to monotone or finite-activity paths.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical Topology

namespace CarryingCapacity.CadlagRateRegularity

/-- A rationally coded crossing with one-sided neighborhoods. -/
def crossing (f : ℝ → ℝ) (a b r : ℚ) : Set ℝ :=
  {t | (a : ℝ) < t ∧ t < b ∧
    (∀ u ∈ Ioo (a : ℝ) t, f u < r) ∧ (∀ u ∈ Ico t (b : ℝ), (r : ℝ) < f u)}

theorem crossing_subsingleton (f : ℝ → ℝ) (a b r : ℚ) :
    (crossing f a b r).Subsingleton := by
  intro x hx y hy
  rcases lt_trichotomy x y with hxy | heq | hyx
  · exact False.elim ((not_lt_of_ge (hx.2.2.2 x ⟨le_rfl, hx.2.1⟩).le)
      (hy.2.2.1 x ⟨hx.1, hxy⟩))
  · exact heq
  · exact False.elim ((not_lt_of_ge (hy.2.2.2 y ⟨le_rfl, hy.2.1⟩).le)
      (hx.2.2.1 y ⟨hy.1, hyx⟩))

theorem countable_upward_jumps (f l : ℝ → ℝ)
    (hl : ∀ t : ℝ, 0 < t → Tendsto f (𝓝[<] t) (𝓝 (l t)))
    (hr : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt f (Ici t) t) :
    {t : ℝ | 0 < t ∧ l t < f t}.Countable := by
  have hcount : (⋃ a : ℚ, ⋃ b : ℚ, ⋃ r : ℚ, crossing f a b r).Countable :=
    Set.countable_iUnion (fun a => Set.countable_iUnion (fun b =>
      Set.countable_iUnion (fun r => (crossing_subsingleton f a b r).countable)))
  apply hcount.mono
  intro t ht
  obtain ⟨r, hlr, hrf⟩ := exists_rat_btwn ht.2
  have hleft : {u : ℝ | f u < (r : ℝ)} ∈ 𝓝[<] t :=
    (hl t ht.1) (Iio_mem_nhds hlr)
  obtain ⟨a', hat, hleft'⟩ : ∃ a' : ℝ, a' < t ∧
      Ioo a' t ⊆ {u : ℝ | f u < (r : ℝ)} := mem_nhdsLT_iff_exists_Ioo_subset.mp hleft
  have hright : {u : ℝ | (r : ℝ) < f u} ∈ 𝓝[≥] t :=
    (hr t ht.1.le) (Ioi_mem_nhds hrf)
  obtain ⟨b', htb, hright'⟩ : ∃ b' : ℝ, t < b' ∧
      Ico t b' ⊆ {u : ℝ | (r : ℝ) < f u} := mem_nhdsGE_iff_exists_Ico_subset.mp hright
  obtain ⟨a, ha', hat'⟩ := exists_rat_btwn hat
  obtain ⟨b, htb', hb'⟩ := exists_rat_btwn htb
  refine mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨r, ?_⟩⟩⟩
  refine ⟨hat', htb', ?_, ?_⟩
  · intro u hu
    exact hleft' ⟨ha'.trans hu.1, hu.2⟩
  · intro u hu
    exact hright' ⟨hu.1, hu.2.trans hb'⟩

/-- Countably many current/left-limit discrepancies, without finite jump
activity, monotonicity, bounded variation, or any stochastic assumption. -/
theorem countable_left_ne (f l : ℝ → ℝ)
    (hl : ∀ t : ℝ, 0 < t → Tendsto f (𝓝[<] t) (𝓝 (l t)))
    (hr : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt f (Ici t) t) :
    {t : ℝ | 0 < t ∧ l t ≠ f t}.Countable := by
  have hup := countable_upward_jumps f l hl hr
  have hdown := countable_upward_jumps (fun t => -f t) (fun t => -l t)
    (fun t ht => (hl t ht).neg) (fun t ht => (hr t ht).neg)
  apply (hup.union hdown).mono
  intro t ht
  rcases lt_or_gt_of_ne ht.2 with h | h
  · exact Or.inl ⟨ht.1, h⟩
  · exact Or.inr ⟨ht.1, neg_lt_neg h⟩

/-- Replacing a real càdlàg rate by its left limit does not change a
positive-time Lebesgue integral. -/
theorem ae_left_eq (f l : ℝ → ℝ)
    (hl : ∀ t : ℝ, 0 < t → Tendsto f (𝓝[<] t) (𝓝 (l t)))
    (hr : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt f (Ici t) t) :
    l =ᵐ[MarkedIntensity.positiveVolume] f := by
  letI : NoAtoms MarkedIntensity.positiveVolume := by
    unfold MarkedIntensity.positiveVolume
    infer_instance
  have hnull := (countable_left_ne f l hl hr).ae_not_mem MarkedIntensity.positiveVolume
  have hpos : ∀ᵐ t ∂MarkedIntensity.positiveVolume, 0 < t := by
    change MarkedIntensity.positiveVolume {t : ℝ | ¬ 0 < t} = 0
    simpa only [not_lt, ENNReal.ofReal_zero] using
      MarkedIntensity.positiveVolume_Iic (0 : ℝ)
  filter_upwards [hnull, hpos] with t hn ht
  exact not_ne_iff.mp (fun hne => hn ⟨ht, hne⟩)

/-- A continuous real observable of any càdlàg environment agrees at its
left and current values outside a countable time set. -/
theorem ae_continuous_observable_left_eq {E : Type*} [TopologicalSpace E]
    (X L : ℝ → E) (g : E → ℝ) (hg : Continuous g)
    (hl : ∀ t : ℝ, 0 < t → Tendsto X (𝓝[<] t) (𝓝 (L t)))
    (hr : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt X (Ici t) t) :
    (fun t => g (L t)) =ᵐ[MarkedIntensity.positiveVolume] (fun t => g (X t)) :=
  ae_left_eq (fun t => g (X t)) (fun t => g (L t))
    (fun t ht => hg.continuousAt.tendsto.comp (hl t ht))
    (fun t ht => hg.continuousAt.comp_continuousWithinAt (hr t ht))

/-- For a countable discrete state space, singleton observables identify the
entire left state with the current state at almost every positive time. -/
theorem ae_left_eq_discrete {E : Type*} [TopologicalSpace E] [DiscreteTopology E]
    [Countable E] (X L : ℝ → E)
    (hl : ∀ t : ℝ, 0 < t → Tendsto X (𝓝[<] t) (𝓝 (L t)))
    (hr : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt X (Ici t) t) :
    L =ᵐ[MarkedIntensity.positiveVolume] X := by
  have h (x : E) := ae_continuous_observable_left_eq X L
    (fun y => if y = x then (1 : ℝ) else 0) continuous_of_discreteTopology hl hr
  filter_upwards [ae_all_iff.mpr h] with t ht
  have he := ht (L t)
  by_contra hn
  simp [hn, Ne.symm hn] at he

end CarryingCapacity.CadlagRateRegularity
