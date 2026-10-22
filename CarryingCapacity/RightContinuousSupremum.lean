import CarryingCapacity.SynchronousRunningSupremum
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Measurability of genuine running suprema for right-continuous costs

The empirical distance to a varying continuous law need not be locally
constant, even though each discrete-state particle path is locally constant
to the right. Right continuity suffices to recover its supremum over every
real time from rational observations and the terminal value. This supplies
the measurable-supremum bridge needed by the Section 6 grid argument.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CarryingCapacity.RightContinuousSupremum
open SynchronousRunningSupremum

/-- Right continuity identifies the true all-real supremum with countably
many observations. The terminal value is retained even when T is irrational. -/
theorem intervalSup_eq_observedSup_of_rightContinuous (f : ℝ → ℝ≥0∞)
    (T : ℝ) (hT : 0 ≤ T)
    (hf : ∀ t ∈ Ico (0 : ℝ) T, ContinuousWithinAt f (Ici t) t) :
    intervalSup f T = observedSup f T := by
  apply le_antisymm
  · apply iSup_le
    intro t
    by_cases ht : (t : ℝ) = T
    · change f t ≤ f T ⊔ _
      rw [ht]
      exact le_sup_left
    · have htT : (t : ℝ) < T := lt_of_le_of_ne t.property.2 ht
      by_contra hn
      have hlt : observedSup f T < f t := lt_of_not_ge hn
      have he : {u | observedSup f T < f u} ∈ 𝓝[≥] (t : ℝ) :=
        (hf t ⟨t.property.1, htT⟩).eventually (Ioi_mem_nhds hlt)
      obtain ⟨b, hb, hlocal⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp he
      obtain ⟨q, hq, hqb⟩ := exists_rat_btwn (lt_min hb htT)
      have hqI : (q : ℝ) ∈ Icc (0 : ℝ) T :=
        ⟨t.property.1.trans hq.le, (lt_min_iff.mp hqb).2.le⟩
      have hval := hlocal ⟨hq.le, (lt_min_iff.mp hqb).1⟩
      have hupper : f q ≤ observedSup f T := by
        apply le_sup_of_le_right
        apply le_iSup_of_le q
        simp only [if_pos hqI, le_refl]
      exact (not_lt_of_ge hupper) hval
  · apply sup_le
    · exact le_iSup_of_le ⟨T, hT, le_rfl⟩ le_rfl
    · apply iSup_le
      intro q
      by_cases hq : (q : ℝ) ∈ Icc (0 : ℝ) T
      · simpa only [if_pos hq] using
          (le_iSup_of_le (⟨(q : ℝ), hq⟩ : Icc (0 : ℝ) T) (le_refl (f q)))
      · simp only [if_neg hq, zero_le]

/-- Measurable evaluations and almost-sure right continuity imply AE
measurability of the exact uncountable supremum, including a zero horizon. -/
theorem aemeasurable_intervalSup_of_rightContinuous {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ → ℝ≥0∞) (T : ℝ) (hT : 0 ≤ T)
    (hm : ∀ t ∈ Icc (0 : ℝ) T, AEMeasurable (fun ω => f ω t) μ)
    (hright : ∀ᵐ ω ∂μ, ∀ t ∈ Ico (0 : ℝ) T,
      ContinuousWithinAt (f ω) (Ici t) t) :
    AEMeasurable (fun ω => intervalSup (f ω) T) μ := by
  have ho : AEMeasurable (fun ω => observedSup (f ω) T) μ := by
    apply (hm T ⟨hT, le_rfl⟩).sup
    apply AEMeasurable.iSup
    intro q
    by_cases hq : (q : ℝ) ∈ Icc (0 : ℝ) T
    · simpa only [if_pos hq] using hm q hq
    · simp only [if_neg hq]
      exact aemeasurable_const
  apply ho.congr
  filter_upwards [hright] with ω hω
  exact (intervalSup_eq_observedSup_of_rightContinuous (f ω) T hT hω).symm

end CarryingCapacity.RightContinuousSupremum
