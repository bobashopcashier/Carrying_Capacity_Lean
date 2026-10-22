import CarryingCapacity.MarkedSetCounts

/-!
# Recovering the canonical records from their actual counting measures

On a proved probability-one event the marks lie in half-open unit strips and
arrival sequences are strictly increasing. The full counting-measure family
then uniquely determines every clock increment and mark. This is a concrete
injectivity result, not an assumption that supplied Poisson measures already
come with canonical clock records.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CarryingCapacity.MarkedNoiseReconstruction
open MarkedNoise CountableJumpProcess

variable {J : Type*}

/-- Half-open strip membership avoids ambiguity at integer height boundaries. -/
def Good (ω : Sample J) : Prop :=
  ∀ i : J × ℕ, StrictMono (arrival (ω i).1) ∧ ∀ k, (ω i).2 k ∈ Ico (0 : ℝ) 1

theorem measurableSet_good [Countable J] : MeasurableSet {ω : Sample J | Good ω} := by
  simp only [Good, StrictMono, Set.setOf_forall, Set.setOf_and]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro a
    apply MeasurableSet.iInter
    intro b
    by_cases hab : a < b
    · have ha : Measurable (fun ω : Sample J => arrival (ω i).1 a) :=
        (measurable_arrival a).comp (measurable_pi_apply i).fst
      have hb : Measurable (fun ω : Sample J => arrival (ω i).1 b) :=
        (measurable_arrival b).comp (measurable_pi_apply i).fst
      simpa [hab] using measurableSet_lt ha hb
    · simp [hab]
  · apply MeasurableSet.iInter
    intro k
    exact measurableSet_Ico.preimage ((measurable_pi_apply k).comp (measurable_pi_apply i).snd)

theorem ae_good [Countable J] : ∀ᵐ ω ∂law J, Good ω := by
  have hm : ∀ᵐ u ∂unitMarksLaw, ∀ k, u k ≠ 1 := by
    apply ae_all_iff.mpr
    intro k
    have h : ∀ᵐ x ∂FrozenProcess.uniformUnit, x ≠ (1 : ℝ) := by
      rw [ae_iff]
      simp [FrozenProcess.uniformUnit]
    rw [← unitMarks_coordinate_map k] at h
    exact ae_of_ae_map (measurable_pi_apply k).aemeasurable h
  have hs : ∀ᵐ ω ∂stripLaw, ∀ k, ω.2 k ≠ 1 := by
    rw [← strip_marks_map] at hm
    exact ae_of_ae_map measurable_snd.aemeasurable hm
  have hall : ∀ᵐ ω ∂law J, ∀ i : J × ℕ, ∀ k, (ω i).2 k ≠ 1 := by
    apply ae_all_iff.mpr
    intro i
    have h := hs
    rw [← strip_map J i] at h
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h
  filter_upwards [MarkedNoise.ae_good J, hall] with ω hω hne
  intro i
  exact ⟨(hω i).1.1, fun k => ⟨((hω i).2 k).1,
    lt_of_le_of_ne ((hω i).2 k).2 (hne i k)⟩⟩

theorem singleton_mass_ne_zero_iff (j : J) (ω : Sample J) (z : ℝ × ℝ) :
    countingMeasure j ω {z} ≠ 0 ↔ ∃ p, point j ω p = z := by
  rw [MarkedSetCounts.countingMeasure_eq_count_preimage j ω {z} (measurableSet_singleton z),
    Measure.count_ne_zero_iff]
  rfl

/-- An actual atom identifies its strip from its height alone. -/
theorem strip_eq_of_point_eq {ω η : Sample J} (hω : Good ω) (hη : Good η)
    (j : J) (p q : ℕ × ℕ) (he : point j ω p = point j η q) : p.1 = q.1 := by
  have hh := congrArg Prod.snd he
  change (p.1 : ℝ) + (ω (j,p.1)).2 p.2 = (q.1 : ℝ) + (η (j,q.1)).2 q.2 at hh
  have hp := (hω (j,p.1)).2 p.2
  have hq := (hη (j,q.1)).2 q.2
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · have hc : (p.1 : ℝ) + 1 ≤ q.1 := by exact_mod_cast hlt
    linarith [hp.1, hp.2, hq.1, hq.2]
  · have hc : (q.1 : ℝ) + 1 ≤ p.1 := by exact_mod_cast hgt
    linarith [hp.1, hp.2, hq.1, hq.2]

/-- Equality of actual measures matches every indexed atom, without assuming
simplicity or a chosen coupling of their enumerations. -/
theorem exists_point_eq_of_measure_eq {ω η : Sample J} (j : J)
    (he : countingMeasure j ω = countingMeasure j η) (p : ℕ × ℕ) :
    ∃ q, point j η q = point j ω p := by
  apply (singleton_mass_ne_zero_iff j η _).mp
  rw [← he]
  exact (singleton_mass_ne_zero_iff j ω _).mpr ⟨p, rfl⟩

theorem arrival_eq_of_countingMeasure_eq {ω η : Sample J}
    (hω : Good ω) (hη : Good η) (j : J)
    (he : countingMeasure j ω = countingMeasure j η) (n k : ℕ) :
    arrival (ω (j,n)).1 (k+1) = arrival (η (j,n)).1 (k+1) := by
  have hf : StrictMono (fun k => arrival (ω (j,n)).1 (k+1)) :=
    (hω (j,n)).1.comp (fun _ _ h => Nat.add_lt_add_right h 1)
  have hg : StrictMono (fun k => arrival (η (j,n)).1 (k+1)) :=
    (hη (j,n)).1.comp (fun _ _ h => Nat.add_lt_add_right h 1)
  apply congrFun ((hf.range_inj hg).mp ?_) k
  apply Set.Subset.antisymm
  · rintro _ ⟨l, rfl⟩
    obtain ⟨⟨m,r⟩, hr⟩ := exists_point_eq_of_measure_eq j he (n,l)
    have hn := strip_eq_of_point_eq hη hω j (m,r) (n,l) hr
    dsimp at hn
    subst m
    exact ⟨r, congrArg Prod.fst hr⟩
  · rintro _ ⟨l, rfl⟩
    obtain ⟨⟨m,r⟩, hr⟩ := exists_point_eq_of_measure_eq j he.symm (n,l)
    have hn := strip_eq_of_point_eq hω hη j (m,r) (n,l) hr
    dsimp at hn
    subst m
    exact ⟨r, congrArg Prod.fst hr⟩

/-- On the actual good event no clock or mark information is hidden from the
family of counting measures. -/
theorem injective_countingMeasures : Set.InjOn
    (fun ω : Sample J => fun j => countingMeasure j ω) {ω | Good ω} := by
  intro ω hω η hη he
  funext i
  rcases i with ⟨j,n⟩
  have hm := congrFun he j
  have ha := arrival_eq_of_countingMeasure_eq hω hη j hm n
  apply Prod.ext
  · funext k
    have hk := ha k
    have hprev : arrival (ω (j,n)).1 k = arrival (η (j,n)).1 k := by
      cases k with
      | zero => simp
      | succ k => exact ha k
    rw [arrival_succ, arrival_succ, hprev] at hk
    exact add_left_cancel hk
  · funext k
    obtain ⟨⟨m,l⟩, hl⟩ := exists_point_eq_of_measure_eq j hm (n,k)
    have hn := strip_eq_of_point_eq hη hω j (m,l) (n,k) hl
    dsimp at hn
    subst m
    have ht := congrArg Prod.fst hl
    change arrival (η (j,n)).1 (l+1) = arrival (ω (j,n)).1 (k+1) at ht
    rw [ha k] at ht
    have hkl : l = k := Nat.add_right_cancel ((hη (j,n)).1.injective ht)
    subst l
    have hh := congrArg Prod.snd hl
    change (n : ℝ) + (η (j,n)).2 k = (n : ℝ) + (ω (j,n)).2 k at hh
    exact (add_left_cancel hh).symm

end CarryingCapacity.MarkedNoiseReconstruction
