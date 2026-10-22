import CarryingCapacity.MarkedNoise

/-! Measurable chronological lists for a countable, randomly selected event family. -/
noncomputable section
open MeasureTheory Set
open scoped Classical

namespace CarryingCapacity.ChronologicalEvents
variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I]

section ListSort
variable [MeasurableSpace (List I)] [MeasurableSingletonClass (List I)]
    (time : I → Ω → ℝ) (htime : ∀ i, Measurable (time i))
include htime

theorem measurable_orderedInsert (i : I) (l : List I) :
    Measurable (fun ω => l.orderedInsert (fun a b => time a ω ≤ time b ω) i) := by
  induction l with
  | nil => exact measurable_const
  | cons j l ih =>
    change Measurable (fun ω => if time i ω ≤ time j ω then i :: j :: l
      else j :: l.orderedInsert (fun a b => time a ω ≤ time b ω) i)
    exact Measurable.ite (measurableSet_le (htime i) (htime j)) measurable_const
      ((measurable_of_countable (List.cons j)).comp ih)

theorem measurable_joint_orderedInsert (i : I) :
    Measurable (fun p : Ω × List I =>
      p.2.orderedInsert (fun a b => time a p.1 ≤ time b p.1) i) := by
  apply measurable_from_prod_countable
  exact measurable_orderedInsert time htime i

theorem measurable_insertionSort (l : List I) :
    Measurable (fun ω => l.insertionSort (fun a b => time a ω ≤ time b ω)) := by
  induction l with
  | nil => exact measurable_const
  | cons i l ih =>
    exact (measurable_joint_orderedInsert time htime i).comp (measurable_id.prodMk ih)

theorem measurable_sort_random_list (L : Ω → List I) (hL : Measurable L) :
    Measurable (fun ω => (L ω).insertionSort (fun a b => time a ω ≤ time b ω)) := by
  have h : Measurable (fun p : Ω × List I =>
      p.2.insertionSort (fun a b => time a p.1 ≤ time b p.1)) :=
    measurable_from_prod_countable (measurable_insertionSort time htime)
  exact h.comp (measurable_id.prodMk hL)
end ListSort

/-- Finite selected events; empty on the measurable exceptional event that the
selected set is infinite. Its use requires no globally assumed local finiteness. -/
def selectedFinset (A : Ω → Set I) (ω : Ω) : Finset I :=
  if h : (A ω).Finite then h.toFinset else ∅

omit [MeasurableSpace Ω] [Countable I] in
theorem selectedFinset_eq_iff (A : Ω → Set I) (ω : Ω) (s : Finset I) :
    selectedFinset A ω = s ↔ A ω = (s : Set I) ∨ (¬(A ω).Finite ∧ s = ∅) := by
  by_cases h : (A ω).Finite
  · rw [selectedFinset, dif_pos h]
    constructor
    · intro he
      left
      rw [← he, h.coe_toFinset]
    · rintro (he | ⟨hf, _⟩)
      · exact Finset.coe_injective (h.coe_toFinset.trans he)
      · exact False.elim (hf h)
  · rw [selectedFinset, dif_neg h]
    constructor
    · intro he
      exact Or.inr ⟨h, he.symm⟩
    · rintro (he | ⟨_, he⟩)
      · exact False.elim (h (he ▸ s.finite_toSet))
      · exact he.symm

theorem measurable_selectedFinset [MeasurableSpace (Finset I)]
    (A : Ω → Set I) (hA : Measurable A) : Measurable (selectedFinset A) := by
  apply measurable_to_countable'
  intro s
  have he : MeasurableSet {ω | A ω = (s : Set I)} := by
    have hs : {ω | A ω = (s : Set I)} = ⋂ i : I, {ω | i ∈ A ω ↔ i ∈ s} := by
      ext ω
      simp only [mem_setOf_eq, mem_iInter, Set.ext_iff, Finset.mem_coe]
    rw [hs]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i ∈ s
    · simpa only [hi, iff_true] using (measurableSet_mem i).preimage hA
    · simpa only [hi, iff_false] using (measurableSet_not_mem i).preimage hA
  have hf : MeasurableSet {ω | ¬(A ω).Finite} :=
    ((MeasurableSet.setOf_finite (α := I)).preimage hA).compl
  have hh : {ω | selectedFinset A ω = s} =
      {ω | A ω = (s : Set I)} ∪ ({ω | ¬(A ω).Finite} ∩ {ω | s = ∅}) := by
    ext ω
    exact selectedFinset_eq_iff A ω s
  change MeasurableSet {ω | selectedFinset A ω = s}
  rw [hh]
  exact he.union (hf.inter (by by_cases hs : s = ∅ <;> simp [hs]))

omit [MeasurableSpace Ω] [Countable I] in
theorem mem_selectedFinset (A : Ω → Set I) (ω : Ω) (h : (A ω).Finite) (i : I) :
    i ∈ selectedFinset A ω ↔ i ∈ A ω := by
  simp [selectedFinset, h]

/-- A genuine sorted list of the selected countable event identifiers. -/
def chronologicalList (time : I → Ω → ℝ) (A : Ω → Set I) (ω : Ω) : List I :=
  (selectedFinset A ω).toList.insertionSort (fun a b => time a ω ≤ time b ω)

section Measurability
variable [MeasurableSpace (Finset I)] [MeasurableSingletonClass (Finset I)]
    [MeasurableSpace (List I)] [MeasurableSingletonClass (List I)]

theorem measurable_chronologicalList (time : I → Ω → ℝ) (htime : ∀ i, Measurable (time i))
    (A : Ω → Set I) (hA : Measurable A) : Measurable (chronologicalList time A) := by
  apply measurable_sort_random_list time htime
  exact (measurable_of_countable Finset.toList).comp (measurable_selectedFinset A hA)
end Measurability

omit [MeasurableSpace Ω] [Countable I] in
theorem chronologicalList_mem (time : I → Ω → ℝ) (A : Ω → Set I) (ω : Ω)
    (hfin : (A ω).Finite) (i : I) :
    i ∈ chronologicalList time A ω ↔ i ∈ A ω := by
  rw [chronologicalList, List.mem_insertionSort, Finset.mem_toList]
  exact mem_selectedFinset A ω hfin i

omit [MeasurableSpace Ω] [Countable I] in
theorem chronologicalList_nodup (time : I → Ω → ℝ) (A : Ω → Set I) (ω : Ω) :
    (chronologicalList time A ω).Nodup :=
  (List.perm_insertionSort _ _).nodup_iff.mpr (Finset.nodup_toList _)

omit [MeasurableSpace Ω] [Countable I] in
theorem chronologicalList_sorted (time : I → Ω → ℝ) (A : Ω → Set I) (ω : Ω) :
    (chronologicalList time A ω).Sorted (fun a b => time a ω ≤ time b ω) := by
  let r : I → I → Prop := fun a b => time a ω ≤ time b ω
  letI : IsTotal I r := ⟨fun a b => le_total _ _⟩
  letI : IsTrans I r := ⟨fun a b c => le_trans⟩
  exact List.sorted_insertionSort r _


omit [MeasurableSpace Ω] [Countable I] in
/-- Distinct times upgrade the constructed weak chronological ordering to a
strict one; no deterministic tie-breaking hypothesis is imposed. -/
theorem chronologicalList_strict (time : I → Ω → ℝ) (A : Ω → Set I) (ω : Ω)
    (hinj : Function.Injective (fun i => time i ω)) :
    (chronologicalList time A ω).Sorted (fun a b => time a ω < time b ω) := by
  exact (chronologicalList_sorted time A ω).imp₂
    (fun a b hab hne => lt_of_le_of_ne hab (fun he => hne (hinj he)))
    (chronologicalList_nodup time A ω)

omit [MeasurableSpace Ω] [Countable I] in
/-- Nested selected sets produce the same chronological list after deleting
the extra events. This supplies the precise list identity needed before the
state-recursion rejection lemma can be applied. -/
theorem chronologicalList_filter (time : I → Ω → ℝ) (A B : Ω → Set I) (ω : Ω)
    (ha : (A ω).Finite) (hb : (B ω).Finite) (hsub : A ω ⊆ B ω)
    (hinj : Function.Injective (fun i => time i ω)) :
    (chronologicalList time B ω).filter (fun i => decide (i ∈ A ω)) =
      chronologicalList time A ω := by
  let r : I → I → Prop := fun a b => time a ω ≤ time b ω
  letI : IsAntisymm I r := ⟨fun a b hab hba => hinj (le_antisymm hab hba)⟩
  apply List.eq_of_perm_of_sorted (r := r)
  · apply (List.perm_ext_iff_of_nodup
      ((chronologicalList_nodup time B ω).filter _)
      (chronologicalList_nodup time A ω)).mpr
    intro i
    simp only [List.mem_filter, decide_eq_true_eq, chronologicalList_mem time B ω hb,
      chronologicalList_mem time A ω ha]
    exact ⟨And.right, fun h => ⟨hsub h, h⟩⟩
  · exact (chronologicalList_sorted time B ω).filter _
  · exact chronologicalList_sorted time A ω


omit [MeasurableSpace Ω] [Countable I] in
/-- Keeping events before a time threshold yields a prefix of a chronological list. -/
theorem time_filter_isPrefix (time : I → ℝ) (T : ℝ) (l : List I)
    (hs : l.Sorted (fun a b => time a ≤ time b)) :
    l.filter (fun i => decide (time i ≤ T)) <+: l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : time a ≤ T
    · simpa [ha] using ih hs.of_cons
    · have hn : l.filter (fun i => decide (time i ≤ T)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro b hb
        have hab := List.rel_of_sorted_cons hs b hb
        simpa only [decide_eq_true_eq] using not_le_of_gt ((lt_of_not_ge ha).trans_le hab)
      simp [ha, hn]

section MarkedBoxes
variable {J : Type*} [Countable J]
abbrev Event (J : Type*) := J × (ℕ × ℕ)

local instance listMeasurable : MeasurableSpace (List (Event J)) := ⊤
local instance listSingleton : MeasurableSingletonClass (List (Event J)) := ⟨fun _ => trivial⟩
local instance finsetMeasurable : MeasurableSpace (Finset (Event J)) := ⊤
local instance finsetSingleton : MeasurableSingletonClass (Finset (Event J)) := ⟨fun _ => trivial⟩

/-- Joint sample, time horizon, and height cutoff. -/
abbrev BoxInput (J : Type*) := MarkedNoise.Sample J × ℝ × ℝ

def boxSet (p : BoxInput J) : Set (Event J) :=
  {e | MarkedNoise.point e.1 p.1 e.2 ∈ Iic p.2.1 ×ˢ Iic p.2.2}

def eventTime (e : Event J) (p : BoxInput J) : ℝ := (MarkedNoise.point e.1 p.1 e.2).1

omit [Countable J] in
theorem measurable_eventTime (e : Event J) : Measurable (eventTime e : BoxInput J → ℝ) :=
  ((MarkedNoise.measurable_point e.1 e.2).comp measurable_fst).fst

omit [Countable J] in
theorem measurable_boxSet : Measurable (boxSet : BoxInput J → Set (Event J)) := by
  apply measurable_set_iff.mpr
  intro e
  apply measurable_to_prop
  rw [preimage_singleton_true]
  change MeasurableSet ({p : BoxInput J | eventTime e p ≤ p.2.1} ∩
    {p : BoxInput J | (MarkedNoise.point e.1 p.1 e.2).2 ≤ p.2.2})
  exact (measurableSet_le (measurable_eventTime e) measurable_snd.fst).inter
    (measurableSet_le (((MarkedNoise.measurable_point e.1 e.2).comp measurable_fst).snd)
      measurable_snd.snd)

/-- The actual common-strip atoms in a box, listed in chronological order.
This is a total function and is defined jointly in sample, horizon and cutoff. -/
def boxedList (p : BoxInput J) : List (Event J) := chronologicalList eventTime boxSet p

theorem measurable_boxedList : Measurable (boxedList : BoxInput J → List (Event J)) :=
  measurable_chronologicalList eventTime measurable_eventTime boxSet measurable_boxSet

/-- Every bounded box is enumerated exactly, on the previously proved single
full-measure event of local finiteness. -/
theorem ae_boxedList_mem [Finite J] : ∀ᵐ ω ∂MarkedNoise.law J, ∀ T C : ℝ, ∀ e : Event J,
    e ∈ boxedList (ω, T, C) ↔ MarkedNoise.point e.1 ω e.2 ∈ Iic T ×ˢ Iic C := by
  filter_upwards [MarkedNoise.ae_finite_total_points (J := J)] with ω hω
  intro T C e
  exact chronologicalList_mem eventTime boxSet (ω, T, C) (hω T C) e

/-- Its event times are strictly increasing, simultaneously for all boxes. -/
theorem ae_boxedList_strict : ∀ᵐ ω ∂MarkedNoise.law J, ∀ T C : ℝ,
    (boxedList (ω, T, C)).Sorted
      (fun e f => (MarkedNoise.point e.1 ω e.2).1 < (MarkedNoise.point f.1 ω f.2).1) := by
  filter_upwards [MarkedNoise.ae_distinct_event_times (J := J)] with ω hω
  intro T C
  exact chronologicalList_strict eventTime boxSet (ω, T, C) hω

/-- Raising the vertical cutoff inserts only the additional high marks; deletion
of those marks recovers exactly the lower-cutoff chronological list. -/
theorem ae_boxedList_height_filter [Finite J] : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ T C₁ C₂ : ℝ, C₁ ≤ C₂ →
      (boxedList (ω, T, C₂)).filter
        (fun e => decide ((MarkedNoise.point e.1 ω e.2).2 ≤ C₁)) =
      boxedList (ω, T, C₁) := by
  filter_upwards [MarkedNoise.ae_finite_total_points (J := J),
    MarkedNoise.ae_distinct_event_times (J := J)] with ω hfin hinj
  intro T C₁ C₂ hC
  have hsub : boxSet (ω, T, C₁) ⊆ boxSet (ω, T, C₂) := by
    intro e he
    exact ⟨he.1, he.2.trans hC⟩
  have hf := chronologicalList_filter
    (fun e (w : MarkedNoise.Sample J) => (MarkedNoise.point e.1 w e.2).1)
    (fun w => boxSet (w, T, C₁)) (fun w => boxSet (w, T, C₂))
    ω (hfin T C₁) (hfin T C₂) hsub hinj
  change (boxedList (ω, T, C₂)).filter (fun e => decide (e ∈ boxSet (ω, T, C₁))) =
    boxedList (ω, T, C₁) at hf
  rw [← hf]
  apply List.filter_congr
  intro e he
  have ht := ((chronologicalList_mem eventTime boxSet (ω, T, C₂) (hfin T C₂) e).mp he).1
  change (MarkedNoise.point e.1 ω e.2).1 ≤ T at ht
  simp only [boxSet, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Iic, ht, true_and]


/-- Increasing the time horizon extends the same event list. Filtering back to
the earlier horizon recovers exactly its earlier chronological list. -/
theorem ae_boxedList_time_filter [Finite J] : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ T₁ T₂ C : ℝ, T₁ ≤ T₂ →
      (boxedList (ω, T₂, C)).filter
        (fun e => decide ((MarkedNoise.point e.1 ω e.2).1 ≤ T₁)) =
      boxedList (ω, T₁, C) := by
  filter_upwards [MarkedNoise.ae_finite_total_points (J := J),
    MarkedNoise.ae_distinct_event_times (J := J)] with ω hfin hinj
  intro T₁ T₂ C hT
  have hsub : boxSet (ω, T₁, C) ⊆ boxSet (ω, T₂, C) := by
    intro e he
    exact ⟨he.1.trans hT, he.2⟩
  have hf := chronologicalList_filter
    (fun e (w : MarkedNoise.Sample J) => (MarkedNoise.point e.1 w e.2).1)
    (fun w => boxSet (w, T₁, C)) (fun w => boxSet (w, T₂, C))
    ω (hfin T₁ C) (hfin T₂ C) hsub hinj
  change (boxedList (ω, T₂, C)).filter (fun e => decide (e ∈ boxSet (ω, T₁, C))) =
    boxedList (ω, T₁, C) at hf
  rw [← hf]
  apply List.filter_congr
  intro e he
  have hh := ((chronologicalList_mem eventTime boxSet (ω, T₂, C) (hfin T₂ C) e).mp he).2
  change (MarkedNoise.point e.1 ω e.2).2 ≤ C at hh
  simp only [boxSet, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Iic, hh, and_true]

/-- On a common probability-one event, chronological event lists at earlier
times are literal prefixes of those at later times. -/
theorem ae_boxedList_time_prefix [Finite J] : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ T₁ T₂ C : ℝ, T₁ ≤ T₂ → boxedList (ω, T₁, C) <+: boxedList (ω, T₂, C) := by
  filter_upwards [ae_boxedList_time_filter (J := J)] with ω hω
  intro T₁ T₂ C hT
  rw [← hω T₁ T₂ C hT]
  exact time_filter_isPrefix (fun e : Event J => (MarkedNoise.point e.1 ω e.2).1) T₁ _
    (chronologicalList_sorted eventTime boxSet (ω, T₂, C))

end MarkedBoxes

end CarryingCapacity.ChronologicalEvents
