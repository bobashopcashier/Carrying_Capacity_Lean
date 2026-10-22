import CarryingCapacity.CommonFrozenExit
import CarryingCapacity.CommonNoiseFiltration

/-!
# Genuine stopping times in the completed common-noise filtration

Each finite-time noise history is augmented by all null sets of the ambient
marked-noise law. Equivalently, its measurable sets are the sets equal almost
everywhere to a raw history-measurable set. This is the smallest such
augmentation, not the full ambient sigma algebra. At infinity the filtration
uses the supremum of its finite-time histories.

The exact `CommonFrozenExit.firstExit` is a stopping time for this filtration:
on a probability-one event its sublevel event at time `t` is precisely that the
frozen path is outside the active set at time `t`. Completion is essential to
transfer this equality across the exceptional samples. Right continuity of the
filtration is not needed for this particular argument and is not claimed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal

namespace CarryingCapacity.CommonFrozenStopping
open CommonFrozenProcess CommonFrozenRegularity CommonFrozenExit

/-- The completed ambient sigma algebra of the actual marked-noise law. -/
def completedSpace (J : Type*) : MeasurableSpace (MarkedNoise.Sample J) :=
  EventuallyMeasurableSpace inferInstance (ae (MarkedNoise.law J))

/-- The actual law extended to its completed ambient sigma algebra. -/
def completedLaw (J : Type*) : @Measure (MarkedNoise.Sample J) (completedSpace J) :=
  (MarkedNoise.law J).completion

@[simp] theorem completedLaw_apply (J : Type*) (s : Set (MarkedNoise.Sample J)) :
    completedLaw J s = MarkedNoise.law J s := rfl

@[simp] theorem ae_completedLaw (J : Type*) : ae (completedLaw J) = ae (MarkedNoise.law J) := rfl

instance completedLaw_probability (J : Type*) : IsProbabilityMeasure (completedLaw J) :=
  ⟨by change MarkedNoise.law J univ = 1; exact measure_univ⟩

/-- The extended ambient law is complete, with the same probabilities as the
original marked-noise law on every set. -/
instance completedLaw_complete (J : Type*) : (completedLaw J).IsComplete :=
  inferInstanceAs ((MarkedNoise.law J).completion.IsComplete)

/-- A finite-time history enlarged only by ambient null sets. -/
def completedAt (J : Type*) (t : ℝ) : MeasurableSpace (MarkedNoise.Sample J) :=
  EventuallyMeasurableSpace (CommonNoiseFiltration.filtration J t) (ae (MarkedNoise.law J))

/-- This description explicitly records the information in the augmented history. -/
theorem measurableSet_completedAt_iff (J : Type*) (t : ℝ) (s : Set (MarkedNoise.Sample J)) :
    MeasurableSet[completedAt J t] s ↔
      ∃ r, MeasurableSet[CommonNoiseFiltration.filtration J t] r ∧
        s =ᵐ[MarkedNoise.law J] r := Iff.rfl

theorem raw_le_completedAt (J : Type*) (t : ℝ) :
    CommonNoiseFiltration.filtration J t ≤ completedAt J t :=
  EventuallyMeasurableSpace.measurable_le

/-- Every subset of an ambient null event is already present at every time. -/
theorem measurableSet_completedAt_of_null (J : Type*) (t : ℝ)
    {s : Set (MarkedNoise.Sample J)} (hs : MarkedNoise.law J s = 0) :
    MeasurableSet[completedAt J t] s := by
  apply (measurableSet_completedAt_iff J t s).mpr
  refine ⟨∅, ?_, ?_⟩
  · exact @MeasurableSet.empty _ (CommonNoiseFiltration.filtration J t)
  · exact ae_eq_empty.mpr hs

/-- The augmentation is minimal among sigma algebras containing the raw
history and every ambient null set. In particular it does not add arbitrary
future information. -/
theorem completedAt_le_of_null_sets (J : Type*) (t : ℝ)
    (m : MeasurableSpace (MarkedNoise.Sample J))
    (hraw : CommonNoiseFiltration.filtration J t ≤ m)
    (hnull : ∀ s, MarkedNoise.law J s = 0 → MeasurableSet[m] s) : completedAt J t ≤ m := by
  intro s hs
  obtain ⟨r, hr, heq⟩ := hs
  have hsr := hnull (s \ r) (ae_le_set.mp heq.le)
  have hrs := hnull (r \ s) (ae_le_set.mp heq.symm.le)
  have hid : s = (r \ (r \ s)) ∪ (s \ r) := by
    ext x
    simp only [mem_union, mem_diff]
    tauto
  rw [hid]
  exact ((hraw r hr).diff hrs).union hsr

theorem completedAt_mono (J : Type*) : Monotone (completedAt J) := by
  intro s t hst a ha
  obtain ⟨r, hr, heq⟩ := ha
  exact ⟨r, (CommonNoiseFiltration.filtration J).mono hst r hr, heq⟩

theorem completedAt_le_completedSpace (J : Type*) (t : ℝ) :
    completedAt J t ≤ completedSpace J := by
  intro s hs
  obtain ⟨r, hr, heq⟩ := hs
  exact ⟨r, (CommonNoiseFiltration.filtration J).le t r hr, heq⟩

/-- The completed noise filtration at finite real times. -/
def completedFiltration (J : Type*) : Filtration ℝ (completedSpace J) where
  seq := completedAt J
  mono' := completedAt_mono J
  le' := completedAt_le_completedSpace J

/-- All nonnegative finite-time noise histories together. -/
def terminalHistory (J : Type*) : MeasurableSpace (MarkedNoise.Sample J) :=
  ⨆ t : ℝ≥0, completedAt J (t : ℝ)

theorem terminalHistory_le_completedSpace (J : Type*) :
    terminalHistory J ≤ completedSpace J :=
  iSup_le (fun t => completedAt_le_completedSpace J t)

/-- Extended-time filtration. Infinity contains exactly the sigma algebra
generated by the finite completed histories. -/
def extendedFiltration (J : Type*) : Filtration ℝ≥0∞ (completedSpace J) where
  seq t := if t = ⊤ then terminalHistory J else completedAt J t.toReal
  mono' := by
    intro s t hst
    by_cases ht : t = ⊤
    · simp only [ht, ↓reduceIte]
      split_ifs with hs
      · exact le_rfl
      · exact le_iSup (fun u : ℝ≥0 => completedAt J (u : ℝ))
          (⟨s.toReal, ENNReal.toReal_nonneg⟩ : ℝ≥0)
    · have hs : s ≠ ⊤ := ne_top_of_le_ne_top ht hst
      simp only [ht, hs, ↓reduceIte]
      exact completedAt_mono J (ENNReal.toReal_mono ht hst)
  le' t := by
    split_ifs
    · exact terminalHistory_le_completedSpace J
    · exact completedAt_le_completedSpace J t.toReal

@[simp] theorem extendedFiltration_top (J : Type*) :
    extendedFiltration J ⊤ = terminalHistory J := by simp [extendedFiltration]

theorem extendedFiltration_of_ne_top (J : Type*) {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    extendedFiltration J t = completedAt J t.toReal := by simp [extendedFiltration, ht]

section Exits

variable {E J : Type*} [DecidableEq E] [Fintype J]
  (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)

/-- On the actual good-noise event, exiting by a time is equivalent to being
outside at that time. Both finite attainment and permanent freezing are used. -/
theorem ae_firstExit_le_iff_outside : ∀ᵐ ω ∂MarkedNoise.law J, ∀ C x t, 0 ≤ t →
    (firstExit active jump rate C x ω ≤ ENNReal.ofReal t ↔
      process active jump rate C x ω t ∉ active) := by
  filter_upwards [ae_firstExit_attained active jump rate,
    ae_process_frozen active jump rate] with ω hatt hfrozen
  intro C x t ht
  constructor
  · intro hle
    have hfin : firstExit active jump rate C x ω ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
    have htime : (firstExit active jump rate C x ω).toReal ≤ t := by
      simpa only [ENNReal.toReal_ofReal ht] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rw [hfrozen C x _ t htime (hatt C x hfin)]
    exact hatt C x hfin
  · exact exitTime_le_of_not_mem _ _ ht

variable [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]

/-- The first-exit event differs only by an ambient null set from an event
visible in the actual raw history at that time. -/
theorem measurableSet_firstExit_le (C : ℝ) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    MeasurableSet[completedAt J t]
      {ω | firstExit active jump rate C x ω ≤ ENNReal.ofReal t} := by
  refine ⟨{ω | process active jump rate C x ω t ∉ active}, ?_, ?_⟩
  · exact active.measurableSet.compl.preimage
      (CommonNoiseFiltration.measurable_process_at active jump rate C x t)
  · filter_upwards [ae_firstExit_le_iff_outside active jump rate] with ω hω
    exact propext (hω C x t ht)

/-- The exact first-exit functional, with no modification of bad samples, is a
stopping time in the legitimately completed observation filtration. -/
theorem isStoppingTime_firstExit (C : ℝ) (x : E) :
    IsStoppingTime (extendedFiltration J) (firstExit active jump rate C x) := by
  intro t
  by_cases ht : t = ⊤
  · simp only [ht, le_top, setOf_true]
    exact MeasurableSet.univ
  · rw [extendedFiltration_of_ne_top J ht]
    simpa only [ENNReal.ofReal_toReal ht] using
      (measurableSet_firstExit_le active jump rate C x (t := t.toReal) ENNReal.toReal_nonneg)

/-- First exits are measurable in the completed ambient space. -/
theorem measurable_firstExit (C : ℝ) (x : E) :
    Measurable[completedSpace J] (firstExit active jump rate C x) :=
  ((isStoppingTime_firstExit active jump rate C x).measurable_of_le
    (fun _ => le_top)).mono ((extendedFiltration J).le ⊤) le_rfl

/-- On the original probability space the first exit is almost-everywhere
measurable; no unjustified raw measurability assertion is made. -/
theorem aemeasurable_firstExit (C : ℝ) (x : E) :
    AEMeasurable (firstExit active jump rate C x) (MarkedNoise.law J) :=
  (show NullMeasurable (firstExit active jump rate C x) (MarkedNoise.law J) from
    measurable_firstExit active jump rate C x).aemeasurable

/-- The same stopping theorem permits an initial state known at raw time zero.
An arbitrary independent initial law requires the separate product extension. -/
theorem isStoppingTime_firstExit_random_initial (C : ℝ) (X : MarkedNoise.Sample J → E)
    (hX : Measurable[CommonNoiseFiltration.filtration J 0] X) :
    IsStoppingTime (extendedFiltration J)
      (fun ω => firstExit active jump rate C (X ω) ω) := by
  intro t
  by_cases ht : t = ⊤
  · simp only [ht, le_top, setOf_true]
    exact MeasurableSet.univ
  · rw [extendedFiltration_of_ne_top J ht]
    refine ⟨{ω | process active jump rate C (X ω) ω t.toReal ∉ active}, ?_, ?_⟩
    · exact active.measurableSet.compl.preimage
        (CommonNoiseFiltration.measurable_process_random_initial_at active jump rate
          C X hX t.toReal ENNReal.toReal_nonneg)
    · filter_upwards [ae_firstExit_le_iff_outside active jump rate] with ω hω
      exact propext (by simpa only [ENNReal.ofReal_toReal ht] using
        (hω C (X ω) t.toReal ENNReal.toReal_nonneg))

end Exits

end CarryingCapacity.CommonFrozenStopping
