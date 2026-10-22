import CarryingCapacity.CommonInitialStopping

/-!
# The completed right-continuous augmentation

The augmentation is constructed from the given raw filtration and the given
measure. It contains all ambient null sets at every time and is the smallest
right-continuous filtration with those properties. Adapted processes and
stopping times retain their properties. This does not identify labelled noise
histories with histories generated solely by the random counting measures.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal

namespace CarryingCapacity.UsualFiltration

variable {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)

/-- The original sample space completed using its own null sets. -/
def completedSpace : MeasurableSpace Ω := EventuallyMeasurableSpace m (ae P)

/-- The same measure on the completed ambient sigma algebra. -/
def completedLaw : @Measure Ω (completedSpace P) := P.completion

@[simp] theorem completedLaw_apply (s : Set Ω) : completedLaw P s = P s := rfl

@[simp] theorem ae_completedLaw : ae (completedLaw P) = ae P := rfl

instance completedLaw_probability [IsProbabilityMeasure P] :
    IsProbabilityMeasure (completedLaw P) :=
  ⟨by change P univ = 1; exact measure_univ⟩

instance completedLaw_complete : (completedLaw P).IsComplete :=
  inferInstanceAs P.completion.IsComplete

variable (F : Filtration ℝ m)

/-- Add precisely the ambient null sets to the given past. -/
def completedAt (t : ℝ) : MeasurableSpace Ω := EventuallyMeasurableSpace (F t) (ae P)

theorem raw_le_completedAt (t : ℝ) : F t ≤ completedAt P F t :=
  EventuallyMeasurableSpace.measurable_le

theorem completedAt_mono : Monotone (completedAt P F) := by
  intro s t hst a ha
  obtain ⟨b, hb, heq⟩ := ha
  exact ⟨b, F.mono hst b hb, heq⟩

theorem completedAt_le_completedSpace (t : ℝ) : completedAt P F t ≤ completedSpace P := by
  intro a ha
  obtain ⟨b, hb, heq⟩ := ha
  exact ⟨b, F.le t b hb, heq⟩

theorem measurableSet_completedAt_of_null (t : ℝ) {s : Set Ω} (hs : P s = 0) :
    MeasurableSet[completedAt P F t] s :=
  ⟨∅, @MeasurableSet.empty Ω (F t), ae_eq_empty.mpr hs⟩

/-- Minimality of completion, with no additional future information. -/
theorem completedAt_le (t : ℝ) (n : MeasurableSpace Ω) (hraw : F t ≤ n)
    (hnull : ∀ s, P s = 0 → MeasurableSet[n] s) : @completedAt Ω m P F t ≤ n := by
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

/-- Intersect the completed histories strictly after the selected time. -/
def usualAt (t : ℝ) : MeasurableSpace Ω := ⨅ u : {u : ℝ // t < u}, completedAt P F u.1

theorem completedAt_le_usualAt (t : ℝ) : completedAt P F t ≤ usualAt P F t :=
  le_iInf (fun u => completedAt_mono P F u.2.le)

theorem raw_le_usualAt (t : ℝ) : F t ≤ usualAt P F t :=
  (raw_le_completedAt P F t).trans (completedAt_le_usualAt P F t)

theorem at_le_completedAt {t u : ℝ} (htu : t < u) : usualAt P F t ≤ completedAt P F u :=
  iInf_le (fun v : {v : ℝ // t < v} => completedAt P F v.1) ⟨u, htu⟩

theorem at_mono : Monotone (usualAt P F) := by
  intro s t hst
  apply le_iInf
  intro u
  exact at_le_completedAt P F (lt_of_le_of_lt hst u.2)

theorem at_le_completedSpace (t : ℝ) : usualAt P F t ≤ completedSpace P :=
  (at_le_completedAt P F (show t < t + 1 by linarith)).trans
    (completedAt_le_completedSpace P F (t + 1))

/-- The completed right-continuous filtration of the prescribed raw history. -/
def filtration : Filtration ℝ (completedSpace P) where
  seq := usualAt P F
  mono' := at_mono P F
  le' := at_le_completedSpace P F

/-- Right continuity is equality with the intersection of all strict future histories. -/
def IsRightContinuous {n : MeasurableSpace Ω} (G : Filtration ℝ n) : Prop :=
  ∀ t, G t = ⨅ u : {u : ℝ // t < u}, G u.1

theorem rightContinuous : IsRightContinuous (filtration P F) := by
  intro t
  apply le_antisymm
  · exact le_iInf (fun u => at_mono P F u.2.le)
  · apply le_iInf
    intro v
    obtain ⟨u, htu, huv⟩ := exists_between v.2
    exact (iInf_le (fun w : {w : ℝ // t < w} => usualAt P F w.1) ⟨u, htu⟩).trans
      (at_le_completedAt P F huv)

theorem measurableSet_at_iff (t : ℝ) (s : Set Ω) :
    MeasurableSet[usualAt P F t] s ↔ ∀ u > t, MeasurableSet[completedAt P F u] s := by
  simp only [usualAt, MeasurableSpace.measurableSet_iInf, Subtype.forall]

/-- Every subset of an ambient null event is present at every time. -/
theorem measurableSet_at_of_null (t : ℝ) {s : Set Ω} (hs : P s = 0) :
    MeasurableSet[usualAt P F t] s :=
  completedAt_le_usualAt P F t s (measurableSet_completedAt_of_null P F t hs)

/-- Each past sigma algebra is complete for the actual restricted law. -/
instance trimmed_complete (t : ℝ) :
    ((completedLaw P).trim ((filtration P F).le t)).IsComplete := by
  refine ⟨fun s hs => ?_⟩
  apply measurableSet_at_of_null P F t
  exact le_antisymm ((le_trim ((filtration P F).le t)).trans hs.le) (zero_le _)

/-- Any right-continuous, null-complete enlargement of the raw history contains
this construction. The augmentation does not select an arbitrary larger filtration. -/
theorem minimal (G : Filtration ℝ (completedSpace P))
    (hraw : ∀ t, F t ≤ G t)
    (hnull : ∀ t s, P s = 0 → MeasurableSet[G t] s)
    (hright : IsRightContinuous G) : filtration P F ≤ G := by
  intro t
  rw [hright t]
  apply le_iInf
  intro u
  exact (at_le_completedAt P F u.2).trans
    (completedAt_le P F u.1 (G u.1) (hraw u.1) (hnull u.1))

/-- Raw measurable observations are still measurable in the usual past. -/
theorem measurable_at {E : Type*} [MeasurableSpace E] {X : Ω → E} (t : ℝ)
    (hX : Measurable[F t] X) : Measurable[filtration P F t] X :=
  hX.mono (raw_le_usualAt P F t) le_rfl

/-- No modification of an already adapted process is needed. -/
theorem adapted {E : Type*} [TopologicalSpace E] {X : ℝ → Ω → E}
    (hX : Adapted F X) : Adapted (filtration P F) X :=
  fun t => (hX t).mono (raw_le_usualAt P F t)

/-- Exact stopping times remain stopping times after the usual augmentation. -/
theorem isStoppingTime {τ : Ω → ℝ} (hτ : IsStoppingTime F τ) :
    IsStoppingTime (filtration P F) τ :=
  fun t => raw_le_usualAt P F t _ (hτ t)

/-- The terminal history contains all finite nonnegative usual histories. -/
def terminalHistory : MeasurableSpace Ω := ⨆ t : ℝ≥0, usualAt P F (t : ℝ)

theorem terminalHistory_le_completedSpace : terminalHistory P F ≤ completedSpace P :=
  iSup_le (fun t => at_le_completedSpace P F t)

/-- Add an infinite time for genuine possibly infinite exit times. At infinity
use the sigma algebra generated by finite histories. -/
def extendedFiltration : Filtration ℝ≥0∞ (completedSpace P) where
  seq t := if t = ⊤ then terminalHistory P F else usualAt P F t.toReal
  mono' := by
    intro s t hst
    by_cases ht : t = ⊤
    · simp only [ht, ↓reduceIte]
      split_ifs with hs
      · exact le_rfl
      · exact le_iSup (fun u : ℝ≥0 => usualAt P F (u : ℝ))
          (⟨s.toReal, ENNReal.toReal_nonneg⟩ : ℝ≥0)
    · have hs : s ≠ ⊤ := ne_top_of_le_ne_top ht hst
      simp only [ht, hs, ↓reduceIte]
      exact at_mono P F (ENNReal.toReal_mono ht hst)
  le' t := by
    split_ifs
    · exact terminalHistory_le_completedSpace P F
    · exact at_le_completedSpace P F t.toReal

@[simp] theorem extendedFiltration_top :
    extendedFiltration P F ⊤ = terminalHistory P F := by simp [extendedFiltration]

theorem extendedFiltration_of_ne_top {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    extendedFiltration P F t = usualAt P F t.toReal := by simp [extendedFiltration, ht]

/-- Completed finite-time sublevels suffice for the exact extended stopping time. -/
theorem isStoppingTime_extended {τ : Ω → ℝ≥0∞}
    (hτ : ∀ t, 0 ≤ t → MeasurableSet[completedAt P F t] {ω | τ ω ≤ ENNReal.ofReal t}) :
    IsStoppingTime (extendedFiltration P F) τ := by
  intro t
  by_cases ht : t = ⊤
  · simp only [ht, le_top, setOf_true]
    exact MeasurableSet.univ
  · rw [extendedFiltration_of_ne_top P F ht]
    apply completedAt_le_usualAt P F t.toReal
    simpa only [ENNReal.ofReal_toReal ht] using hτ t.toReal ENNReal.toReal_nonneg

end CarryingCapacity.UsualFiltration
