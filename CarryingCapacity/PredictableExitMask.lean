import CarryingCapacity.PredictableStepApproximation
import CarryingCapacity.CommonFrozenExit
import CarryingCapacity.InitialPredictableCompensation

/-!
# Predictable masks retaining a genuine first-exit jump

Survival through a positive time is first defined using only strictly earlier
nonnegative rational observations. The resulting set is raw predictable by a
countable union of past-event rectangles. For a path locally constant to the
right, rational survival is exactly survival up to and including its genuine
first exit. This covers an initial state outside the set and a path that never
exits. Nonnegative compensation transfers from the raw predictable version to
the inclusive genuine-exit mask on a single probability-one sample event.

No raw stopping-time claim is made about exceptional paths, and no completed
predictable compensation theorem is used.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical ENNReal

namespace CarryingCapacity.PredictableExitMask
open PredictableSets CommonFrozenExit

section Deterministic
variable {E : Type*}

/-- Survival at every strictly earlier real time is equivalent to the
inclusive comparison with the genuine exit infimum. Attainment is unnecessary. -/
theorem le_exitTime_iff_before_mem (active : Set E) (f : ℝ → E)
    (t : ℝ) :
    ENNReal.ofReal t ≤ exitTime active f ↔
      ∀ s : ℝ, 0 ≤ s → s < t → f s ∈ active := by
  constructor
  · intro h s hs hst
    exact mem_before_exit active f hs
      (((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs).mpr hst).trans_le h)
  · intro h
    by_cases he : (exitSet active f).Nonempty
    · rw [exitTime, if_pos he]
      apply ENNReal.ofReal_le_ofReal
      apply le_csInf he
      intro s hs
      by_contra hts
      exact hs.2 (h s hs.1 (lt_of_not_ge hts))
    · simp only [exitTime, if_neg he, le_top]

/-- Right-local constancy turns the rational strict-past observations into
the whole real strict-past history, without assuming monotone costs or permanent freezing. -/
theorem rational_before_iff_before (active : Set E) (f : ℝ → E)
    (hright : ∀ s : ℝ, 0 ≤ s → ∃ b, s < b ∧ ∀ u ∈ Ico s b, f u = f s)
    (t : ℝ) :
    (∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) < t → f q ∈ active) ↔
      ∀ s : ℝ, 0 ≤ s → s < t → f s ∈ active := by
  constructor
  · intro h s hs hst
    obtain ⟨b, hb, hconst⟩ := hright s hs
    obtain ⟨q, hsq, hq⟩ := exists_rat_btwn (lt_min hb hst)
    have hi := h q (hs.trans hsq.le) (lt_min_iff.mp hq).2
    rw [hconst q ⟨hsq.le, (lt_min_iff.mp hq).1⟩] at hi
    exact hi
  · intro h q hq hqt
    exact h q hq hqt

end Deterministic

variable {Ω E : Type*}

/-- Positive-time survival using only strictly earlier rational observations.
In particular, the time of the first exit itself is included. -/
def survivalSet (X : ℝ → Ω → E) (active : Set E) : Set (Ω × (ℝ × ℝ)) :=
  {p | 0 < p.2.1 ∧ ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) < p.2.1 → X q p.1 ∈ active}

/-- The mask of a field by its raw rational-history survival version. -/
def rationalMask {V : Type*} [Zero V] (X : ℝ → Ω → E) (active : Set E)
    (f : Ω × (ℝ × ℝ) → V) : Ω × (ℝ × ℝ) → V :=
  (survivalSet X active).indicator f

/-- The mask at the genuine real-time first exit, retaining the exit jump. -/
def exitMask {V : Type*} [Zero V] (X : ℝ → Ω → E) (active : Set E)
    (f : Ω × (ℝ × ℝ) → V) (p : Ω × (ℝ × ℝ)) : V :=
  if 0 < p.2.1 ∧ ENNReal.ofReal p.2.1 ≤ exitTime active (fun s => X s p.1) then f p else 0

section Measurability
variable [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
  (F : Filtration ℝ mΩ) (X : ℝ → Ω → E)
  (hX : ∀ s, 0 ≤ s → Measurable[F s] (X s))
  (active : Set E) (hactive : MeasurableSet active)
include hX hactive

/-- Predictability is proved directly from the generating rectangles of the
raw filtration, with no stopping-time or regularity assumption. -/
theorem measurableSet_survivalSet : MeasurableSet[predictable F] (survivalSet X active) := by
  classical
  let bad : Set (Ω × (ℝ × ℝ)) :=
    ⋃ q : ℚ, ⋃ (_ : 0 ≤ (q : ℝ)), ⋃ n : ℕ,
      rectangle ((X q) ⁻¹' activeᶜ) q n univ
  have hbad : MeasurableSet[predictable F] bad := by
    apply MeasurableSet.iUnion
    intro q
    apply MeasurableSet.iUnion
    intro hq
    exact MeasurableSet.iUnion (fun n => measurableSet_predictable_rectangle
      F q n hq _ (hactive.compl.preimage (hX q hq)) univ MeasurableSet.univ)
  have he : survivalSet X active = {p : Ω × (ℝ × ℝ) | 0 < p.2.1} ∩ badᶜ := by
    ext p
    simp only [survivalSet, mem_setOf_eq, mem_inter_iff, mem_compl_iff, bad,
      mem_iUnion, rectangle, mem_prod, mem_preimage, mem_univ, and_true, mem_Ioc]
    constructor
    · rintro ⟨ht, h⟩
      refine ⟨ht, ?_⟩
      rintro ⟨q, hq, n, hout, hqt, _⟩
      exact hout (h q hq hqt)
    · rintro ⟨ht, h⟩
      refine ⟨ht, ?_⟩
      intro q hq hqt
      by_contra hout
      obtain ⟨n, hn⟩ := exists_nat_ge p.2.1
      exact h ⟨q, hq, n, hout, hqt, hn⟩
  rw [he]
  exact (PredictableStepApproximation.measurableSet_positive F).inter hbad.compl

/-- Masking a predictable field by strictly past survival remains predictable. -/
theorem measurable_rationalMask {V : Type*} [Zero V] [MeasurableSpace V]
    (f : Ω × (ℝ × ℝ) → V) (hf : Measurable[predictable F] f) :
    Measurable[predictable F] (rationalMask X active f) :=
  hf.indicator (measurableSet_survivalSet F X hX active hactive)

end Measurability

/-- On every right-locally-constant sample path the raw predictable mask is
exactly the true inclusive exit mask, simultaneously for all times and marks. -/
theorem rationalMask_eq_exitMask {V : Type*} [Zero V]
    (X : ℝ → Ω → E) (active : Set E) (f : Ω × (ℝ × ℝ) → V) (ω : Ω)
    (hright : ∀ s : ℝ, 0 ≤ s → ∃ b, s < b ∧ ∀ u ∈ Ico s b, X u ω = X s ω)
    (z : ℝ × ℝ) : rationalMask X active f (ω,z) = exitMask X active f (ω,z) := by
  have he : (ω,z) ∈ survivalSet X active ↔
      0 < z.1 ∧ ENNReal.ofReal z.1 ≤ exitTime active (fun s => X s ω) := by
    change (0 < z.1 ∧ _) ↔ _
    by_cases hz : 0 < z.1
    · simp only [hz, true_and]
      exact (rational_before_iff_before active (fun s => X s ω) hright z.1).trans
        (le_exitTime_iff_before_mem active (fun s => X s ω) z.1).symm
    · simp only [hz, false_and]
  simp only [rationalMask, Set.indicator, exitMask, he]

/-- A single pathwise regularity event identifies both fields at all points;
no exceptional set is chosen separately at a random exit or event time. -/
theorem ae_rationalMask_eq_exitMask [MeasurableSpace Ω] (μ : Measure Ω)
    {V : Type*} [Zero V] (X : ℝ → Ω → E) (active : Set E) (f : Ω × (ℝ × ℝ) → V)
    (hright : ∀ᵐ ω ∂μ, ∀ s : ℝ, 0 ≤ s → ∃ b, s < b ∧ ∀ u ∈ Ico s b, X u ω = X s ω) :
    ∀ᵐ ω ∂μ, ∀ z : ℝ × ℝ, rationalMask X active f (ω,z) = exitMask X active f (ω,z) :=
  hright.mono (fun ω hω z => rationalMask_eq_exitMask X active f ω hω z)

section InitialNoise
open CommonInitialNoise MarkedIntensity
variable {A J : Type*} [MeasurableSpace A] [MeasurableSpace E]
  (μ : Measure A) [IsProbabilityMeasure μ]
  (X : ℝ → Sample A J → E)
  (hX : ∀ s, 0 ≤ s → Measurable[filtration A J s] (X s))
  (active : Set E) (hactive : MeasurableSet active)
  (hright : ∀ᵐ p ∂law μ J, ∀ s : ℝ, 0 ≤ s → ∃ b, s < b ∧ ∀ u ∈ Ico s b, X u p = X s p)
  (f : Sample A J × (ℝ × ℝ) → ℝ≥0∞)
  (hf : Measurable[predictable (filtration A J)] f)
include hX hactive hright hf

omit [IsProbabilityMeasure μ] in
/-- The actual inclusive stopped counting integral has an AE measurable
version, derived from the raw predictable rational-history field. -/
theorem aemeasurable_exitCountingIntegral (j : J) :
    AEMeasurable (fun p => ∫⁻ z, exitMask X active f (p,z) ∂MarkedNoise.countingMeasure j p.2)
      (law μ J) := by
  have hm := InitialPredictableCompensation.measurable_countingIntegral j (rationalMask X active f)
    ((measurable_rationalMask (filtration A J) X hX active hactive f hf).mono (predictable_le _) le_rfl)
  apply hm.aemeasurable.congr
  filter_upwards [ae_rationalMask_eq_exitMask (law μ J) X active f hright] with p hp
  exact lintegral_congr hp

/-- Nonnegative compensation up to and including the true first-exit jump.
Predictability is derived from raw strict-past observations and actual path
regularity; no integrability or finite expectation is assumed. -/
theorem compensation_exitMask_nonnegative (j : J) :
    (∫⁻ p, ∫⁻ z, exitMask X active f (p,z) ∂MarkedNoise.countingMeasure j p.2 ∂law μ J) =
      ∫⁻ p, ∫⁻ z, exitMask X active f (p,z) ∂positiveVolume.prod positiveVolume ∂law μ J := by
  have he := ae_rationalMask_eq_exitMask (law μ J) X active f hright
  calc
    _ = ∫⁻ p, ∫⁻ z, rationalMask X active f (p,z)
        ∂MarkedNoise.countingMeasure j p.2 ∂law μ J := by
      apply lintegral_congr_ae
      filter_upwards [he] with p hp
      exact lintegral_congr (fun z => (hp z).symm)
    _ = ∫⁻ p, ∫⁻ z, rationalMask X active f (p,z)
        ∂positiveVolume.prod positiveVolume ∂law μ J :=
      InitialPredictableCompensation.compensation_nonnegative μ j _
        (measurable_rationalMask (filtration A J) X hX active hactive f hf)
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [he] with p hp
      exact lintegral_congr hp

end InitialNoise
end CarryingCapacity.PredictableExitMask
