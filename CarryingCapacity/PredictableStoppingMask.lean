import CarryingCapacity.PredictableStepApproximation
import CarryingCapacity.InitialPredictableCompensation

/-!
# Predictable masks for arbitrary common stopping times

The set `0 < t ≤ τ` is predictable. Its complement at positive times is a
countable union of past-event rectangles, using the stopping events `τ ≤ q`
at nonnegative rational times. In particular this mask retains a possible
jump at the stopping time, including when the stopping time is zero or
infinite. No first-exit representation or path regularity is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical ENNReal

namespace CarryingCapacity.PredictableStoppingMask
open PredictableSets

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The positive-time predictable interval ending at and including `τ`. -/
def survivalSet (τ : Ω → ℝ≥0∞) : Set (Ω × (ℝ × ℝ)) :=
  {p | 0 < p.2.1 ∧ ENNReal.ofReal p.2.1 ≤ τ p.1}

/-- Stop a field inclusively, so its value at an exit jump is retained. -/
def mask {V : Type*} [Zero V] (τ : Ω → ℝ≥0∞)
    (f : Ω × (ℝ × ℝ) → V) : Ω × (ℝ × ℝ) → V :=
  (survivalSet τ).indicator f

omit mΩ in
theorem mask_apply {V : Type*} [Zero V] (τ : Ω → ℝ≥0∞)
    (f : Ω × (ℝ × ℝ) → V) (p : Ω × (ℝ × ℝ)) :
    mask τ f p = if 0 < p.2.1 ∧ ENNReal.ofReal p.2.1 ≤ τ p.1 then f p else 0 := by
  classical
  by_cases h : 0 < p.2.1 ∧ ENNReal.ofReal p.2.1 ≤ τ p.1
  · simp [mask, survivalSet, h]
  · simp [mask, survivalSet, h]

/-- The usual stopping-time sublevel condition suffices. The filtration may
be completed or right continuous, but neither property is needed here. -/
theorem measurableSet_survivalSet (F : Filtration ℝ mΩ) (τ : Ω → ℝ≥0∞)
    (hτ : ∀ s : ℝ, 0 ≤ s → MeasurableSet[F s] {ω | τ ω ≤ ENNReal.ofReal s}) :
    MeasurableSet[predictable F] (survivalSet τ) := by
  let bad : Set (Ω × (ℝ × ℝ)) :=
    ⋃ q : ℚ, ⋃ (_ : 0 ≤ (q : ℝ)), ⋃ n : ℕ,
      rectangle {ω | τ ω ≤ ENNReal.ofReal q} q n univ
  have hbad : MeasurableSet[predictable F] bad := by
    apply MeasurableSet.iUnion
    intro q
    apply MeasurableSet.iUnion
    intro hq
    exact MeasurableSet.iUnion (fun n => measurableSet_predictable_rectangle
      F q n hq _ (hτ q hq) univ MeasurableSet.univ)
  have he : survivalSet τ = {p : Ω × (ℝ × ℝ) | 0 < p.2.1} ∩ badᶜ := by
    ext p
    simp only [survivalSet, mem_setOf_eq, mem_inter_iff, mem_compl_iff, bad,
      mem_iUnion, rectangle, mem_prod, mem_univ, and_true, mem_Ioc]
    constructor
    · rintro ⟨ht, hle⟩
      refine ⟨ht, ?_⟩
      rintro ⟨q, hq, n, hτq, hqt, _⟩
      exact (not_lt_of_ge (hle.trans hτq))
        ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hq).mpr hqt)
    · rintro ⟨ht, hbad⟩
      refine ⟨ht, ?_⟩
      by_contra hnle
      have hlt : τ p.1 < ENNReal.ofReal p.2.1 := lt_of_not_ge hnle
      have htop : τ p.1 ≠ ⊤ := ne_top_of_lt hlt
      have hreal : (τ p.1).toReal < p.2.1 := by
        simpa only [ENNReal.toReal_ofReal ht.le] using
          (ENNReal.toReal_lt_toReal htop ENNReal.ofReal_ne_top).mpr hlt
      obtain ⟨q, hτq, hqt⟩ := exists_rat_btwn hreal
      obtain ⟨n, hn⟩ := exists_nat_ge p.2.1
      have hq : 0 ≤ (q : ℝ) := ENNReal.toReal_nonneg.trans hτq.le
      have hτq' : τ p.1 ≤ ENNReal.ofReal q := by
        simpa only [ENNReal.ofReal_toReal htop] using ENNReal.ofReal_le_ofReal hτq.le
      exact hbad ⟨q, hq, n, hτq', hqt, hn⟩
  rw [he]
  exact (PredictableStepApproximation.measurableSet_positive F).inter hbad.compl

theorem measurable_mask (F : Filtration ℝ mΩ) (τ : Ω → ℝ≥0∞)
    (hτ : ∀ s : ℝ, 0 ≤ s → MeasurableSet[F s] {ω | τ ω ≤ ENNReal.ofReal s})
    {V : Type*} [Zero V] [MeasurableSpace V]
    (f : Ω × (ℝ × ℝ) → V) (hf : Measurable[predictable F] f) :
    Measurable[predictable F] (mask τ f) :=
  hf.indicator (measurableSet_survivalSet F τ hτ)

/-- An ordinary extended-time stopping time supplies exactly the sublevel
condition used by the predictable mask. -/
theorem measurable_mask_of_isStoppingTime
    (F : Filtration ℝ mΩ) (G : Filtration ℝ≥0∞ mΩ) (τ : Ω → ℝ≥0∞)
    (hτ : IsStoppingTime G τ)
    (hFG : ∀ s : ℝ, 0 ≤ s → G (ENNReal.ofReal s) ≤ F s)
    {V : Type*} [Zero V] [MeasurableSpace V]
    (f : Ω × (ℝ × ℝ) → V) (hf : Measurable[predictable F] f) :
    Measurable[predictable F] (mask τ f) :=
  measurable_mask F τ (fun s hs => hFG s hs _ (hτ (ENNReal.ofReal s))) f hf

section CanonicalCompensation
open CommonInitialNoise MarkedIntensity
variable {A J : Type*} [MeasurableSpace A]

/-- The existing actual Poisson compensation theorem applies to an arbitrary
raw-history stopping time. Its endpoint is retained and no integrability or
finite-expectation premise is required. -/
theorem compensation_nonnegative (μ : Measure A) [IsProbabilityMeasure μ]
    (τ : Sample A J → ℝ≥0∞)
    (hτ : ∀ s : ℝ, 0 ≤ s →
      MeasurableSet[filtration A J s] {p | τ p ≤ ENNReal.ofReal s})
    (j : J) (f : Sample A J × (ℝ × ℝ) → ℝ≥0∞)
    (hf : Measurable[predictable (filtration A J)] f) :
    (∫⁻ p, ∫⁻ z, mask τ f (p,z) ∂MarkedNoise.countingMeasure j p.2 ∂law μ J) =
      ∫⁻ p, ∫⁻ z, mask τ f (p,z) ∂positiveVolume.prod positiveVolume ∂law μ J :=
  InitialPredictableCompensation.compensation_nonnegative μ j _
    (measurable_mask (filtration A J) τ hτ f hf)

end CanonicalCompensation
end CarryingCapacity.PredictableStoppingMask
