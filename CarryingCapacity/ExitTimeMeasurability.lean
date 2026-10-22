import CarryingCapacity.PredictableExitMask

/-!
# Measurability and attainment of genuine first exits

The infimum over rational nonnegative observations is measurable. Actual
right-local constancy identifies it with the first exit over all real times,
including an initial exit at zero and an infinite non-crossing time. Thus
almost-sure path regularity gives almost-everywhere measurability of the exact
exit, without claiming raw measurability on exceptional samples.

Finite exits are attained using regularity only at nonnegative times. No
permanent freezing, monotonicity, or stopping-time assumption is used.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical ENNReal

namespace CarryingCapacity.ExitTimeMeasurability
open CommonFrozenExit PredictableExitMask

variable {Ω E : Type*}

/-- A measurable rational-observation version of the actual first exit. -/
def rationalExit (X : ℝ → Ω → E) (G : Set E) (ω : Ω) : ℝ≥0∞ :=
  ⨅ q : ℚ, if 0 ≤ (q : ℝ) ∧ X q ω ∉ G then ENNReal.ofReal q else ⊤

/-- The rational infimum has exactly the rational strict-past survival sets. -/
theorem le_rationalExit_iff (X : ℝ → Ω → E) (G : Set E) (ω : Ω) (t : ℝ) :
    ENNReal.ofReal t ≤ rationalExit X G ω ↔
      ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) < t → X q ω ∈ G := by
  rw [rationalExit, le_iInf_iff]
  constructor
  · intro h q hq hqt
    by_contra hout
    have hi := h q
    rw [if_pos ⟨hq, hout⟩] at hi
    exact not_le_of_gt hqt ((ENNReal.ofReal_le_ofReal_iff hq).mp hi)
  · intro h q
    split_ifs with hq
    · apply ENNReal.ofReal_le_ofReal
      exact le_of_not_gt (fun hqt => hq.2 (h q hq.1 hqt))
    · exact le_top

/-- Rational and real first exits coincide pathwise under actual right-local
constancy; this includes the zero and infinity cases. -/
theorem rationalExit_eq_exitTime (X : ℝ → Ω → E) (G : Set E) (ω : Ω)
    (hright : ∀ s : ℝ, 0 ≤ s → ∃ b, s < b ∧ ∀ u ∈ Ico s b, X u ω = X s ω) :
    rationalExit X G ω = exitTime G (fun s => X s ω) := by
  apply ENNReal.eq_of_forall_nnreal_iff
  intro r
  rw [← ENNReal.ofReal_coe_nnreal]
  rw [le_rationalExit_iff, le_exitTime_iff_before_mem]
  exact rational_before_iff_before G (fun s => X s ω) hright r

/-- Finite attainment requires local constancy only on the time domain of
the exit, not at negative times. -/
theorem exitTime_attained (G : Set E) (f : ℝ → E)
    (hright : ∀ s : ℝ, 0 ≤ s → ∃ b, s < b ∧ ∀ u ∈ Ico s b, f u = f s)
    (hfin : exitTime G f ≠ ⊤) : f (exitTime G f).toReal ∉ G := by
  have hne : (exitSet G f).Nonempty := by
    by_contra h
    exact hfin ((exitTime_eq_top_iff G f).mpr h)
  rw [exitTime_toReal G f hne]
  intro hin
  obtain ⟨b, hb, hconst⟩ := hright (sInf (exitSet G f)) (exitSet_inf_nonneg G f hne)
  obtain ⟨u, hu, hub⟩ := exists_lt_of_csInf_lt hne hb
  have hlu := csInf_le (exitSet_bddBelow G f) hu
  exact hu.2 ((hconst u ⟨hlu, hub⟩).symm ▸ hin)

/-- A genuine exit by a finite horizon is equivalent to an actual crossing
in that closed horizon, retaining both the initial and terminal time. -/
theorem exitTime_le_iff_exists (G : Set E) (f : ℝ → E)
    (hright : ∀ s : ℝ, 0 ≤ s → ∃ b, s < b ∧ ∀ u ∈ Ico s b, f u = f s)
    (T : ℝ) (hT : 0 ≤ T) :
    exitTime G f ≤ ENNReal.ofReal T ↔ ∃ t ∈ Icc 0 T, f t ∉ G := by
  constructor
  · intro h
    have hfin : exitTime G f ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
    refine ⟨(exitTime G f).toReal, ⟨ENNReal.toReal_nonneg, ?_⟩,
      exitTime_attained G f hright hfin⟩
    simpa only [ENNReal.toReal_ofReal hT] using ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  · rintro ⟨t, ht, hout⟩
    exact (exitTime_le_of_not_mem G f ht.1 hout).trans (ENNReal.ofReal_le_ofReal ht.2)

section Measurability
variable [MeasurableSpace Ω] [MeasurableSpace E]
  (X : ℝ → Ω → E) (hX : ∀ s : ℝ, 0 ≤ s → Measurable (X s))
  (G : Set E) (hG : MeasurableSet G)

include hX hG in
/-- Coordinate measurability at nonnegative times suffices for a measurable
rational exit version; no sample-path regularity is used here. -/
theorem measurable_rationalExit : Measurable (rationalExit X G) := by
  apply Measurable.iInf
  intro q
  by_cases hq : 0 ≤ (q : ℝ)
  · simp only [hq, true_and]
    exact measurable_const.ite ((hG.preimage (hX q hq)).compl) measurable_const
  · simp only [hq, false_and, if_false]
    exact measurable_const

variable (μ : Measure Ω)
  (hright : ∀ᵐ ω ∂μ, ∀ s : ℝ, 0 ≤ s →
    ∃ b, s < b ∧ ∀ u ∈ Ico s b, X u ω = X s ω)
include hright

omit [MeasurableSpace E] in
/-- One probability-one regularity event identifies both exit definitions. -/
theorem ae_rationalExit_eq_exitTime :
    rationalExit X G =ᵐ[μ] fun ω => exitTime G (fun s => X s ω) := by
  filter_upwards [hright] with ω hω
  exact rationalExit_eq_exitTime X G ω hω

include hX hG in
/-- The exact real-time exit is AE measurable in the original measure space.
The definition itself is retained even on exceptional paths. -/
theorem aemeasurable_exitTime :
    AEMeasurable (fun ω => exitTime G (fun s => X s ω)) μ :=
  (measurable_rationalExit X hX G hG).aemeasurable.congr
    (ae_rationalExit_eq_exitTime X G μ hright)

omit [MeasurableSpace E] in
/-- Finite attainment is simultaneous for every sample on one regularity event. -/
theorem ae_exitTime_attained : ∀ᵐ ω ∂μ,
    exitTime G (fun s => X s ω) ≠ ⊤ →
      X (exitTime G (fun s => X s ω)).toReal ω ∉ G := by
  filter_upwards [hright] with ω hω
  exact exitTime_attained G (fun s => X s ω) hω

omit [MeasurableSpace E] in
/-- The crossing-event equivalence holds for all finite nonnegative horizons
on one event, rather than choosing a null set at each random horizon. -/
theorem ae_exitTime_le_iff_exists : ∀ᵐ ω ∂μ, ∀ T : ℝ, 0 ≤ T →
    (exitTime G (fun s => X s ω) ≤ ENNReal.ofReal T ↔
      ∃ t ∈ Icc 0 T, X t ω ∉ G) := by
  filter_upwards [hright] with ω hω
  exact fun T hT => exitTime_le_iff_exists G (fun s => X s ω) hω T hT

end Measurability
end CarryingCapacity.ExitTimeMeasurability
