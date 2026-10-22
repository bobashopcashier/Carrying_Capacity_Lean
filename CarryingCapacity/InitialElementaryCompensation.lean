import CarryingCapacity.InitialMarkedPastIndependence
import CarryingCapacity.MarkedIntensity
import Mathlib.Probability.Integration

/-!
# Elementary marked compensation with an arbitrary initial law

Coefficients may depend on the whole initial record and the arrived marked
history. Both raw and null-augmented histories satisfy the compensation
identity for the actual counting measure. Nonnegative coefficients may have
infinite expectation; no compensation formula is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CarryingCapacity.InitialElementaryCompensation
open CommonInitialNoise MarkedIntensity InitialMarkedPastIndependence

variable {A J : Type*} [MeasurableSpace A]

/-- A measurable nonnegative integrand has the same integral under completion. -/
theorem completion_lintegral_eq {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ν : Measure Ω) (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f ω ∂ν.completion) = ∫⁻ ω, f ω ∂ν := by
  have hle : mΩ ≤ EventuallyMeasurableSpace mΩ (MeasureTheory.ae ν) :=
    EventuallyMeasurableSpace.measurable_le
  have htrim : ν.completion.trim hle = ν := by
    apply @Measure.ext Ω mΩ
    intro S hS
    rw [trim_measurableSet_eq hle hS]
    rfl
  have h := lintegral_trim (μ := ν.completion) hle hf
  rw [htrim] at h
  exact h.symm

/-- The entire deterministic intensity lifts through the exact noise marginal. -/
theorem lintegral_counting_set (μ : Measure A) [IsProbabilityMeasure μ]
    (j : J) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) :
    (∫⁻ p : Sample A J, MarkedNoise.countingMeasure j p.2 S ∂law μ J) =
      (positiveVolume.prod positiveVolume) S := by
  have hm : Measurable (fun ω : MarkedNoise.Sample J => MarkedNoise.countingMeasure j ω S) :=
    (Measure.measurable_coe hS).comp (MarkedNoise.measurable_countingMeasure j)
  rw [← lintegral_map hm measurable_snd, map_noise]
  exact MarkedIntensity.lintegral_counting_set j S hS

/-- Completion leaves the genuine counting-measure intensity unchanged. -/
theorem lintegral_counting_set_completed (μ : Measure A) [IsProbabilityMeasure μ]
    (j : J) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) :
    (∫⁻ p : Sample A J, MarkedNoise.countingMeasure j p.2 S
      ∂CommonInitialStopping.completedLaw μ J) =
      (positiveVolume.prod positiveVolume) S := by
  exact (completion_lintegral_eq (law μ J)
    (fun p : Sample A J => MarkedNoise.countingMeasure j p.2 S)
    (((Measure.measurable_coe hS).comp
      (MarkedNoise.measurable_countingMeasure j)).comp measurable_snd)).trans
        (lintegral_counting_set μ j S hS)

/-- A coefficient known at the raw initial-plus-noise history factors from
the future marked rectangle through proved independence. -/
theorem lintegral_past_mul_countingMeasure
    (μ : Measure A) [IsProbabilityMeasure μ] (j : J) (m : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (H : Sample A J → ℝ≥0∞) (hH : Measurable[filtration A J s] H) :
    (∫⁻ p, H p * MarkedNoise.countingMeasure j p.2 (Ioc s t ×ˢ B) ∂law μ J) =
      (∫⁻ p, H p ∂law μ J) * (positiveVolume.prod positiveVolume) (Ioc s t ×ˢ B) := by
  have hm : Measurable (fun p : Sample A J =>
      MarkedNoise.countingMeasure j p.2 (Ioc s t ×ˢ B)) :=
    ((Measure.measurable_coe (measurableSet_Ioc.prod hB)).comp
      (MarkedNoise.measurable_countingMeasure j)).comp measurable_snd
  have hind := independent_filtration_countingMeasure_windowrectangle
    μ j m B hB hbound s (t-s) hs (sub_nonneg.mpr hst)
  rw [add_sub_cancel] at hind
  have hfun : IndepFun H (fun p => MarkedNoise.countingMeasure j p.2 (Ioc s t ×ˢ B))
      (law μ J) := indep_of_indep_of_le_left hind hH.comap_le
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hH.mono ((filtration A J).le s) le_rfl).aemeasurable hm.aemeasurable hfun,
    lintegral_counting_set μ j _ (measurableSet_Ioc.prod hB)]

/-- The same identity allows coefficients measurable only in the null-augmented history. -/
theorem lintegral_completedPast_mul_countingMeasure
    (μ : Measure A) [IsProbabilityMeasure μ] (j : J) (m : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (H : Sample A J → ℝ≥0∞)
    (hH : Measurable[CommonInitialStopping.completedAt μ J s] H) :
    (∫⁻ p, H p * MarkedNoise.countingMeasure j p.2 (Ioc s t ×ˢ B)
      ∂CommonInitialStopping.completedLaw μ J) =
      (∫⁻ p, H p ∂CommonInitialStopping.completedLaw μ J) *
        (positiveVolume.prod positiveVolume) (Ioc s t ×ˢ B) := by
  have hm : Measurable[CommonInitialStopping.completedSpace μ J]
      (fun p : Sample A J => MarkedNoise.countingMeasure j p.2 (Ioc s t ×ˢ B)) :=
    (((Measure.measurable_coe (measurableSet_Ioc.prod hB)).comp
      (MarkedNoise.measurable_countingMeasure j)).comp measurable_snd).mono
        EventuallyMeasurableSpace.measurable_le le_rfl
  have hind := independent_completedAt_countingMeasure_windowrectangle
    μ j m B hB hbound s (t-s) hs (sub_nonneg.mpr hst)
  rw [add_sub_cancel] at hind
  have hfun : IndepFun H (fun p => MarkedNoise.countingMeasure j p.2 (Ioc s t ×ˢ B))
      (CommonInitialStopping.completedLaw μ J) :=
    indep_of_indep_of_le_left hind hH.comap_le
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hH.mono (CommonInitialStopping.completedAt_le_completedSpace μ J s) le_rfl).aemeasurable
      hm.aemeasurable hfun,
    lintegral_counting_set_completed μ j _ (measurableSet_Ioc.prod hB)]

theorem lintegral_indicator_countingMeasure
    (μ : Measure A) [IsProbabilityMeasure μ] (j : J) (m : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (C : Set (Sample A J)) (hC : MeasurableSet[filtration A J s] C) :
    (∫⁻ p, C.indicator (fun p => MarkedNoise.countingMeasure j p.2 (Ioc s t ×ˢ B)) p
      ∂law μ J) = law μ J C * (positiveVolume.prod positiveVolume) (Ioc s t ×ˢ B) := by
  have h := lintegral_past_mul_countingMeasure μ j m B hB hbound s t hs hst
    (C.indicator (fun _ => 1)) (measurable_const.indicator hC)
  have hI : (∫⁻ p, C.indicator (fun _ => (1 : ℝ≥0∞)) p ∂law μ J) = law μ J C :=
    lintegral_indicator_one (μ := law μ J) ((filtration A J).le s _ hC)
  rw [hI] at h
  convert h using 1
  congr 1
  funext p
  by_cases hp : p ∈ C <;> simp [hp]

theorem lintegral_completedIndicator_countingMeasure
    (μ : Measure A) [IsProbabilityMeasure μ] (j : J) (m : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (C : Set (Sample A J))
    (hC : MeasurableSet[CommonInitialStopping.completedAt μ J s] C) :
    (∫⁻ p, C.indicator (fun p => MarkedNoise.countingMeasure j p.2 (Ioc s t ×ˢ B)) p
      ∂CommonInitialStopping.completedLaw μ J) =
      CommonInitialStopping.completedLaw μ J C *
        (positiveVolume.prod positiveVolume) (Ioc s t ×ˢ B) := by
  have h := lintegral_completedPast_mul_countingMeasure μ j m B hB hbound s t hs hst
    (C.indicator (fun _ => 1)) (measurable_const.indicator hC)
  have hI : (∫⁻ p, C.indicator (fun _ => (1 : ℝ≥0∞)) p
      ∂CommonInitialStopping.completedLaw μ J) = CommonInitialStopping.completedLaw μ J C :=
    lintegral_indicator_one (μ := CommonInitialStopping.completedLaw μ J)
      (CommonInitialStopping.completedAt_le_completedSpace μ J s _ hC)
  rw [hI] at h
  convert h using 1
  congr 1
  funext p
  by_cases hp : p ∈ C <;> simp [hp]

/-- A nonnegative past coefficient on a later deterministic time-height rectangle. -/
def step (s t : ℝ) (B : Set ℝ) (H : Sample A J → ℝ≥0∞)
    (p : Sample A J) (q : ℝ × ℝ) : ℝ≥0∞ :=
  (Ioc s t ×ˢ B).indicator (fun _ => H p) q

omit [MeasurableSpace A] in
theorem measurable_step_points (s t : ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (H : Sample A J → ℝ≥0∞) (p : Sample A J) : Measurable (step s t B H p) :=
  measurable_const.indicator (measurableSet_Ioc.prod hB)

omit [MeasurableSpace A] in
theorem lintegral_step (s t : ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (H : Sample A J → ℝ≥0∞) (p : Sample A J) (ν : Measure (ℝ × ℝ)) :
    (∫⁻ q, step s t B H p q ∂ν) = H p * ν (Ioc s t ×ˢ B) := by
  change (∫⁻ q, (Ioc s t ×ˢ B).indicator (fun _ => H p) q ∂ν) = _
  exact lintegral_indicator_const (measurableSet_Ioc.prod hB) (H p)

theorem compensation_step
    (μ : Measure A) [IsProbabilityMeasure μ] (j : J) (m : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (H : Sample A J → ℝ≥0∞) (hH : Measurable[filtration A J s] H) :
    (∫⁻ p, ∫⁻ q, step s t B H p q ∂MarkedNoise.countingMeasure j p.2 ∂law μ J) =
      ∫⁻ p, ∫⁻ q, step s t B H p q ∂positiveVolume.prod positiveVolume ∂law μ J := by
  simp_rw [lintegral_step s t B hB H]
  rw [lintegral_past_mul_countingMeasure μ j m B hB hbound s t hs hst H hH]
  symm
  exact lintegral_mul_const _ (hH.mono ((filtration A J).le s) le_rfl)

theorem compensation_step_completed
    (μ : Measure A) [IsProbabilityMeasure μ] (j : J) (m : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (H : Sample A J → ℝ≥0∞)
    (hH : Measurable[CommonInitialStopping.completedAt μ J s] H) :
    (∫⁻ p, ∫⁻ q, step s t B H p q ∂MarkedNoise.countingMeasure j p.2
      ∂CommonInitialStopping.completedLaw μ J) =
      ∫⁻ p, ∫⁻ q, step s t B H p q ∂positiveVolume.prod positiveVolume
        ∂CommonInitialStopping.completedLaw μ J := by
  simp_rw [lintegral_step s t B hB H]
  rw [lintegral_completedPast_mul_countingMeasure μ j m B hB hbound s t hs hst H hH]
  symm
  exact lintegral_mul_const _
    (hH.mono (CommonInitialStopping.completedAt_le_completedSpace μ J s) le_rfl)

end CarryingCapacity.InitialElementaryCompensation
