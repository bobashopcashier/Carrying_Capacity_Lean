import CarryingCapacity.CommonMarkedPastIndependence
import CarryingCapacity.MarkedIntensity
import Mathlib.Probability.Integration

/-!
# Compensation for actual elementary predictable marked integrands

A nonnegative coefficient measurable in the full past may multiply the count
of a later deterministic time-height rectangle. Its expectation factors by the
proved independence, and the actual intensity supplies the deterministic area.
No compensation identity is assumed and no finite expectation of the past
coefficient is required.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace CarryingCapacity.MarkedElementaryCompensation
open MarkedNoise MarkedIntensity CommonMarkedPastIndependence

variable {J : Type*}

/-- Exact elementary compensation for any nonnegative coefficient known at s. -/
theorem lintegral_past_mul_countingMeasure (j : J) (m : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (H : MarkedNoise.Sample J → ℝ≥0∞)
    (hH : Measurable[CommonNoiseFiltration.filtration J s] H) :
    (∫⁻ ω, H ω * countingMeasure j ω (Ioc s t ×ˢ B) ∂law J) =
      (∫⁻ ω, H ω ∂law J) * (positiveVolume.prod positiveVolume) (Ioc s t ×ˢ B) := by
  have hm : Measurable (fun ω : MarkedNoise.Sample J =>
      countingMeasure j ω (Ioc s t ×ˢ B)) :=
    (Measure.measurable_coe (measurableSet_Ioc.prod hB)).comp (measurable_countingMeasure j)
  have hind := independent_filtration_countingMeasure_windowrectangle
    j m B hB hbound s (t-s) hs (sub_nonneg.mpr hst)
  rw [add_sub_cancel] at hind
  have hfun : IndepFun H (fun ω => countingMeasure j ω (Ioc s t ×ˢ B)) (law J) :=
    indep_of_indep_of_le_left hind hH.comap_le
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hH.mono ((CommonNoiseFiltration.filtration J).le s) le_rfl).aemeasurable
    hm.aemeasurable hfun, lintegral_counting_set j _ (measurableSet_Ioc.prod hB)]

/-- Past events are valid predictable coefficients, including null events. -/
theorem lintegral_indicator_countingMeasure (j : J) (m : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (A : Set (MarkedNoise.Sample J))
    (hA : MeasurableSet[CommonNoiseFiltration.filtration J s] A) :
    (∫⁻ ω, A.indicator (fun ω => countingMeasure j ω (Ioc s t ×ˢ B)) ω ∂law J) =
      law J A * (positiveVolume.prod positiveVolume) (Ioc s t ×ˢ B) := by
  have h := lintegral_past_mul_countingMeasure j m B hB hbound s t hs hst
    (A.indicator (fun _ => 1)) (measurable_const.indicator hA)
  have hmass : (∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂law J) = law J A :=
    lintegral_indicator_one ((CommonNoiseFiltration.filtration J).le s _ hA)
  rw [hmass] at h
  convert h using 1
  congr 1
  funext ω
  by_cases hω : ω ∈ A <;> simp [hω]

/-- A standard predictable step function: a past coefficient on a later rectangle. -/
def step (s t : ℝ) (B : Set ℝ) (H : MarkedNoise.Sample J → ℝ≥0∞)
    (ω : MarkedNoise.Sample J) (p : ℝ × ℝ) : ℝ≥0∞ :=
  (Ioc s t ×ˢ B).indicator (fun _ => H ω) p

theorem measurable_step_points (s t : ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (H : MarkedNoise.Sample J → ℝ≥0∞) (ω : MarkedNoise.Sample J) :
    Measurable (step s t B H ω) :=
  measurable_const.indicator (measurableSet_Ioc.prod hB)

theorem lintegral_step (s t : ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (H : MarkedNoise.Sample J → ℝ≥0∞) (ω : MarkedNoise.Sample J)
    (ν : Measure (ℝ × ℝ)) :
    (∫⁻ p, step s t B H ω p ∂ν) = H ω * ν (Ioc s t ×ˢ B) := by
  change (∫⁻ p, (Ioc s t ×ˢ B).indicator (fun _ => H ω) p ∂ν) = _
  rw [lintegral_indicator_const (measurableSet_Ioc.prod hB)]

/-- The actual random-measure integral and deterministic intensity integral
agree in expectation for elementary predictable nonnegative integrands. -/
theorem compensation_step (j : J) (m : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (H : MarkedNoise.Sample J → ℝ≥0∞)
    (hH : Measurable[CommonNoiseFiltration.filtration J s] H) :
    (∫⁻ ω, ∫⁻ p, step s t B H ω p ∂countingMeasure j ω ∂law J) =
      ∫⁻ ω, ∫⁻ p, step s t B H ω p ∂positiveVolume.prod positiveVolume ∂law J := by
  simp_rw [lintegral_step s t B hB H]
  rw [lintegral_past_mul_countingMeasure j m B hB hbound s t hs hst H hH]
  symm
  exact lintegral_mul_const _
    (hH.mono ((CommonNoiseFiltration.filtration J).le s) le_rfl)

end CarryingCapacity.MarkedElementaryCompensation
