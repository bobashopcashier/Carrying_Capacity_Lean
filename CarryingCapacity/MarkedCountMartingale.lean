import CarryingCapacity.MarkedCountAdapted
import CarryingCapacity.CommonMarkedPastIndependence
import Mathlib.Probability.ConditionalExpectation

/-!
# The actual compensated marked count is a martingale

Bounded measurable height categories have finite first moments. The derived
independence from the entire observed marked history identifies the conditional
mean of each future window. Together with exact adaptedness of the original
prefix count, this proves the compensated process is a martingale.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace CarryingCapacity.MarkedCountMartingale
open MarkedNoise MarkedIntensity MarkedCountMoments MarkedCountAdapted
  CommonMarkedPastIndependence CommonNoiseFiltration

variable {J : Type*}

/-- Conditional mean of the actual future rectangle count given all marked history. -/
theorem conditional_realWindowCount (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    (law J)[realWindowCount j B s t | filtration J s] =ᵐ[law J]
      fun _ => (t-s) * positiveVolume.real B := by
  let X : MarkedNoise.Sample J → ℝ≥0∞ := fun ω => countingMeasure j ω (Ioc s t ×ˢ B)
  have hm : Measurable X := measurable_countingMass j _ (measurableSet_Ioc.prod hB)
  have hf : StronglyMeasurable[MeasurableSpace.comap X inferInstance]
      (realWindowCount j B s t) :=
    ((comap_measurable X).ennreal_toReal).stronglyMeasurable
  have hi := independent_filtration_countingMeasure_windowrectangle
    j m B hB hbound s (t-s) hs (sub_nonneg.mpr hst)
  rw [add_sub_cancel] at hi
  have h := condExp_indep_eq hm.comap_le ((filtration J).le s) hf hi.symm
  simpa only [integral_realWindowCount j m B hB hbound s t hs hst] using h

/-- Actual prefix count minus its deterministic intensity. -/
def compensated (j : J) (B : Set ℝ) (t : ℝ≥0) (ω : MarkedNoise.Sample J) : ℝ :=
  realCount j B t ω - (t : ℝ) * positiveVolume.real B

theorem integrable_compensated (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ)) (t : ℝ≥0) :
    Integrable (compensated j B t) (law J) :=
  (integrable_realCount j m B hB hbound t).sub (integrable_const _)

theorem adapted_compensated (j : J) (B : Set ℝ) (hB : MeasurableSet B) :
    Adapted (nonnegativeFiltration J) (compensated j B) := by
  intro t
  exact (adapted_nonnegative_realCount j B hB t).sub stronglyMeasurable_const

/-- Actual compensated increments have zero conditional mean. -/
theorem conditional_compensated_difference (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ≥0) (hst : s ≤ t) :
    (law J)[compensated j B t - compensated j B s | nonnegativeFiltration J s]
      =ᵐ[law J] fun _ => (0 : ℝ) := by
  have hrel : compensated j B t - compensated j B s =ᵐ[law J]
      realWindowCount j B s t - (fun _ => ((t:ℝ)-(s:ℝ)) * positiveVolume.real B) := by
    filter_upwards [ae_realCount_sub_eq_realWindowCount j m B hB hbound s t s.property hst]
      with ω hω
    simp only [Pi.sub_apply, compensated]
    rw [← hω]
    ring
  have hmean := conditional_realWindowCount j m B hB hbound s t s.property hst
  have hsub := condExp_sub (integrable_realWindowCount j m B hB hbound s t s.property)
    (integrable_const (((t:ℝ)-(s:ℝ)) * positiveVolume.real B)) (nonnegativeFiltration J s)
  rw [condExp_const ((nonnegativeFiltration J).le s)] at hsub
  apply (condExp_congr_ae hrel).trans
  apply hsub.trans
  filter_upwards [hmean] with ω hω
  change (law J)[realWindowCount j B s t | filtration J s] ω -
    ((t:ℝ)-(s:ℝ)) * positiveVolume.real B = 0
  rw [hω, sub_self]

/-- The compensated actual bounded-height count is a martingale in the full
natural marked-noise filtration, not only its own count filtration. -/
theorem martingale_compensated (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ)) :
    Martingale (compensated j B) (nonnegativeFiltration J) (law J) := by
  refine ⟨adapted_compensated j B hB, ?_⟩
  intro s t hst
  have hzero := conditional_compensated_difference j m B hB hbound s t hst
  have hsub := condExp_sub (integrable_compensated j m B hB hbound t)
    (integrable_compensated j m B hB hbound s) (nonnegativeFiltration J s)
  rw [condExp_of_stronglyMeasurable ((nonnegativeFiltration J).le s)
    (adapted_compensated j B hB s) (integrable_compensated j m B hB hbound s)] at hsub
  filter_upwards [hzero, hsub] with ω hzero hsub
  simp only [Pi.sub_apply] at hsub
  linarith

theorem integral_compensated (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ)) (t : ℝ≥0) :
    (∫ ω, compensated j B t ω ∂law J) = 0 := by
  simp only [compensated]
  rw [integral_sub (integrable_realCount j m B hB hbound t) (integrable_const _),
    integral_realCount j m B hB hbound t t.property, integral_const]
  simp

end CarryingCapacity.MarkedCountMartingale
