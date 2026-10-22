import CarryingCapacity.MarkedCountingKernel

/-!
# Integrable predictable compensation

For strongly predictable vector-valued functions, integrability against the
deterministic sample-time-height measure is equivalent to integrability against
the actual Campbell measure. Bochner Fubini then gives the actual iterated
compensation identity and integrability of the random counting integral.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter MeasurableSpace

namespace CarryingCapacity.PredictableIntegral
open MarkedNoise MarkedIntensity PredictableSets PredictableCompensation MarkedCountingKernel

variable {J V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

omit [NormedSpace ℝ V] in
theorem integrable_campbell_iff (j : J) (f : SamplePoint J → V)
    (hf : StronglyMeasurable[predictable (CommonNoiseFiltration.filtration J)] f) :
    Integrable f (campbell j) ↔ Integrable f (productIntensity J) := by
  constructor
  · intro hi
    have ht := hi.trim (predictable_le _) hf
    rw [trim_campbell_eq_product] at ht
    exact integrable_of_integrable_trim (predictable_le _) ht
  · intro hi
    have ht := hi.trim (predictable_le _) hf
    rw [← trim_campbell_eq_product j] at ht
    exact integrable_of_integrable_trim (predictable_le _) ht

theorem integral_campbell_eq_product (j : J) (f : SamplePoint J → V)
    (hf : StronglyMeasurable[predictable (CommonNoiseFiltration.filtration J)] f) :
    (∫ x, f x ∂campbell j) = ∫ x, f x ∂productIntensity J := by
  rw [integral_trim (predictable_le _) hf, trim_campbell_eq_product]
  exact (integral_trim (predictable_le _) hf).symm

omit [NormedSpace ℝ V] in
/-- Integrability is established for the actual random-measure sections. -/
theorem ae_integrable_counting (j : J) (f : SamplePoint J → V)
    (hf : StronglyMeasurable[predictable (CommonNoiseFiltration.filtration J)] f)
    (hi : Integrable f (productIntensity J)) :
    ∀ᵐ ω ∂law J, Integrable (fun p => f (ω,p)) (countingMeasure j ω) :=
  ae_integrable_countingMeasure j f ((integrable_campbell_iff j f hf).mpr hi)

theorem integrable_counting_integral (j : J) (f : SamplePoint J → V)
    (hf : StronglyMeasurable[predictable (CommonNoiseFiltration.filtration J)] f)
    (hi : Integrable f (productIntensity J)) :
    Integrable (fun ω => ∫ p, f (ω,p) ∂countingMeasure j ω) (law J) :=
  integrable_countingIntegral j f ((integrable_campbell_iff j f hf).mpr hi)

/-- Compensation for signed or vector-valued predictable integrands under
an explicit, deterministic product-integrability hypothesis. -/
theorem compensation_integrable (j : J) (f : SamplePoint J → V)
    (hf : StronglyMeasurable[predictable (CommonNoiseFiltration.filtration J)] f)
    (hi : Integrable f (productIntensity J)) :
    (∫ ω, ∫ p, f (ω,p) ∂countingMeasure j ω ∂law J) =
      ∫ ω, ∫ p, f (ω,p) ∂positiveVolume.prod positiveVolume ∂law J := by
  rw [← integral_campbell j f ((integrable_campbell_iff j f hf).mpr hi),
    integral_campbell_eq_product j f hf]
  exact integral_prod f hi

end CarryingCapacity.PredictableIntegral
