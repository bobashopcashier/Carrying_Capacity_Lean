import CarryingCapacity.InitialPredictableCompensation
import CarryingCapacity.PredictableIntegral

/-!
# Integrable predictable compensation with an arbitrary initial record

The actual counting kernel is pulled back along the noise projection. The
proved nonnegative compensation identity identifies its genuine Campbell
measure with the deterministic intensity on the predictable sigma algebra.
This yields integrability equivalence and signed or vector-valued compensation
on the actual initial-record/noise product probability space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter MeasurableSpace
open scoped ENNReal

namespace CarryingCapacity.InitialPredictableIntegral
open CommonInitialNoise MarkedIntensity PredictableSets InitialPredictableCompensation

variable {A J : Type*} [MeasurableSpace A]

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

/-- The original random counting measure, evaluated on the noise coordinate. -/
def countingKernel (j : J) : Kernel (Sample A J) (ℝ × ℝ) :=
  (MarkedCountingKernel.countingKernel j).comap Prod.snd measurable_snd

instance (j : J) : IsSFiniteKernel (countingKernel (A := A) j) := by
  unfold countingKernel
  infer_instance

theorem countingKernel_apply (j : J) (p : Sample A J) :
    countingKernel j p = MarkedNoise.countingMeasure j p.2 :=
  MarkedCountingKernel.countingKernel_apply j p.2

/-- The actual joint sample-point measure from the constructed counting kernel. -/
def campbell (μ : Measure A) (j : J) : Measure (SamplePoint A J) :=
  (law μ J) ⊗ₘ countingKernel j

def productIntensity (μ : Measure A) (J : Type*) : Measure (SamplePoint A J) :=
  (law μ J).prod (positiveVolume.prod positiveVolume)

theorem lintegral_campbell (μ : Measure A) [IsProbabilityMeasure μ]
    (j : J) (f : SamplePoint A J → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂campbell μ j) =
      ∫⁻ p, ∫⁻ q, f (p, q) ∂MarkedNoise.countingMeasure j p.2 ∂law μ J := by
  rw [campbell, Measure.lintegral_compProd hf]
  simp only [countingKernel_apply]

/-- The established nonnegative predictable compensation identifies the
actual Campbell measure on the entire predictable sigma algebra. -/
theorem trim_campbell_eq_product (μ : Measure A) [IsProbabilityMeasure μ] (j : J) :
    (campbell μ j).trim (predictable_le (filtration A J)) =
      (productIntensity μ J).trim (predictable_le (filtration A J)) := by
  apply @Measure.ext (SamplePoint A J) (predictable (filtration A J))
  intro S hS
  have hSa : MeasurableSet S := predictable_le (filtration A J) S hS
  have hI : Measurable[predictable (filtration A J)]
      (S.indicator (1 : SamplePoint A J → ℝ≥0∞)) := by
    letI : MeasurableSpace (SamplePoint A J) := predictable (filtration A J)
    exact measurable_one.indicator hS
  rw [trim_measurableSet_eq _ hS, trim_measurableSet_eq _ hS]
  calc
    _ = ∫⁻ x, S.indicator 1 x ∂campbell μ j := (lintegral_indicator_one hSa).symm
    _ = ∫⁻ p, ∫⁻ q, S.indicator 1 (p, q)
        ∂MarkedNoise.countingMeasure j p.2 ∂law μ J :=
      lintegral_campbell μ j _ (hI.mono (predictable_le _) le_rfl)
    _ = ∫⁻ p, ∫⁻ q, S.indicator 1 (p, q)
        ∂positiveVolume.prod positiveVolume ∂law μ J :=
      compensation_nonnegative μ j _ hI
    _ = ∫⁻ x, S.indicator 1 x ∂productIntensity μ J :=
      (lintegral_prod _ (hI.mono (predictable_le _) le_rfl).aemeasurable).symm
    _ = _ := lintegral_indicator_one hSa

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ V] in
/-- Predictable integrability is equivalent for the actual Campbell and
deterministic product intensity measures. -/
theorem integrable_campbell_iff (μ : Measure A) [IsProbabilityMeasure μ]
    (j : J) (f : SamplePoint A J → V)
    (hf : StronglyMeasurable[predictable (filtration A J)] f) :
    Integrable f (campbell μ j) ↔ Integrable f (productIntensity μ J) := by
  constructor
  · intro hi
    have ht := hi.trim (predictable_le _) hf
    rw [trim_campbell_eq_product] at ht
    exact integrable_of_integrable_trim (predictable_le _) ht
  · intro hi
    have ht := hi.trim (predictable_le _) hf
    rw [← trim_campbell_eq_product μ j] at ht
    exact integrable_of_integrable_trim (predictable_le _) ht

theorem integral_campbell_eq_product (μ : Measure A) [IsProbabilityMeasure μ]
    (j : J) (f : SamplePoint A J → V)
    (hf : StronglyMeasurable[predictable (filtration A J)] f) :
    (∫ x, f x ∂campbell μ j) = ∫ x, f x ∂productIntensity μ J := by
  rw [integral_trim (predictable_le _) hf, trim_campbell_eq_product]
  exact (integral_trim (predictable_le _) hf).symm

omit [NormedSpace ℝ V] in
/-- Almost every actual noise realization admits an integrable random-measure section. -/
theorem ae_integrable_counting (μ : Measure A) [IsProbabilityMeasure μ]
    (j : J) (f : SamplePoint A J → V)
    (hf : StronglyMeasurable[predictable (filtration A J)] f)
    (hi : Integrable f (productIntensity μ J)) :
    ∀ᵐ p ∂law μ J, Integrable (fun q => f (p, q)) (MarkedNoise.countingMeasure j p.2) := by
  have hc := (integrable_campbell_iff μ j f hf).mpr hi
  change Integrable f ((law μ J) ⊗ₘ countingKernel j) at hc
  have h := ((Measure.integrable_compProd_iff hc.aestronglyMeasurable).mp hc).1
  simpa only [countingKernel_apply] using h

/-- The actual vector-valued random counting integral is integrable over
both the initial record and common noise. -/
theorem integrable_counting_integral (μ : Measure A) [IsProbabilityMeasure μ]
    (j : J) (f : SamplePoint A J → V)
    (hf : StronglyMeasurable[predictable (filtration A J)] f)
    (hi : Integrable f (productIntensity μ J)) :
    Integrable (fun p => ∫ q, f (p, q) ∂MarkedNoise.countingMeasure j p.2) (law μ J) := by
  have hc := (integrable_campbell_iff μ j f hf).mpr hi
  rw [campbell, Measure.compProd] at hc
  have h := hc.integral_compProd
  simpa only [Kernel.prodMkLeft_apply, Kernel.const_apply, countingKernel_apply] using h

/-- Signed and vector-valued compensation on the actual independently
initialized probability space, under deterministic product integrability. -/
theorem compensation_integrable (μ : Measure A) [IsProbabilityMeasure μ]
    (j : J) (f : SamplePoint A J → V)
    (hf : StronglyMeasurable[predictable (filtration A J)] f)
    (hi : Integrable f (productIntensity μ J)) :
    (∫ p, ∫ q, f (p, q) ∂MarkedNoise.countingMeasure j p.2 ∂law μ J) =
      ∫ p, ∫ q, f (p, q) ∂positiveVolume.prod positiveVolume ∂law μ J := by
  have hc := (integrable_campbell_iff μ j f hf).mpr hi
  calc
    _ = ∫ x, f x ∂campbell μ j := by
      change Integrable f ((law μ J) ⊗ₘ countingKernel j) at hc
      simpa only [campbell, countingKernel_apply] using (Measure.integral_compProd hc).symm
    _ = ∫ x, f x ∂productIntensity μ J := integral_campbell_eq_product μ j f hf
    _ = _ := integral_prod f hi

end CarryingCapacity.InitialPredictableIntegral
