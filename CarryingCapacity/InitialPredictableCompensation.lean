import CarryingCapacity.InitialElementaryCompensation
import CarryingCapacity.PredictableCompensation

/-!
# Predictable compensation with an arbitrary independent initial record

Fixing an initial record preserves predictability in the raw marked-noise
filtration. Applying the proved noise compensation theorem to every such
section and then Tonelli's theorem proves full nonnegative predictable
compensation under the actual initial-record/noise product law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set MeasurableSpace
open scoped ENNReal

namespace CarryingCapacity.InitialPredictableCompensation
open CommonInitialNoise MarkedIntensity PredictableSets

variable {A J : Type*} [MeasurableSpace A]

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

abbrev SamplePoint (A J : Type*) := Sample A J × (ℝ × ℝ)

/-- Insert a fixed full initial record, leaving the noise and marked point untouched. -/
def initialSection (a : A) (x : PredictableCompensation.SamplePoint J) : SamplePoint A J :=
  ((a, x.1), x.2)

/-- Sections of the actual initial-product predictable sigma algebra are
predictable for the original noise filtration. This holds for every initial record. -/
theorem measurable_initialSection_predictable (a : A) :
    @Measurable (PredictableCompensation.SamplePoint J) (SamplePoint A J)
      (predictable (CommonNoiseFiltration.filtration J))
      (predictable (filtration A J)) (initialSection a) := by
  apply @measurable_generateFrom (PredictableCompensation.SamplePoint J) (SamplePoint A J)
    (predictable (CommonNoiseFiltration.filtration J)) (rectangles (filtration A J))
    (initialSection a)
  rintro S ⟨s, t, C, B, m, hs, hC, hB, hb, rfl⟩
  have hinit : @Measurable (MarkedNoise.Sample J) (Sample A J)
      (CommonNoiseFiltration.filtration J s) (filtration A J s) (Prod.mk a) :=
    @measurable_prodMk_left A (MarkedNoise.Sample J) _
      (CommonNoiseFiltration.filtration J s) a
  have hset : initialSection a ⁻¹' rectangle C s t B =
      rectangle (Prod.mk a ⁻¹' C) s t B := rfl
  rw [hset]
  exact measurableSet_predictable_rectangle_bounded
    (CommonNoiseFiltration.filtration J) s t hs _ (hC.preimage hinit) B hB m hb

/-- A predictable integrand remains predictable after fixing the initial record. -/
theorem measurable_initial_section {V : Type*} [MeasurableSpace V]
    (f : SamplePoint A J → V) (hf : Measurable[predictable (filtration A J)] f) (a : A) :
    Measurable[predictable (CommonNoiseFiltration.filtration J)]
      (fun x : PredictableCompensation.SamplePoint J => f ((a, x.1), x.2)) :=
  hf.comp (measurable_initialSection_predictable a)

/-- Joint measurability of the integral against the actual random measure
follows directly from its countable family of marked points. -/
theorem measurable_countingIntegral (j : J) (f : SamplePoint A J → ℝ≥0∞)
    (hf : Measurable f) :
    Measurable (fun p : Sample A J =>
      ∫⁻ q, f (p, q) ∂MarkedNoise.countingMeasure j p.2) := by
  have he : (fun p : Sample A J => ∫⁻ q, f (p, q) ∂MarkedNoise.countingMeasure j p.2) =
      (fun p => ∑' k : ℕ × ℕ, f (p, MarkedNoise.point j p.2 k)) := by
    funext p
    rw [MarkedNoise.countingMeasure, lintegral_sum_measure]
    simp only [lintegral_dirac]
  rw [he]
  apply Measurable.ennreal_tsum
  intro k
  exact hf.comp (measurable_id.prodMk
    ((MarkedNoise.measurable_point j k).comp measurable_snd))

/-- Full compensation for every nonnegative predictable integrand on the
actual arbitrarily initialized sample space. Infinite expectations are allowed. -/
theorem compensation_nonnegative
    (μ : Measure A) [IsProbabilityMeasure μ] (j : J) (f : SamplePoint A J → ℝ≥0∞)
    (hf : Measurable[predictable (filtration A J)] f) :
    (∫⁻ p, ∫⁻ q, f (p, q) ∂MarkedNoise.countingMeasure j p.2 ∂law μ J) =
      ∫⁻ p, ∫⁻ q, f (p, q) ∂positiveVolume.prod positiveVolume ∂law μ J := by
  have hm : Measurable f := hf.mono (predictable_le _) le_rfl
  have hrandom := measurable_countingIntegral j f hm
  have hdet : Measurable (fun p : Sample A J =>
      ∫⁻ q, f (p, q) ∂positiveVolume.prod positiveVolume) := hm.lintegral_prod_right'
  change (∫⁻ p, ∫⁻ q, f (p, q) ∂MarkedNoise.countingMeasure j p.2
      ∂μ.prod (MarkedNoise.law J)) =
    ∫⁻ p, ∫⁻ q, f (p, q) ∂positiveVolume.prod positiveVolume
      ∂μ.prod (MarkedNoise.law J)
  rw [lintegral_prod _ hrandom.aemeasurable, lintegral_prod _ hdet.aemeasurable]
  apply lintegral_congr
  intro a
  exact PredictableCompensation.compensation_nonnegative j
    (fun x => f ((a, x.1), x.2)) (measurable_initial_section f hf a)

end CarryingCapacity.InitialPredictableCompensation
