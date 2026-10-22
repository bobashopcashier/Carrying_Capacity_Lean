import CarryingCapacity.PredictableCompensation
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# The actual marked counting measure as an s-finite kernel

The kernel is a countable sum of deterministic kernels at the constructed
marked points. Its composition product is the genuine sample-point Campbell
measure. Consequently Bochner Fubini applies after integrability is proved.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace CarryingCapacity.MarkedCountingKernel
open MarkedNoise PredictableCompensation

variable {J : Type*}

/-- A countable sum of the actual point kernels, not an assumed compensator. -/
def countingKernel (j : J) : Kernel (MarkedNoise.Sample J) (ℝ × ℝ) :=
  Kernel.sum (fun p : ℕ × ℕ => Kernel.deterministic
    (fun ω => point j ω p) (measurable_point j p))

instance (j : J) : IsSFiniteKernel (countingKernel j) := by
  unfold countingKernel
  infer_instance

theorem countingKernel_apply (j : J) (ω : MarkedNoise.Sample J) :
    countingKernel j ω = countingMeasure j ω := by
  simp only [countingKernel, Kernel.sum_apply, Kernel.deterministic_apply, countingMeasure]

/-- The composition product retains both the actual sample and marked point. -/
theorem campbell_eq_compProd (j : J) :
    campbell j = (law J) ⊗ₘ countingKernel j := by
  apply Measure.ext
  intro S hS
  rw [← lintegral_indicator_one hS, ← lintegral_indicator_one hS]
  have hm : Measurable (S.indicator (1 : SamplePoint J → ℝ≥0∞)) :=
    measurable_one.indicator hS
  rw [lintegral_campbell j (S.indicator 1) hm,
    Measure.lintegral_compProd hm]
  simp only [countingKernel_apply]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ V] in
theorem ae_integrable_countingMeasure (j : J) (f : SamplePoint J → V)
    (hf : Integrable f (campbell j)) :
    ∀ᵐ ω ∂law J, Integrable (fun p => f (ω,p)) (countingMeasure j ω) := by
  rw [campbell_eq_compProd] at hf
  have h := ((Measure.integrable_compProd_iff hf.aestronglyMeasurable).mp hf).1
  simpa only [countingKernel_apply] using h

theorem integrable_countingIntegral (j : J) (f : SamplePoint J → V)
    (hf : Integrable f (campbell j)) :
    Integrable (fun ω => ∫ p, f (ω,p) ∂countingMeasure j ω) (law J) := by
  rw [campbell_eq_compProd, Measure.compProd] at hf
  have h := hf.integral_compProd
  simpa only [Kernel.prodMkLeft_apply, Kernel.const_apply, countingKernel_apply] using h

theorem integral_campbell (j : J) (f : SamplePoint J → V)
    (hf : Integrable f (campbell j)) :
    (∫ x, f x ∂campbell j) =
      ∫ ω, ∫ p, f (ω,p) ∂countingMeasure j ω ∂law J := by
  rw [campbell_eq_compProd] at hf ⊢
  rw [Measure.integral_compProd hf]
  simp only [countingKernel_apply]

end CarryingCapacity.MarkedCountingKernel
