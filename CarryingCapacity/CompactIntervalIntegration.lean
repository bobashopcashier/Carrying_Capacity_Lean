import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Integrating over the compact interval as the time type

Empirical-error theorems quantify moment bounds over their entire time type.
Using the interval subtype makes those bounds genuinely horizon-specific.
The measure below is finite, including a zero horizon, and its integrals and
integrability are exactly those of the ordinary restricted Lebesgue measure.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace CarryingCapacity.CompactIntervalIntegration

/-- Lebesgue measure on the actual interval subtype. Restricting before
pullback makes finiteness available directly from the existing instances. -/
def timeMeasure (T : ℝ) : Measure (Icc (0 : ℝ) T) :=
  (volume.restrict (Icc (0 : ℝ) T)).comap Subtype.val

instance timeMeasure_finite (T : ℝ) : IsFiniteMeasure (timeMeasure T) := by
  unfold timeMeasure
  infer_instance

/-- Genuine integrability is equivalent under the subtype representation. -/
theorem integrable_iff (T : ℝ) (f : ℝ → ℝ) :
    Integrable (fun t : Icc (0 : ℝ) T => f t) (timeMeasure T) ↔
      IntegrableOn f (Icc 0 T) volume := by
  have h := (integrableOn_iff_comap_subtypeVal
    (μ := volume.restrict (Icc (0 : ℝ) T)) (f := f)
    (s := Icc (0 : ℝ) T) measurableSet_Icc).symm
  simpa only [timeMeasure, Function.comp_def, IntegrableOn,
    Measure.restrict_restrict measurableSet_Icc, inter_self] using h

/-- This equality transports the integral itself; it does not assert
integrability for an arbitrary function. Use `integrable_iff` for that. -/
theorem integral_eq_setIntegral (T : ℝ) (f : ℝ → ℝ) :
    (∫ t : Icc (0 : ℝ) T, f t ∂timeMeasure T) = ∫ t in Icc 0 T, f t := by
  rw [timeMeasure, integral_subtype_comap measurableSet_Icc]
  rw [Measure.restrict_restrict measurableSet_Icc, inter_self]

/-- The left endpoint has zero Lebesgue mass, including when `T = 0`. -/
theorem integral_eq_Ioc (T : ℝ) (f : ℝ → ℝ) :
    (∫ t : Icc (0 : ℝ) T, f t ∂timeMeasure T) = ∫ t in Ioc 0 T, f t := by
  rw [integral_eq_setIntegral, integral_Icc_eq_integral_Ioc]

/-- Integral convergence proved on the interval time type transfers to the
ordinary set integral without any additional domination premise. -/
theorem tendsto_integral_iff {ι : Type*} (l : Filter ι) (T : ℝ)
    (f : ι → ℝ → ℝ) (a : ℝ) :
    Tendsto (fun i => ∫ t : Icc (0 : ℝ) T, f i t ∂timeMeasure T) l (𝓝 a) ↔
      Tendsto (fun i => ∫ t in Icc 0 T, f i t) l (𝓝 a) := by
  simp only [integral_eq_setIntegral]

end CarryingCapacity.CompactIntervalIntegration
