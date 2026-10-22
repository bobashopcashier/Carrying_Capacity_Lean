import CarryingCapacity.TransportMetric
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Weak convergence from a coupling with vanishing mismatch probability

For countable measurable state spaces, exact agreement except on a vanishing
probability event controls every bounded continuous test. The sample spaces
may vary with the row. No common space across rows or weak-convergence premise
is required.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace CarryingCapacity.CoupledLawConvergence

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
  [OpensMeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

/-- The actual pushforward law, packaged in the weak-topology probability space. -/
def imageLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → E) (hX : Measurable X) : ProbabilityMeasure E :=
  ⟨P.map X, isProbabilityMeasure_map hX.aemeasurable⟩

/-- A bounded test sees only the event on which the coupled states differ. -/
theorem integral_difference_le_mismatch {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → E)
    (hX : Measurable X) (hY : Measurable Y) (f : BoundedContinuousFunction E ℝ) :
    |(∫ p, f (X p) ∂P) - ∫ p, f (Y p) ∂P| ≤
      2 * ‖f‖ * P.real {p | X p ≠ Y p} := by
  classical
  have hiX : Integrable (fun p => f (X p)) P :=
    (f.integrable (P.map X)).comp_measurable hX
  have hiY : Integrable (fun p => f (Y p)) P :=
    (f.integrable (P.map Y)).comp_measurable hY
  have hS : MeasurableSet {p | X p ≠ Y p} := (measurableSet_eq_fun_of_countable hX hY).compl
  have hi : Integrable ({p | X p ≠ Y p}.indicator (fun _ => (2 : ℝ) * ‖f‖)) P :=
    (integrable_const _).indicator hS
  have hb : ∀ᵐ p ∂P, ‖f (X p) - f (Y p)‖ ≤
      {p | X p ≠ Y p}.indicator (fun _ => (2 : ℝ) * ‖f‖) p := by
    apply Eventually.of_forall
    intro p
    by_cases hp : X p = Y p
    · simp [hp]
    · rw [Set.indicator_of_mem hp]
      exact (norm_sub_le _ _).trans (by linarith [f.norm_coe_le_norm (X p), f.norm_coe_le_norm (Y p)])
  rw [← integral_sub hiX hiY, ← Real.norm_eq_abs]
  apply (norm_integral_le_of_norm_le hi hb).trans_eq
  rw [integral_indicator_const _ hS, smul_eq_mul]
  ring

/-- Eventual equality of the comparison law and vanishing actual mismatch
probability imply weak convergence of the actual laws. -/
theorem tendsto_imageLaw_of_mismatch
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Ω n → E) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (ν : ProbabilityMeasure E)
    (hlaw : ∀ᶠ n in atTop, (P n).map (Y n) = ν.toMeasure)
    (hmismatch : Tendsto (fun n => (P n).real {p | X n p ≠ Y n p}) atTop (𝓝 0)) :
    Tendsto (fun n => imageLaw (P n) (X n) (hX n)) atTop (𝓝 ν) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun n => 2 * ‖f‖ * (P n).real {p | X n p ≠ Y n p}) atTop (𝓝 0) := by
    simpa using hmismatch.const_mul (2 * ‖f‖)
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [hlaw] with n hn
  have hye := integral_map_of_stronglyMeasurable (μ := P n) (hY n) f.continuous.measurable.stronglyMeasurable
  rw [hn] at hye
  change ‖(∫ x, f x ∂(P n).map (X n)) - ∫ x, f x ∂ν.toMeasure‖ ≤ _
  rw [integral_map_of_stronglyMeasurable (hX n) f.continuous.measurable.stronglyMeasurable, hye,
    Real.norm_eq_abs]
  exact integral_difference_le_mismatch (P n) (X n) (Y n) (hX n) (hY n) f

end CarryingCapacity.CoupledLawConvergence
