import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Weak convergence from an explicit exceptional event

The target can be an uncountable Borel metric space, including an actual
Skorokhod path space. The random maps need only be AE measurable. A supplied
null-measurable event contains all disagreements up to a null set; the proof
never asks whether the mismatch set itself is measurable. Vanishing event
probabilities and an eventual exact comparison marginal give weak convergence
of the actual pushforward probability measures on varying sample spaces.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace CarryingCapacity.CoupledPathLawConvergence

variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- The genuine pushforward of an AE-measurable random variable, as a
probability measure with its weak topology. -/
def imageLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → E) (hX : AEMeasurable X P) : ProbabilityMeasure E :=
  ⟨P.map X, isProbabilityMeasure_map hX⟩

/-- The supplied null-measurable exceptional event controls every bounded
continuous test. Neither the target nor the mismatch set needs to be countable. -/
theorem integral_difference_le_badEvent {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → E)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (B : Set Ω) (hB : NullMeasurableSet B P)
    (heq : ∀ᵐ p ∂P, p ∉ B → X p = Y p)
    (f : BoundedContinuousFunction E ℝ) :
    |(∫ p, f (X p) ∂P) - ∫ p, f (Y p) ∂P| ≤
      2 * ‖f‖ * P.real B := by
  have hiX : Integrable (fun p => f (X p)) P :=
    (f.integrable (P.map X)).comp_aemeasurable hX
  have hiY : Integrable (fun p => f (Y p)) P :=
    (f.integrable (P.map Y)).comp_aemeasurable hY
  let C := toMeasurable P B
  have hC : MeasurableSet C := measurableSet_toMeasurable P B
  have hi : Integrable (C.indicator (fun _ => (2 : ℝ) * ‖f‖)) P :=
    (integrable_const _).indicator hC
  have hb : ∀ᵐ p ∂P, ‖f (X p) - f (Y p)‖ ≤
      C.indicator (fun _ => (2 : ℝ) * ‖f‖) p := by
    filter_upwards [heq, hB.toMeasurable_ae_eq] with p hp hCp
    by_cases hpC : p ∈ C
    · rw [Set.indicator_of_mem hpC]
      exact (norm_sub_le _ _).trans (by
        linarith [f.norm_coe_le_norm (X p), f.norm_coe_le_norm (Y p)])
    · have hCp' : p ∈ C ↔ p ∈ B := iff_of_eq hCp
      have hpB : p ∉ B := fun hb => hpC (hCp'.mpr hb)
      simp only [hp hpB, sub_self, norm_zero, Set.indicator_of_not_mem hpC, le_refl]
  rw [← integral_sub hiX hiY, ← Real.norm_eq_abs]
  apply (norm_integral_le_of_norm_le hi hb).trans_eq
  rw [integral_indicator_const _ hC, smul_eq_mul]
  simp only [C, measureReal_def, measure_toMeasurable]
  ring

/-- Exact comparison marginals and a vanishing explicit exceptional-event
probability imply weak convergence of the actual laws. The exceptional event
is allowed to be merely null measurable, and equality need hold only almost
surely outside it. There is no compatibility requirement between rows. -/
theorem tendsto_imageLaw_of_badEvent
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Ω n → E)
    (hX : ∀ n, AEMeasurable (X n) (P n)) (hY : ∀ n, AEMeasurable (Y n) (P n))
    (B : ∀ n, Set (Ω n)) (hB : ∀ n, NullMeasurableSet (B n) (P n))
    (heq : ∀ n, ∀ᵐ p ∂P n, p ∉ B n → X n p = Y n p)
    (ν : ProbabilityMeasure E)
    (hlaw : ∀ᶠ n in atTop, (P n).map (Y n) = ν.toMeasure)
    (hbad : Tendsto (fun n => (P n).real (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => imageLaw (P n) (X n) (hX n)) atTop (𝓝 ν) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun n => 2 * ‖f‖ * (P n).real (B n)) atTop (𝓝 0) := by
    simpa using hbad.const_mul (2 * ‖f‖)
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [hlaw] with n hn
  have hye := integral_map (hY n) f.continuous.measurable.stronglyMeasurable.aestronglyMeasurable
  rw [hn] at hye
  change ‖(∫ x, f x ∂(P n).map (X n)) - ∫ x, f x ∂ν.toMeasure‖ ≤ _
  rw [integral_map (hX n) f.continuous.measurable.stronglyMeasurable.aestronglyMeasurable,
    hye, Real.norm_eq_abs]
  exact integral_difference_le_badEvent (P n) (X n) (Y n) (hX n) (hY n)
    (B n) (hB n) (heq n) f

/-- The same theorem accepts convergence of genuine extended event masses. -/
theorem tendsto_imageLaw_of_badEvent_measure
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Ω n → E)
    (hX : ∀ n, AEMeasurable (X n) (P n)) (hY : ∀ n, AEMeasurable (Y n) (P n))
    (B : ∀ n, Set (Ω n)) (hB : ∀ n, NullMeasurableSet (B n) (P n))
    (heq : ∀ n, ∀ᵐ p ∂P n, p ∉ B n → X n p = Y n p)
    (ν : ProbabilityMeasure E)
    (hlaw : ∀ᶠ n in atTop, (P n).map (Y n) = ν.toMeasure)
    (hbad : Tendsto (fun n => P n (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => imageLaw (P n) (X n) (hX n)) atTop (𝓝 ν) :=
  tendsto_imageLaw_of_badEvent P X Y hX hY B hB heq ν hlaw
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top |>.comp hbad)

end CarryingCapacity.CoupledPathLawConvergence
