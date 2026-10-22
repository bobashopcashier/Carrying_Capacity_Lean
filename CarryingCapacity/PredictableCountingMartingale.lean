import CarryingCapacity.InitialConditionalCompensation
import CarryingCapacity.PredictableHistoryTruncation

/-!
# A martingale from an actual predictable counting equation

This bridge takes an adapted observable and its pathwise counting equation.
Predictable product integrability supplies all required integrability, while
conditional compensation derives the martingale property. Neither a
martingale nor a conditional-mean identity is included among the inputs.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace CarryingCapacity.PredictableCountingMartingale
open CommonInitialNoise InitialPredictableCompensation InitialPredictableIntegral
  InitialConditionalCompensation PredictableSets MarkedIntensity

variable {A J : Type*} [MeasurableSpace A]
local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

/-- The actual initial-record plus marked-noise filtration at nonnegative times. -/
def nonnegativeFiltration (A J : Type*) [MeasurableSpace A] :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (Sample A J)) where
  seq t := filtration A J (t : ℝ)
  mono' := fun _ _ h => (filtration A J).mono h
  le' t := (filtration A J).le (t : ℝ)

variable [Fintype J]
  (X : ℝ≥0 → Sample A J → ℝ) (Y : Sample A J → ℝ)
  (H : J → SamplePoint A J → ℝ)

/-- The observable change minus its actual predictable intensity integral. -/
def compensated (t : ℝ≥0) (p : Sample A J) : ℝ :=
  X t p - Y p - ∑ j : J, ∫ q, window (H j) 0 t (p,q) ∂positiveVolume.prod positiveVolume

/-- The compensator uses only history up to the terminal time. -/
theorem adapted_compensated
    (hX : ∀ t : ℝ≥0, StronglyMeasurable[filtration A J t] (X t))
    (hY : StronglyMeasurable[filtration A J 0] Y)
    (hH : ∀ j, Measurable[predictable (filtration A J)] (H j)) :
    Adapted (nonnegativeFiltration A J) (compensated X Y H) := by
  intro t
  have hy : StronglyMeasurable[filtration A J t] Y :=
    hY.mono ((filtration A J).mono t.coe_nonneg)
  have hi : StronglyMeasurable[filtration A J t]
      (fun p => ∑ j : J, ∫ q, window (H j) 0 t (p,q) ∂positiveVolume.prod positiveVolume) := by
    apply Finset.stronglyMeasurable_sum
    intro j _
    exact (PredictableHistoryTruncation.measurable_intensityIntegral
      (filtration A J) (H j) (hH j) (positiveVolume.prod positiveVolume) 0 t).stronglyMeasurable
  exact ((hX t).sub hy).sub hi

variable (μ : Measure A) [IsProbabilityMeasure μ]
  (hH : ∀ j, Measurable[predictable (filtration A J)] (H j))
  (hI : ∀ j (t : ℝ≥0), Integrable (window (H j) 0 t) (productIntensity μ J))
  (hcount : ∀ t : ℝ≥0, (fun p => X t p - Y p) =ᵐ[law μ J]
    (fun p => ∑ j : J, ∫ q, window (H j) 0 t (p,q) ∂MarkedNoise.countingMeasure j p.2))

include hcount

omit [IsProbabilityMeasure μ] in
/-- The pathwise counting equation identifies the compensated observable
with the sum of the actual compensated counting integrals. -/
theorem ae_compensated_eq_sum (t : ℝ≥0) :
    compensated X Y H t =ᵐ[law μ J]
      (fun p => ∑ j : J, compensatedWindow j (H j) 0 t p) := by
  filter_upwards [hcount t] with p hp
  simp only [compensated, compensatedWindow, Finset.sum_sub_distrib]
  rw [hp]

include hH hI

/-- Integrability follows from the actual integrands and counting equation,
without a separate integrability assumption on the observable. -/
theorem integrable_compensated (t : ℝ≥0) :
    Integrable (compensated X Y H t) (law μ J) :=
  (integrable_finset_sum Finset.univ (fun j _ =>
    integrable_compensatedWindow μ j (H j) (hH j) 0 t le_rfl (hI j t))).congr
      (ae_compensated_eq_sum X Y H μ hcount t).symm

/-- Observable increments coincide with actual future-window compensated integrals. -/
theorem ae_compensated_sub (s t : ℝ≥0) (hst : s ≤ t) :
    (compensated X Y H t - compensated X Y H s) =ᵐ[law μ J]
      (fun p => ∑ j : J, compensatedWindow j (H j) s t p) := by
  filter_upwards [ae_compensated_eq_sum X Y H μ hcount t,
    ae_compensated_eq_sum X Y H μ hcount s,
    ae_all_iff.mpr (fun j => ae_compensated_prefix_sub μ j (H j) (hH j)
      s t s.coe_nonneg hst (hI j s) (hI j t))] with p ht hs hw
  simp only [Pi.sub_apply, ht, hs, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ => hw j)

/-- Conditional zero mean is derived for the actual observable increment. -/
theorem conditional_compensated_sub (s t : ℝ≥0) (hst : s ≤ t) :
    (law μ J)[compensated X Y H t - compensated X Y H s | nonnegativeFiltration A J s]
      =ᵐ[law μ J] fun _ => (0 : ℝ) := by
  have hi (j : J) := integrable_window_of_prefixes μ (H j) s t s.coe_nonneg hst (hI j s) (hI j t)
  have hsum := condExp_finset_sum (s := Finset.univ)
    (f := fun j => compensatedWindow j (H j) s t)
    (fun j _ => integrable_compensatedWindow μ j (H j) (hH j) s t s.coe_nonneg (hi j))
    (nonnegativeFiltration A J s)
  have he : (fun p => ∑ j : J, compensatedWindow j (H j) s t p) =
      ∑ j : J, compensatedWindow j (H j) s t := by
    funext p
    simp only [Finset.sum_apply]
  have hc := condExp_congr_ae (m := nonnegativeFiltration A J s) (ae_compensated_sub X Y H μ hH hI hcount s t hst)
  rw [he] at hc
  apply hc.trans
  apply hsum.trans
  filter_upwards [ae_all_iff.mpr (fun j => conditional_compensatedWindow
    μ j (H j) (hH j) s t s.coe_nonneg (hi j))] with p hp
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero (fun j _ => hp j)

/-- The counting equation and actual compensation imply the martingale property. -/
theorem martingale_compensated
    (hX : ∀ t : ℝ≥0, StronglyMeasurable[filtration A J t] (X t))
    (hY : StronglyMeasurable[filtration A J 0] Y) :
    Martingale (compensated X Y H) (nonnegativeFiltration A J) (law μ J) := by
  refine ⟨adapted_compensated X Y H hX hY hH, ?_⟩
  intro s t hst
  have hzero := conditional_compensated_sub X Y H μ hH hI hcount s t hst
  have hsub := condExp_sub (integrable_compensated X Y H μ hH hI hcount t)
    (integrable_compensated X Y H μ hH hI hcount s) (nonnegativeFiltration A J s)
  rw [condExp_of_stronglyMeasurable ((nonnegativeFiltration A J).le s)
    (adapted_compensated X Y H hX hY hH s) (integrable_compensated X Y H μ hH hI hcount s)] at hsub
  filter_upwards [hzero, hsub] with p hzero hsub
  simp only [Pi.sub_apply] at hsub
  linarith

end CarryingCapacity.PredictableCountingMartingale
