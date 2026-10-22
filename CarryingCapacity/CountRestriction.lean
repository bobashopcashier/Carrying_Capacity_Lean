import CarryingCapacity.MarkedThinning

/-!
# Restricted count laws from weighted power transforms

A power-transform identity on a measurable event identifies the actual
restricted pushforward measure, including events of probability zero. No
conditional probability or division by the event's mass is used.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace CarryingCapacity.CountRestriction

variable {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsFiniteMeasure μ]
  (X : Ω → ℕ) (hX : Measurable X) (C : Set Ω) (hC : MeasurableSet C)
  (ν : Measure ℕ) [IsFiniteMeasure ν]

include hX hC

/-- Weighted power transforms determine the exact count law restricted to an event. -/
theorem map_restrict_eq_smul_of_pow_integrals
    (h : ∀ z : ℂ, ‖z‖ ≤ 1 →
      (∫ ω, C.indicator (fun ω => z ^ X ω) ω ∂μ) =
        (μ.real C : ℂ) * (∫ n, z ^ n ∂ν)) :
    (μ.restrict C).map X = μ C • ν := by
  letI : IsFiniteMeasure (μ C • ν) := ν.smul_finite (measure_ne_top μ C)
  apply MarkedThinning.natMeasure_eq_of_pow_integrals
  intro z hz
  rw [integral_map_of_stronglyMeasurable hX (measurable_of_countable _).stronglyMeasurable,
    ← integral_indicator hC, integral_smul_measure, Complex.real_smul]
  exact h z hz

/-- The resulting factorization holds for every set of natural counts. -/
theorem measure_inter_preimage_of_pow_integrals
    (h : ∀ z : ℂ, ‖z‖ ≤ 1 →
      (∫ ω, C.indicator (fun ω => z ^ X ω) ω ∂μ) =
        (μ.real C : ℂ) * (∫ n, z ^ n ∂ν)) (D : Set ℕ) :
    μ (C ∩ X ⁻¹' D) = μ C * ν D := by
  have hD : MeasurableSet D := D.to_countable.measurableSet
  have hm := congrArg (fun ρ : Measure ℕ => ρ D)
    (map_restrict_eq_smul_of_pow_integrals μ X hX C hC ν h)
  dsimp only at hm
  rw [Measure.map_apply hX hD, Measure.restrict_apply (hX hD), Measure.smul_apply] at hm
  simpa only [Set.inter_comm, smul_eq_mul] using hm

/-- An equivalent input form uses the scalar event indicator times the count power. -/
theorem map_restrict_eq_smul_of_indicator_mul_pow_integrals
    (h : ∀ z : ℂ, ‖z‖ ≤ 1 →
      (∫ ω, C.indicator (fun _ => (1 : ℂ)) ω * z ^ X ω ∂μ) =
        (μ.real C : ℂ) * (∫ n, z ^ n ∂ν)) :
    (μ.restrict C).map X = μ C • ν := by
  apply map_restrict_eq_smul_of_pow_integrals μ X hX C hC ν
  intro z hz
  convert h z hz using 1
  congr 1
  funext ω
  by_cases hω : ω ∈ C <;> simp [hω]

theorem measure_inter_preimage_of_indicator_mul_pow_integrals
    (h : ∀ z : ℂ, ‖z‖ ≤ 1 →
      (∫ ω, C.indicator (fun _ => (1 : ℂ)) ω * z ^ X ω ∂μ) =
        (μ.real C : ℂ) * (∫ n, z ^ n ∂ν)) (D : Set ℕ) :
    μ (C ∩ X ⁻¹' D) = μ C * ν D := by
  have hD : MeasurableSet D := D.to_countable.measurableSet
  have hm := congrArg (fun ρ : Measure ℕ => ρ D)
    (map_restrict_eq_smul_of_indicator_mul_pow_integrals μ X hX C hC ν h)
  dsimp only at hm
  rw [Measure.map_apply hX hD, Measure.restrict_apply (hX hD), Measure.smul_apply] at hm
  simpa only [Set.inter_comm, smul_eq_mul] using hm

end CarryingCapacity.CountRestriction
