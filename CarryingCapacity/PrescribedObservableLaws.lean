import CarryingCapacity.PrescribedPoissonRealization

/-!
# Exact observable laws on the supplied Poisson space

The canonical input law is derived from genuine independent PRMs. Consequently
every AE-measurable path observable has the same distribution after realization,
including genuine uncountable running suprema and Borel path-valued observations.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CarryingCapacity.PrescribedObservableLaws
open PrescribedPoissonRealization

variable {Ω A E : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace E]
  (J : Type) [Fintype J] (M : J → Ω → Measure (ℝ × ℝ)) (ξ : Ω → A)
  (P : Measure Ω) [IsProbabilityMeasure P]
  (hM : ∀ j, Measurable (M j)) (hPoisson : PoissonObservationLaw.HasDisjointLaws P J M)
  (hξ : Measurable ξ) (hIndependent : IndepFun ξ (fun ω => fun j => M j ω) P)

include hM hPoisson hξ hIndependent

theorem aemeasurable_comp (F : CommonInitialNoise.Sample A J → E)
    (hF : AEMeasurable F (CommonInitialNoise.law (P.map ξ) J)) :
    AEMeasurable (fun ω => F (record J M ξ ω)) P :=
  hF.comp_quasiMeasurePreserving
    (measurePreserving_record J M ξ P hM hPoisson hξ hIndependent).quasiMeasurePreserving

/-- The exact distribution of the actual reconstructed observable. -/
theorem map_comp (F : CommonInitialNoise.Sample A J → E)
    (hF : AEMeasurable F (CommonInitialNoise.law (P.map ξ) J)) :
    P.map (fun ω => F (record J M ξ ω)) =
      (CommonInitialNoise.law (P.map ξ) J).map F := by
  have hm := measurable_record J M ξ hM hξ
  have he := record_map J M ξ P hM hPoisson hξ hIndependent
  have hF' : AEMeasurable F (P.map (record J M ξ)) := by rwa [he]
  exact (hF'.map_map_of_aemeasurable hm.aemeasurable).symm.trans
    (congrArg (Measure.map F) he)

/-- Null-measurable events suffice, so no measurable supremum is assumed. -/
theorem measure_preimage (S : Set (CommonInitialNoise.Sample A J))
    (hS : NullMeasurableSet S (CommonInitialNoise.law (P.map ξ) J)) :
    P ((record J M ξ) ⁻¹' S) = CommonInitialNoise.law (P.map ξ) J S := by
  have he := record_map J M ξ P hM hPoisson hξ hIndependent
  have hS' : NullMeasurableSet S (P.map (record J M ξ)) := by rwa [he]
  have h := Measure.map_apply₀ (measurable_record J M ξ hM hξ).aemeasurable hS'
  rw [he] at h
  exact h.symm

theorem measure_above (F : CommonInitialNoise.Sample A J → ℝ≥0∞)
    (hF : AEMeasurable F (CommonInitialNoise.law (P.map ξ) J)) (a : ℝ≥0∞) :
    P {ω | a < F (record J M ξ ω)} =
      CommonInitialNoise.law (P.map ξ) J {p | a < F p} :=
  measure_preimage J M ξ P hM hPoisson hξ hIndependent _
    (nullMeasurableSet_lt aemeasurable_const hF)

end CarryingCapacity.PrescribedObservableLaws
