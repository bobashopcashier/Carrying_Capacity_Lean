import CarryingCapacity.PoissonObservationLaw
import CarryingCapacity.CountingMeasureStrongFunction
import CarryingCapacity.MarkedPastReconstruction

/-!
# Realization on a supplied Poisson random-measure space

The input consists of genuine jointly independent Poisson counting measures
and an independent initial record. The canonical record is reconstructed as a
measurable function of those inputs. Its law and its exact counting measures
are proved from the finite disjoint-set laws, not supplied as assumptions.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal

namespace CarryingCapacity.PrescribedPoissonRealization
open MarkedNoiseObservation CountingMeasureStrongFunction

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  (J : Type) [Fintype J] (M : J → Ω → Measure (ℝ × ℝ))

/-- A deterministic function of the supplied random measures. -/
def noise (ω : Ω) : MarkedNoise.Sample J :=
  noiseFromMeasures J (fun j => M j ω)

theorem measurable_noise (hM : ∀ j, Measurable (M j)) : Measurable (noise J M) :=
  (measurable_noiseFromMeasures J).comp (measurable_pi_lambda _ hM)

variable (ξ : Ω → A)

/-- Retain the whole original initial record and reconstruct only the noise. -/
def record (ω : Ω) : CommonInitialNoise.Sample A J := (ξ ω, noise J M ω)

theorem measurable_record (hM : ∀ j, Measurable (M j)) (hξ : Measurable ξ) :
    Measurable (record J M ξ) := hξ.prodMk (measurable_noise J M hM)

variable (P : Measure Ω) [IsProbabilityMeasure P]
  (hM : ∀ j, Measurable (M j))
  (hPoisson : PoissonObservationLaw.HasDisjointLaws P J M)
include hM hPoisson

theorem noise_map : P.map (noise J M) = MarkedNoise.law J :=
  decode_map_of_observation_map J P _
    ((measurable_observeMeasures J).comp (measurable_pi_lambda _ hM))
    (PoissonObservationLaw.observation_map_eq P J M hM hPoisson)

/-- Every supplied measure is recovered, as an actual measure on one event. -/
theorem ae_countingMeasure_noise : ∀ᵐ ω ∂P, ∀ j,
    MarkedNoise.countingMeasure j (noise J M ω) = M j ω :=
  ae_countingMeasure_decode_eq J P _ (measurable_pi_lambda _ hM)
    (PoissonObservationLaw.observation_map_eq P J M hM hPoisson)

variable (hξ : Measurable ξ)
  (hIndependent : IndepFun ξ (fun ω => fun j => M j ω) P)
include hξ hIndependent

omit [IsProbabilityMeasure P] hM hPoisson hξ in
/-- Reconstructing the noise preserves its independence from the entire initial record. -/
theorem independent_initial_noise : IndepFun ξ (noise J M) P :=
  hIndependent.comp measurable_id (measurable_noiseFromMeasures J)

/-- The full initial/noise product law is derived from the supplied PRMs and
initial independence; it is not an extra realization hypothesis. -/
theorem record_map : P.map (record J M ξ) = CommonInitialNoise.law (P.map ξ) J := by
  have h := (indepFun_iff_map_prod_eq_prod_map_map hξ.aemeasurable
    (measurable_noise J M hM).aemeasurable).mp
      (independent_initial_noise J M ξ P hIndependent)
  rw [noise_map J M P hM hPoisson] at h
  exact h

theorem measurePreserving_record : MeasurePreserving (record J M ξ) P
    (CommonInitialNoise.law (P.map ξ) J) :=
  ⟨measurable_record J M ξ hM hξ, record_map J M ξ P hM hPoisson hξ hIndependent⟩

/-- Almost-sure canonical path properties transfer on the supplied probability
space, without needing measurability of the property itself. -/
theorem ae_record {Q : CommonInitialNoise.Sample A J → Prop}
    (hQ : ∀ᵐ p ∂CommonInitialNoise.law (P.map ξ) J, Q p) :
    ∀ᵐ ω ∂P, Q (record J M ξ ω) :=
  (measurePreserving_record J M ξ P hM hPoisson hξ hIndependent).quasiMeasurePreserving.ae hQ

end CarryingCapacity.PrescribedPoissonRealization
