import CarryingCapacity.UsualPoissonIndependence
import CarryingCapacity.IndependentIncrementCompensation

/-!
# Genuine supplied Poisson kernels in the usual filtration

The countable reconstructed atoms give an s-finite kernel on the completed
supplied space. On one probability-one event it is the specified random measure
itself, for every label and measurable set. Its unweighted intensity and full
future-count independence are proved from the primitive Poisson laws and the
independent initial record. Thus general predictable compensation applies
without assuming a compensator identity.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal NNReal

namespace CarryingCapacity.PrescribedCountingKernel
open PrescribedPoissonRealization PrescribedPoissonFiltration

variable {Ω A : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace A]
  (J : Type) [Fintype J] (M : J → Ω → Measure (ℝ × ℝ))
  (P : Measure Ω) (hM : ∀ j, Measurable (M j))

/-- The measurable countable-atom reconstruction is s-finite even on the
exceptional samples where a supplied random measure is not locally finite. -/
def countingKernel (j : J) :
    @Kernel Ω (ℝ × ℝ) (UsualFiltration.completedSpace P) inferInstance :=
  (MarkedCountingKernel.countingKernel j).comap (noise J M)
    ((measurable_noise J M hM).mono EventuallyMeasurableSpace.measurable_le le_rfl)

instance (j : J) : IsSFiniteKernel (countingKernel J M P hM j) := by
  unfold countingKernel
  infer_instance

theorem countingKernel_apply (j : J) (ω : Ω) :
    countingKernel J M P hM j ω = MarkedNoise.countingMeasure j (noise J M ω) :=
  MarkedCountingKernel.countingKernel_apply j (noise J M ω)

variable [IsProbabilityMeasure P]
  (hPoisson : PoissonObservationLaw.HasDisjointLaws P J M)
include hPoisson

/-- Equality of measures, simultaneously for every label, rather than
separate null events for individual test functions or sets. -/
theorem ae_countingKernel_eq : ∀ᵐ ω ∂UsualFiltration.completedLaw P, ∀ j,
    countingKernel J M P hM j ω = M j ω := by
  filter_upwards [ae_countingMeasure_noise J M P hM hPoisson] with ω hω
  exact fun j => (countingKernel_apply J M P hM j ω).trans (hω j)

/-- The unweighted expectation of every measurable count is its intensity. -/
theorem hasIntensity (j : J) :
    @IndependentIncrementCompensation.HasIntensity Ω (UsualFiltration.completedSpace P)
      (UsualFiltration.completedLaw P)
      (countingKernel J M P hM j) := by
  intro S hS
  simp only [countingKernel_apply]
  have hm : Measurable (fun ω : MarkedNoise.Sample J => MarkedNoise.countingMeasure j ω S) :=
    (Measure.measurable_coe hS).comp (MarkedNoise.measurable_countingMeasure j)
  have ht := lintegral_trim (μ := UsualFiltration.completedLaw P)
    (show mΩ ≤ UsualFiltration.completedSpace P from EventuallyMeasurableSpace.measurable_le)
    (hm.comp (measurable_noise J M hM))
  rw [UsualMartingale.trim_completedLaw] at ht
  simp only [Function.comp_def] at ht
  rw [← ht,← lintegral_map hm (measurable_noise J M hM),noise_map J M P hM hPoisson]
  exact MarkedIntensity.lintegral_counting_set j S hS

variable (ξ : Ω → A) (hξ : Measurable ξ)
  (hIndependent : IndepFun ξ (fun ω j => M j ω) P)
include hξ hIndependent

/-- All future bounded count observations are independent of the entire
usual natural past. This is a primitive independence result, not a weighted
compensation or stochastic-estimate assumption. -/
theorem futureCountsIndependent (j : J) :
    @IndependentIncrementCompensation.FutureCountsIndependent Ω (UsualFiltration.completedSpace P)
      (UsualFiltration.filtration P (rawFiltration J M ξ hM hξ))
      (UsualFiltration.completedLaw P) (countingKernel J M P hM j) := by
  intro s t m B hs hst hB hb
  have hi := UsualPoissonIndependence.independent_usual_window M ξ P hM hPoisson hξ hIndependent
    j m B hB hb s t hs hst
  apply (Indep_iff _ _ _).mpr
  intro S H hS hH
  obtain ⟨C,hC,rfl⟩ := hH
  have he : (fun ω => countingKernel J M P hM j ω (Ioc s t ×ˢ B)) ⁻¹' C =ᵐ[UsualFiltration.completedLaw P]
      (fun ω => M j ω (Ioc s t ×ˢ B)) ⁻¹' C := by
    filter_upwards [ae_countingKernel_eq J M P hM hPoisson] with ω hω
    exact congrArg (fun μ : Measure (ℝ × ℝ) => μ (Ioc s t ×ˢ B) ∈ C) (hω j)
  have heI : (S ∩ (fun ω => countingKernel J M P hM j ω (Ioc s t ×ˢ B)) ⁻¹' C : Set Ω)
      =ᵐ[UsualFiltration.completedLaw P]
      (S ∩ (fun ω => M j ω (Ioc s t ×ˢ B)) ⁻¹' C : Set Ω) := by
    filter_upwards [he] with ω hω
    exact congrArg (fun p : Prop => ω ∈ S ∧ p) hω
  rw [measure_congr heI,measure_congr he]
  exact (Indep_iff _ _ _).mp hi S _ hS ⟨C,hC,rfl⟩

/-- Full nonnegative predictable compensation for the specified measures
in their usual filtration, allowing infinite expectations. -/
theorem compensation_nonnegative (j : J) (f : Ω × (ℝ × ℝ) → ℝ≥0∞)
    (hf : Measurable[@PredictableSets.predictable Ω (UsualFiltration.completedSpace P)
      (UsualFiltration.filtration P (rawFiltration J M ξ hM hξ))] f) :
    (∫⁻ ω, ∫⁻ z, f (ω,z) ∂M j ω ∂UsualFiltration.completedLaw P) =
      ∫⁻ ω, ∫⁻ z, f (ω,z)
        ∂MarkedIntensity.positiveVolume.prod MarkedIntensity.positiveVolume
        ∂UsualFiltration.completedLaw P := by
  have hc := @IndependentIncrementCompensation.compensation_nonnegative Ω
    (UsualFiltration.completedSpace P)
    (UsualFiltration.filtration P (rawFiltration J M ξ hM hξ))
    (UsualFiltration.completedLaw P) inferInstance (countingKernel J M P hM j) inferInstance
    (hasIntensity J M P hM hPoisson j)
    (futureCountsIndependent J M P hM hPoisson ξ hξ hIndependent j) f hf
  refine (lintegral_congr_ae ?_).trans hc
  filter_upwards [ae_countingKernel_eq J M P hM hPoisson] with ω hω
  rw [hω j]

end CarryingCapacity.PrescribedCountingKernel
