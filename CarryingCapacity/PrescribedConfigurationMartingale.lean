import CarryingCapacity.PrescribedMartingale
import CarryingCapacity.ConfigurationUsualMartingale
import CarryingCapacity.PrescribedConfigurationProcess

/-!
# The supplied particle system solves the generator martingale problem

The statement uses the actual supplied Poisson measures and their completed
right-continuous natural filtration. The autonomous and time-dependent
constructions agree on one event for all nonnegative times; their current-state
generator expressions therefore agree too.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology NNReal

namespace CarryingCapacity.PrescribedConfigurationMartingale
open ConfigurationLocalization PrescribedPoissonRealization

variable {Ω A : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace A]
  {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N) (initial : A → Configuration N D)
  (F : Configuration N D → ℝ) (hF : (Function.support F).Finite)
  (M : Label N D → Ω → Measure (ℝ × ℝ)) (ξ : Ω → A)
  (P : Measure Ω) [IsProbabilityMeasure P]
  (hinit : Measurable initial) (hM : ∀ j, Measurable (M j)) (hξ : Measurable ξ)
  (hPoisson : PoissonObservationLaw.HasDisjointLaws P (Label N D) M)
  (hIndependent : IndepFun ξ (fun ω => fun j => M j ω) P)

def generatorProcess (t : ℝ≥0) (ω : Ω) : ℝ :=
  F (PrescribedConfigurationProcess.process control hN initial M ξ ω t) - F (initial (ξ ω)) -
    ∫ s in Ioc 0 (t : ℝ), generator κ q hN F
      (PrescribedConfigurationProcess.process control hN initial M ξ ω s) ∂MarkedIntensity.positiveVolume

include hF hinit hM hξ hPoisson hIndependent

/-- First the actual autonomous realization satisfies the martingale problem. -/
theorem autonomous_martingale :
    Martingale (fun t ω => ConfigurationMartingale.generatorProcess control hN initial F t
      (record (Label N D) M ξ ω))
      (UsualMartingale.usualNonnegative P
        (PrescribedPoissonFiltration.rawFiltration (Label N D) M ξ hM hξ))
      (UsualFiltration.completedLaw P) := by
  letI : IsProbabilityMeasure (P.map ξ) := isProbabilityMeasure_map hξ.aemeasurable
  apply PrescribedMartingale.martingale_usual (Label N D) M ξ P hM hPoisson hξ hIndependent
    (ConfigurationMartingale.generatorProcess control hN initial F)
    (ConfigurationMartingale.generator_martingale control hN initial F hF (P.map ξ) hinit)
    (ConfigurationUsualMartingale.ae_rightContinuous control hN initial F hF hinit (P.map ξ))
  intro T
  refine ⟨fun _ => 2 * FiniteSupportGeometry.functionBound F hF +
      FiniteSupportGeometry.generatorBound κ q hN F hF * T,
    integrable_const _, Filter.Eventually.of_forall (fun p t ht => ?_)⟩
  exact (ConfigurationUsualMartingale.norm_generatorProcess_le control hN initial F hF p t).trans
    (add_le_add_left (mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ T from ht)
      (ConfigurationUsualMartingale.generatorBound_nonnegative hN F hF)) _)

variable (hV : Integrable (fun a => lyapunov control (initial a)) (P.map ξ))
include hV

omit hF in
theorem ae_eq_autonomous (t : ℝ≥0) :
    generatorProcess control hN initial F M ξ t =ᵐ[P]
      (fun ω => ConfigurationMartingale.generatorProcess control hN initial F t
        (record (Label N D) M ξ ω)) := by
  letI : IsProbabilityMeasure (P.map ξ) := isProbabilityMeasure_map hξ.aemeasurable
  filter_upwards [PrescribedConfigurationProcess.ae_eq_autonomous control hN initial M ξ
    hinit hM hξ P hPoisson hIndependent (P.map ξ) rfl hV] with ω hω
  simp only [generatorProcess,ConfigurationMartingale.generatorProcess,record]
  rw [hω t t.coe_nonneg]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [hω s hs.1.le]
  rfl

omit [MeasurableSpace A] hF [IsProbabilityMeasure P] hinit hM hξ hPoisson hIndependent hV in
/-- Null modifications of a usual-adapted observable remain usual-adapted. -/
theorem measurable_usual_congr {E : Type*} [MeasurableSpace E]
    (G : Filtration ℝ mΩ) (t : ℝ) {f g : Ω → E}
    (hg : Measurable[UsualFiltration.usualAt P G t] g) (he : f =ᵐ[P] g) :
    Measurable[UsualFiltration.usualAt P G t] f := by
  intro S hS
  apply (UsualFiltration.measurableSet_at_iff P G t _).mpr
  intro u hu
  obtain ⟨B,hB,hB'⟩ :=
    (UsualFiltration.measurableSet_at_iff P G t _).mp (hg hS) u hu
  refine ⟨B,hB,Filter.EventuallyEq.trans ?_ hB'⟩
  filter_upwards [he] with ω hω
  change (f ω ∈ S) = (g ω ∈ S)
  rw [hω]

/-- Proposition 3.4's exact current-state finite-support generator expression
is a martingale in the prescribed completed right-continuous natural filtration. -/
theorem generator_martingale :
    Martingale (generatorProcess control hN initial F M ξ)
      (UsualMartingale.usualNonnegative P
        (PrescribedPoissonFiltration.rawFiltration (Label N D) M ξ hM hξ))
      (UsualFiltration.completedLaw P) := by
  have hm := autonomous_martingale control hN initial F hF M ξ P hinit hM hξ hPoisson hIndependent
  have he := ae_eq_autonomous control hN initial F M ξ P hinit hM hξ hPoisson hIndependent hV
  have hadapt : Adapted (UsualMartingale.usualNonnegative P
      (PrescribedPoissonFiltration.rawFiltration (Label N D) M ξ hM hξ))
      (generatorProcess control hN initial F M ξ) := by
    intro t
    exact (measurable_usual_congr P
      (PrescribedPoissonFiltration.rawFiltration (Label N D) M ξ hM hξ) t
      (hm.adapted t).measurable (he t)).stronglyMeasurable
  refine ⟨hadapt,fun s t hst => ?_⟩
  exact (condExp_congr_ae (μ := UsualFiltration.completedLaw P) (he t)).trans
    ((hm.condExp_ae_eq hst).trans (he s).symm)

end CarryingCapacity.PrescribedConfigurationMartingale
