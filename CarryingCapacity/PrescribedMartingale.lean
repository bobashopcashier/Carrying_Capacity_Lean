import CarryingCapacity.PrescribedPoissonFiltration
import CarryingCapacity.UsualMartingale

/-!
# Martingales on the supplied Poisson space

Every supplied past event is, modulo a null set, the pullback of a canonical
past event. This reverse causality statement is essential: measurability of
the reconstructed record alone would not establish martingale preservation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology NNReal

namespace CarryingCapacity.PrescribedMartingale
open PrescribedPoissonRealization PrescribedPoissonFiltration MarkedPastReconstruction

variable {Ω A : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace A]
  (J : Type) [Fintype J] (M : J → Ω → Measure (ℝ × ℝ)) (ξ : Ω → A)

def canonicalHistory (t : ℝ) (p : CommonInitialNoise.Sample A J) :
    A × (J → Measure (ℝ × ℝ)) :=
  (p.1,pastMeasures t (fun j => MarkedNoise.countingMeasure j p.2))

omit [Fintype J] in
theorem measurable_canonicalHistory (t : ℝ) :
    Measurable[CommonInitialNoise.filtration A J t] (canonicalHistory (A := A) J t) := by
  have hn : Measurable[CommonNoiseFiltration.filtration J t]
      (fun ω : MarkedNoise.Sample J => pastMeasures t (fun j => MarkedNoise.countingMeasure j ω)) :=
    (comap_measurable _).mono (countingHistory_le_filtration J t) le_rfl
  exact measurable_fst.prodMk (hn.comp measurable_snd)

variable (P : Measure Ω) [IsProbabilityMeasure P]
  (hM : ∀ j, Measurable (M j)) (hPoisson : PoissonObservationLaw.HasDisjointLaws P J M)
  (hξ : Measurable ξ) (hIndependent : IndepFun ξ (fun ω => fun j => M j ω) P)

include hM hPoisson

/-- Supplied raw past events pull back from genuine canonical past events. -/
theorem raw_event_pullback (t : ℝ) {S : Set Ω} (hS : MeasurableSet[rawAt J M ξ t] S) :
    ∃ B : Set (CommonInitialNoise.Sample A J),
      MeasurableSet[CommonInitialNoise.filtration A J t] B ∧
      S =ᵐ[P] (record J M ξ ⁻¹' B) := by
  obtain ⟨C,hC,rfl⟩ := hS
  refine ⟨canonicalHistory (A := A) J t ⁻¹' C,measurable_canonicalHistory J t hC,?_⟩
  filter_upwards [ae_countingMeasure_noise J M P hM hPoisson] with ω hω
  have he : canonicalHistory (A := A) J t (record J M ξ ω) = history J M ξ t ω := by
    simp only [canonicalHistory,record,history]
    exact congrArg (Prod.mk (ξ ω)) (congrArg (pastMeasures t) (funext hω))
  change (history J M ξ t ω ∈ C) = (canonicalHistory J t (record J M ξ ω) ∈ C)
  rw [he]

theorem completed_event_pullback (t : ℝ) {S : Set Ω}
    (hS : MeasurableSet[NullAugmentedIndependence.augmentation (rawAt J M ξ t) P] S) :
    ∃ B : Set (CommonInitialNoise.Sample A J),
      MeasurableSet[CommonInitialNoise.filtration A J t] B ∧
      S =ᵐ[P] (record J M ξ ⁻¹' B) := by
  obtain ⟨C,hC,he⟩ := hS
  obtain ⟨B,hB,he'⟩ := raw_event_pullback J M ξ P hM hPoisson t hC
  exact ⟨B,hB,he.trans he'⟩

include hξ hIndependent

theorem integral_realized (g : CommonInitialNoise.Sample A J → ℝ) (hg : Measurable g) :
    ∫ ω, g (record J M ξ ω) ∂P = ∫ p, g p ∂CommonInitialNoise.law (P.map ξ) J := by
  have hp := measurePreserving_record J M ξ P hM hPoisson hξ hIndependent
  have he := integral_map (μ := P) hp.measurable.aemeasurable hg.aestronglyMeasurable
  rw [hp.map_eq] at he
  exact he.symm

theorem setIntegral_realized (g : CommonInitialNoise.Sample A J → ℝ) (hg : Measurable g)
    {B : Set (CommonInitialNoise.Sample A J)} (hB : MeasurableSet B) :
    ∫ ω in record J M ξ ⁻¹' B, g (record J M ξ ω) ∂P =
      ∫ p in B, g p ∂CommonInitialNoise.law (P.map ξ) J := by
  rw [← integral_indicator (hB.preimage (measurable_record J M ξ hM hξ)),
    ← integral_indicator hB]
  have he := integral_realized J M ξ P hM hPoisson hξ hIndependent
    (B.indicator g) (hg.indicator hB)
  simpa only [← Set.indicator_comp_right,Function.comp_def] using he

theorem integrable_realized (g : CommonInitialNoise.Sample A J → ℝ)
    (hg : Integrable g (CommonInitialNoise.law (P.map ξ) J)) :
    Integrable (fun ω => g (record J M ξ ω)) P := by
  have hp := measurePreserving_record J M ξ P hM hPoisson hξ hIndependent
  have hg' : Integrable g (P.map (record J M ξ)) := hp.map_eq.symm ▸ hg
  exact (integrable_map_measure hg'.aestronglyMeasurable hp.measurable.aemeasurable).mp hg'

variable (X : ℝ≥0 → CommonInitialNoise.Sample A J → ℝ)
  (hX : Martingale X (UsualMartingale.nonnegative (CommonInitialNoise.filtration A J))
    (CommonInitialNoise.law (P.map ξ) J))
include hX

/-- The canonical martingale supplies the integral identity for every actual
completed supplied past event. -/
theorem setIntegral_completedAt {s t : ℝ≥0} (hst : s ≤ t) {S : Set Ω}
    (hS : MeasurableSet[UsualFiltration.completedAt P (rawFiltration J M ξ hM hξ) s] S) :
    (∫ ω in S, X s (record J M ξ ω) ∂UsualFiltration.completedLaw P) =
      ∫ ω in S, X t (record J M ξ ω) ∂UsualFiltration.completedLaw P := by
  letI : IsProbabilityMeasure (P.map ξ) := isProbabilityMeasure_map hξ.aemeasurable
  obtain ⟨B,hB,he⟩ := completed_event_pullback J M ξ P hM hPoisson s hS
  have hb : MeasurableSet B := (CommonInitialNoise.filtration A J).le s B hB
  have hm (u : ℝ≥0) : Measurable (X u) :=
    (hX.adapted u).measurable.mono ((CommonInitialNoise.filtration A J).le u) le_rfl
  have hs : MeasurableSet (record J M ξ ⁻¹' B) := hb.preimage (measurable_record J M ξ hM hξ)
  have he' : S =ᵐ[UsualFiltration.completedLaw P] (record J M ξ ⁻¹' B) := he
  rw [setIntegral_congr_set he',setIntegral_congr_set he',
    UsualMartingale.setIntegral_completedLaw P
      (show StronglyMeasurable (fun ω => X s (record J M ξ ω)) from
        ((hm s).comp (measurable_record J M ξ hM hξ)).stronglyMeasurable) hs,
    UsualMartingale.setIntegral_completedLaw P
      (show StronglyMeasurable (fun ω => X t (record J M ξ ω)) from
        ((hm t).comp (measurable_record J M ξ hM hξ)).stronglyMeasurable) hs,
    setIntegral_realized J M ξ P hM hPoisson hξ hIndependent (X s) (hm s) hb,
    setIntegral_realized J M ξ P hM hPoisson hξ hIndependent (X t) (hm t) hb]
  exact hX.setIntegral_eq hst hB

/-- A locally dominated, right-continuous canonical martingale is a genuine
martingale in the supplied completed right-continuous natural filtration. -/
theorem martingale_usual
    (hright : ∀ᵐ p ∂CommonInitialNoise.law (P.map ξ) J, ∀ s : ℝ≥0,
      ContinuousWithinAt (fun t => X t p) (Ici s) s)
    (hbound : ∀ T : ℝ≥0, ∃ b : CommonInitialNoise.Sample A J → ℝ,
      Integrable b (CommonInitialNoise.law (P.map ξ) J) ∧
      ∀ᵐ p ∂CommonInitialNoise.law (P.map ξ) J, ∀ t : ℝ≥0, t ≤ T → ‖X t p‖ ≤ b p) :
    Martingale (fun t ω => X t (record J M ξ ω))
      (UsualMartingale.usualNonnegative P (rawFiltration J M ξ hM hξ))
      (UsualFiltration.completedLaw P) := by
  let Q := UsualFiltration.completedLaw P
  let U := UsualMartingale.usualNonnegative P (rawFiltration J M ξ hM hξ)
  let Y := fun t ω => X t (record J M ξ ω)
  have hadapt : Adapted U Y := by
    intro t
    simpa only [Y,Real.toNNReal_coe] using (measurable_realized_at J M ξ P hM hPoisson hξ hIndependent
      (fun p u => X (Real.toNNReal u) p) t
      (by simpa only [Real.toNNReal_coe] using (hX.adapted t).measurable)).stronglyMeasurable
  have hint : ∀ t, Integrable (Y t) Q := fun t =>
    UsualMartingale.integrable_completedLaw P
      (integrable_realized J M ξ P hM hPoisson hξ hIndependent (X t) (hX.integrable t))
  have hrQ : ∀ᵐ ω ∂Q, ∀ s : ℝ≥0, ContinuousWithinAt (fun t => Y t ω) (Ici s) s :=
    ae_record J M ξ P hM hPoisson hξ hIndependent hright
  have hbQ : ∀ T : ℝ≥0, ∃ b : Ω → ℝ, Integrable b Q ∧
      ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → ‖Y t ω‖ ≤ b ω := by
    intro T
    obtain ⟨b,hb,hdom⟩ := hbound T
    exact ⟨fun ω => b (record J M ξ ω),UsualMartingale.integrable_completedLaw P
      (integrable_realized J M ξ P hM hPoisson hξ hIndependent b hb),
      ae_record J M ξ P hM hPoisson hξ hIndependent hdom⟩
  have hsets : ∀ (s u t : ℝ≥0), s < u → u ≤ t → ∀ S : Set Ω,
      MeasurableSet[U s] S → (∫ ω in S, Y u ω ∂Q) = ∫ ω in S, Y t ω ∂Q := by
    intro s u t hsu hut S hS
    exact setIntegral_completedAt J M ξ P hM hPoisson hξ hIndependent X hX hut
      (UsualFiltration.at_le_completedAt P (rawFiltration J M ξ hM hξ)
        (show (s : ℝ) < (u : ℝ) from hsu) S hS)
  letI : MeasurableSpace Ω := UsualFiltration.completedSpace P
  exact UsualMartingale.martingale_of_right_integrals Q U Y hadapt hint hrQ hbQ hsets

end CarryingCapacity.PrescribedMartingale
