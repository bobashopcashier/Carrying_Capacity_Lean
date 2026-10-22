import CarryingCapacity.PrescribedConfigurationProcess
import CarryingCapacity.PrescribedObservableLaws
import CarryingCapacity.ConfigurationRelabeling

/-!
# Exchangeability of the actual supplied particle system

An invariant initial configuration law and independent identically distributed
labelled Poisson measures imply exchangeability at every nonnegative time.
Actual noise relabeling and the coordinate counting equations prove path
equivariance; the reconstructed input law then transfers the result to the
supplied probability space. No output-law invariance is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.PrescribedConfigurationExchangeability
open ConfigurationLocalization CommonInitialNoise Symmetrization ParticleRelabeling
  ConfigurationRelabeling ExchangeableMatching

variable {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N)

/-- Relabel the whole initial configuration and every corresponding noise label. -/
def configurationSampleRelabel (e : Equiv.Perm (Fin N))
    (p : Sample (Configuration N D) (Label N D)) : Sample (Configuration N D) (Label N D) :=
  (relabel e p.1, noiseRelabel e p.2)

theorem measurable_configurationSampleRelabel (e : Equiv.Perm (Fin N)) :
    Measurable (configurationSampleRelabel (D := D) e) :=
  ((measurable_relabel e).comp measurable_fst).prodMk
    ((measurable_noiseRelabel e).comp measurable_snd)

theorem configurationSampleRelabel_preserving (μ : Measure (Configuration N D))
    [IsProbabilityMeasure μ]
    (hex : ExchangeableLaw μ) (e : Equiv.Perm (Fin N)) :
    MeasurePreserving (configurationSampleRelabel (D := D) e)
      (law μ (Label N D)) (law μ (Label N D)) := by
  have hi : MeasurePreserving (relabel e) μ μ := ⟨measurable_relabel e, hex e⟩
  exact hi.prod (noiseRelabel_preserving (J := Jump D) e)

variable (μ : Measure (Configuration N D)) [IsProbabilityMeasure μ]
  (hex : ExchangeableLaw μ) (hV : Integrable (lyapunov control) μ)
include hex hV

local notation "X" => ConfigurationTimeDependent.process control hN (id : Configuration N D → _)
local notation "pre" => ConfigurationTimeDependent.preState control hN (id : Configuration N D → _)
local notation "r" => ConfigurationTimeDependent.timeRate κ q hN

/-- Actual process equivariance follows from its supplied coordinate equations. -/
theorem ae_configuration_relabel (e : Equiv.Perm (Fin N)) :
    ∀ᵐ p ∂law μ (Label N D), ∀ t : ℝ, 0 ≤ t →
      X (configurationSampleRelabel e p) t = relabel e (X p t) := by
  have hexhaust := ConfigurationTimeDependent.ae_exhaustive control hN id μ measurable_id hV
  have hc := TimeDependentGlobalProcess.ae_process_cadlag (lyapunov control) (finite_sublevel control hN)
    jump r (ConfigurationTimeDependent.uniform_rate_bounds control hN) id 0 μ hexhaust
  have hp := ConfigurationTimeDependent.ae_tendsto_preState control hN id μ measurable_id hV
  have hz := ConfigurationTimeDependent.ae_initial control hN id μ
  have he : ∀ᵐ p ∂law μ (Label N D), ∀ i : Fin N × Fin D, ∀ T : ℝ≥0,
      (X p T i.1 i.2 : ℝ) - (p.1 i.1 i.2 : ℝ) =
        ∑ j, ∫ z, TimeDependentEquationUniqueness.increment jump r (pre p)
          (fun x => (x i.1 i.2 : ℝ)) j T z ∂MarkedNoise.countingMeasure j p.2 := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [ConfigurationTimeDependent.ae_counting_identity
      control hN id μ measurable_id hV (fun x => (x i.1 i.2 : ℝ))] with p hEq
    intro T
    simp only [id_eq] at hEq
    rw [hEq T]
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => TimeDependentGlobalCounting.horizonIncrement_apply
      (lyapunov control) (finite_sublevel control hN) jump r
      (ConfigurationTimeDependent.uniform_rate_bounds control hN) id 0
      (fun x => (x i.1 i.2 : ℝ)) j T p z)
  have hg := hc.and (hp.and (hz.and he))
  have hpres := configurationSampleRelabel_preserving μ hex e
  filter_upwards [hg,hpres.quasiMeasurePreserving.ae hg] with p hgood hgood'
  rcases hgood with ⟨hcad,hpre,hzero,heq⟩
  rcases hgood' with ⟨hcad',hpre',hzero',heq'⟩
  have hcont : Continuous (relabel e : Configuration N D → Configuration N D) :=
    continuous_of_discreteTopology
  apply TimeDependentEquationUniqueness.eq_of_separating_counting_equations
    (fun i : Fin N × Fin D => fun x : Configuration N D => (x i.1 i.2 : ℝ))
    (fun x y hxy => by
      funext i d
      have h : (x i d : ℝ) = (y i d : ℝ) := hxy (i,d)
      exact_mod_cast h) jump r
    (fun j => MarkedNoise.countingMeasure j (configurationSampleRelabel e p).2)
    (X (configurationSampleRelabel e p)) (fun t => relabel e (X p t))
    (pre (configurationSampleRelabel e p)) (fun t => relabel e (pre p t))
    hcad'.1 (fun t ht => hcont.continuousAt.comp_continuousWithinAt (hcad.1 t ht))
    hpre' (fun t ht => hcont.continuousAt.tendsto.comp (hpre t ht))
  · rw [hzero',hzero]
    rfl
  · intro i T hT
    rw [hzero']
    exact heq' i ⟨T,hT⟩
  · intro i T hT
    rw [hzero]
    change (X p T (e i.1) i.2 : ℝ) - (p.1 (e i.1) i.2 : ℝ) = _
    calc
      _ = ∑ j, ∫ z, TimeDependentEquationUniqueness.increment jump r (pre p)
          (fun x => (x (e i.1) i.2 : ℝ)) j T z ∂MarkedNoise.countingMeasure j p.2 :=
        heq (e i.1,i.2) ⟨T,hT⟩
      _ = ∑ j, ∫ z, TimeDependentEquationUniqueness.increment jump r (pre p)
          (fun x => (x (e i.1) i.2 : ℝ)) (labelEquiv e j) T z
          ∂MarkedNoise.countingMeasure (labelEquiv e j) p.2 :=
        (Equiv.sum_comp (labelEquiv e) _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [configurationSampleRelabel, countingMeasure_noiseRelabel]
        apply integral_congr_ae
        exact Eventually.of_forall (fun z =>
          (increment_relabel r e (interacting_rate_relabel hN e) (pre p)
            (fun x => (x i.1 i.2 : ℝ)) j T z).symm)

/-- Fixed-time exchangeability of the actual canonical configuration process. -/
theorem canonical_exchangeable (t : ℝ) (ht : 0 ≤ t) :
    ExchangeableLaw ((law μ (Label N D)).map (fun p => X p t)) := by
  intro e
  have hm : Measurable (fun p => X p t) :=
    (ConfigurationTimeDependent.measurable_process_at control hN id measurable_id t).mono
      ((filtration (Configuration N D) (Label N D)).le t) le_rfl
  have hs := configurationSampleRelabel_preserving μ hex e
  have he : (fun p => X (configurationSampleRelabel e p) t) =ᵐ[law μ (Label N D)]
      (fun p => relabel e (X p t)) :=
    (ae_configuration_relabel control hN μ hex hV e).mono (fun _ h => h t ht)
  calc
    ((law μ (Label N D)).map (fun p => X p t)).map (relabel e) =
        (law μ (Label N D)).map (fun p => relabel e (X p t)) :=
      Measure.map_map (measurable_relabel e) hm
    _ = (law μ (Label N D)).map (fun p => X (configurationSampleRelabel e p) t) :=
      Measure.map_congr he.symm
    _ = ((law μ (Label N D)).map (configurationSampleRelabel e)).map (fun p => X p t) :=
      (Measure.map_map hm hs.measurable).symm
    _ = (law μ (Label N D)).map (fun p => X p t) := by rw [hs.map_eq]

omit μ hex hV [IsProbabilityMeasure μ] in
/-- Proposition 3.4's exchangeability conclusion on the actual supplied probability space. -/
theorem supplied_exchangeable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Label N D → Ω → Measure (ℝ × ℝ)) (ξ : Ω → Configuration N D)
    (hM : ∀ j, Measurable (M j))
    (hPoisson : PoissonObservationLaw.HasDisjointLaws P (Label N D) M)
    (hξ : Measurable ξ) (hIndependent : IndepFun ξ (fun ω => fun j => M j ω) P)
    (hInitial : ExchangeableLaw (P.map ξ))
    (hMoment : Integrable (lyapunov control) (P.map ξ)) (t : ℝ) (ht : 0 ≤ t) :
    ExchangeableLaw (P.map (fun ω =>
      PrescribedConfigurationProcess.process control hN id M ξ ω t)) := by
  letI : IsProbabilityMeasure (P.map ξ) := isProbabilityMeasure_map hξ.aemeasurable
  have hm : Measurable (fun p : Sample (Configuration N D) (Label N D) => X p t) :=
    (ConfigurationTimeDependent.measurable_process_at control hN id measurable_id t).mono
      ((filtration (Configuration N D) (Label N D)).le t) le_rfl
  have he := PrescribedObservableLaws.map_comp (Label N D) M ξ P hM hPoisson hξ hIndependent
    (fun p => X p t) hm.aemeasurable
  change ExchangeableLaw (P.map (fun ω => X (PrescribedPoissonRealization.record (Label N D) M ξ ω) t))
  rw [he]
  exact canonical_exchangeable control hN (P.map ξ) hInitial hMoment t ht

end CarryingCapacity.PrescribedConfigurationExchangeability
