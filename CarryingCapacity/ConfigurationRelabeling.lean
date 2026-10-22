import CarryingCapacity.ParticleRelabeling
import CarryingCapacity.PopulationCouplingInitialization
import CarryingCapacity.ConfigurationTimeDependent
import CarryingCapacity.DeterministicEnvironmentConfiguration
import CarryingCapacity.TimeDependentEquationUniqueness

/-!
# Relabeling the actual interacting and comparison paths

Simultaneous permutation of a paired initial record and its particle noises
permutes both constructed configuration paths. The argument transports their
actual counting equations and applies pathwise uniqueness. In particular,
no invariance of classically chosen localization bounds is required.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.ConfigurationRelabeling
open CommonInitialNoise ConfigurationLocalization Symmetrization
open ParticleRelabeling PopulationCouplingInitialization

variable {N D : ℕ}

/-- Updating a relabeled configuration is the relabeling of the corresponding
original-label update, including boundary deaths. -/
theorem jump_relabel (e : Equiv.Perm (Fin N)) (j : Label N D) (z : Configuration N D) :
    jump j (relabel e z) = relabel e (jump (labelEquiv e j) z) := by
  simp only [labelEquiv_apply, jump, relabel_update,
    Prod.fst, Prod.snd, Equiv.symm_apply_apply, relabel_apply]

/-- Relabeling leaves the empirical law and hence the empirical feedback unchanged. -/
theorem interacting_rate_relabel {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
    (hN : 0 < N) (e : Equiv.Perm (Fin N)) (j : Label N D) (t : ℝ) (z : Configuration N D) :
    ConfigurationTimeDependent.timeRate κ q hN j t (relabel e z) =
      ConfigurationTimeDependent.timeRate κ q hN (labelEquiv e j) t z := by
  simp only [ConfigurationTimeDependent.timeRate_apply, relabel,
    empiricalLaw_relabel, labelEquiv, Equiv.prodCongr_apply, Equiv.refl_apply]
  rfl

/-- The externally prescribed environment is unaffected by particle relabeling. -/
theorem environment_rate_relabel {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
    (v : ℝ → MomentLaw κ D) (T : ℝ) (e : Equiv.Perm (Fin N))
    (j : Label N D) (t : ℝ) (z : Configuration N D) :
    DeterministicEnvironmentConfiguration.rate κ q v T j t (relabel e z) =
      DeterministicEnvironmentConfiguration.rate κ q v T (labelEquiv e j) t z := rfl

/-- Structural symmetry of the unrestricted integrand. The transformed test
reads precisely the coordinate selected by the particle permutation. -/
theorem increment_relabel (rate : Label N D → ℝ → Configuration N D → ℝ)
    (e : Equiv.Perm (Fin N))
    (hrate : ∀ j t z, rate j t (relabel e z) = rate (labelEquiv e j) t z)
    (pre : ℝ → Configuration N D) (f : Configuration N D → ℝ)
    (j : Label N D) (S : ℝ) (r : ℝ × ℝ) :
    TimeDependentEquationUniqueness.increment jump rate (fun t => relabel e (pre t)) f j S r =
      TimeDependentEquationUniqueness.increment jump rate pre (fun z => f (relabel e z))
        (labelEquiv e j) S r := by
  simp only [TimeDependentEquationUniqueness.increment, hrate, jump_relabel]

section ActualConstruction
variable {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N)
  (rate : Label N D → ℝ → Configuration N D → ℝ)
  (hbound : ∀ n : ℕ, ∃ C : ℝ,
    ∀ z ∈ LyapunovLocalization.active (lyapunov control) (finite_sublevel control hN) n,
      ∀ j t, rate j t z ≤ C)
  (initial : Record N D → Configuration N D)
  (γ : Measure (Record N D)) [IsProbabilityMeasure γ]
  (hex : ExchangeableMatching.ExchangeableLaw γ)

local notation "V" => lyapunov control
local notation "hf" => finite_sublevel control hN
local notation "P" => TimeDependentGlobalProcess.process V hf jump rate hbound initial 0
local notation "pre" => TimeDependentGlobalCounting.preState V hf jump rate hbound initial 0

include hex

/-- Generic relabeling of the actual patch under structural coefficient and
initial-map symmetries. Genuine exit exhaustion supplies the path equations
and regularity; the paper-specific wrappers below derive it from Lyapunov drift. -/
theorem ae_process_relabel
    (hexhaust : ∀ᵐ p ∂law γ (Label N D), ∀ S : ℝ≥0, ∃ n,
      (S : ℝ≥0∞) < TimeDependentLocalization.exit V hf jump rate hbound initial n p)
    (e : Equiv.Perm (Fin N))
    (hrate : ∀ j t z, rate j t (relabel e z) = rate (labelEquiv e j) t z)
    (hinitial : ∀ a, initial (relabel e a) = relabel e (initial a)) :
    ∀ᵐ p ∂law γ (Label N D), ∀ t : ℝ, 0 ≤ t →
      P (sampleRelabel e p) t = relabel e (P p t) := by
  have hc := TimeDependentGlobalProcess.ae_process_cadlag V hf jump rate hbound initial 0 γ hexhaust
  have hp := TimeDependentGlobalCounting.ae_tendsto_preState V hf jump rate hbound initial 0 γ hexhaust
  have hz := TimeDependentGlobalProcess.ae_process_zero V hf jump rate hbound initial 0 γ
  have he : ∀ᵐ p ∂law γ (Label N D), ∀ i : Fin N × Fin D, ∀ S : ℝ≥0,
      (P p S i.1 i.2 : ℝ) - (initial p.1 i.1 i.2 : ℝ) =
        ∑ j, ∫ r, TimeDependentEquationUniqueness.increment jump rate (pre p)
          (fun z => (z i.1 i.2 : ℝ)) j S r ∂MarkedNoise.countingMeasure j p.2 := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [TimeDependentGlobalCounting.ae_testFunction_counting_identity V hf jump rate hbound initial 0 γ
      (fun z => (z i.1 i.2 : ℝ)) hexhaust] with p heq
    intro S
    rw [heq S]
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    exact Eventually.of_forall (fun r => TimeDependentGlobalCounting.horizonIncrement_apply
      V hf jump rate hbound initial 0 (fun z => (z i.1 i.2 : ℝ)) j S p r)
  have hgood := hc.and (hp.and (hz.and he))
  have hpres := sampleRelabel_preserving (J := Jump D) e γ hex
  filter_upwards [hgood, hpres.quasiMeasurePreserving.ae hgood] with p hg hg'
  rcases hg with ⟨hcad, hpre, hzero, heq⟩
  rcases hg' with ⟨hcad', hpre', hzero', heq'⟩
  have hcont : Continuous (relabel e : Configuration N D → Configuration N D) := continuous_of_discreteTopology
  apply TimeDependentEquationUniqueness.eq_of_separating_counting_equations
    (fun i : Fin N × Fin D => fun z : Configuration N D => (z i.1 i.2 : ℝ))
    (fun x y hxy => by
      funext i d
      have heq : (x i d : ℝ) = (y i d : ℝ) := hxy (i,d)
      exact_mod_cast heq) jump rate
    (fun j => MarkedNoise.countingMeasure j (sampleRelabel e p).2)
    (P (sampleRelabel e p)) (fun t => relabel e (P p t))
    (pre (sampleRelabel e p)) (fun t => relabel e (pre p t))
    hcad'.1 (fun t ht => hcont.continuousAt.comp_continuousWithinAt (hcad.1 t ht))
    hpre' (fun t ht => hcont.continuousAt.tendsto.comp (hpre t ht))
  · rw [hzero', hzero]
    exact hinitial p.1
  · intro i s hs
    rw [hzero']
    exact heq' i ⟨s,hs⟩
  · intro i s hs
    rw [hzero]
    change (P p s (e i.1) i.2 : ℝ) - (initial p.1 (e i.1) i.2 : ℝ) = _
    calc
      _ = ∑ j, ∫ r, TimeDependentEquationUniqueness.increment jump rate (pre p)
          (fun z => (z (e i.1) i.2 : ℝ)) j s r ∂MarkedNoise.countingMeasure j p.2 :=
        heq (e i.1, i.2) ⟨s,hs⟩
      _ = ∑ j, ∫ r, TimeDependentEquationUniqueness.increment jump rate (pre p)
          (fun z => (z (e i.1) i.2 : ℝ)) (labelEquiv e j) s r
          ∂MarkedNoise.countingMeasure (labelEquiv e j) p.2 :=
        (Equiv.sum_comp (labelEquiv e) _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [sampleRelabel_snd, countingMeasure_noiseRelabel]
        apply integral_congr_ae
        exact Eventually.of_forall (fun r =>
          (increment_relabel rate e hrate (pre p) (fun z => (z i.1 i.2 : ℝ)) j s r).symm)

end ActualConstruction

section Interacting
variable {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N)
  (γ : Measure (Record N D)) [IsProbabilityMeasure γ]
  (hex : ExchangeableMatching.ExchangeableLaw γ)
  (hInitialX : Integrable (fun a => lyapunov control (left a)) γ)
include hex hInitialX

/-- The actual interacting configuration is equivariant on the original
paired-record/noise space, on one event at every nonnegative time. -/
theorem ae_interacting_relabel (e : Equiv.Perm (Fin N)) :
    ∀ᵐ p ∂law γ (Label N D), ∀ t : ℝ, 0 ≤ t →
      ConfigurationTimeDependent.process control hN left (sampleRelabel e p) t =
        relabel e (ConfigurationTimeDependent.process control hN left p t) :=
  ae_process_relabel control hN (ConfigurationTimeDependent.timeRate κ q hN)
    (ConfigurationTimeDependent.uniform_rate_bounds control hN) left γ hex
    (ConfigurationTimeDependent.ae_exhaustive control hN left γ measurable_left hInitialX) e
    (interacting_rate_relabel hN e) (fun _ => rfl)

end Interacting

section Environment
variable {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N) (hActivity : MomentActivityBound κ q)
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))
  (γ : Measure (Record N D)) [IsProbabilityMeasure γ]
  (hex : ExchangeableMatching.ExchangeableLaw γ)
  (hCoupling : MomentCouplingBound κ q) (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ t ∈ Icc 0 T, LyapunovFlowSpace.lyapunovIntegral control.function (v t) ≤ ENNReal.ofReal B)
  (hInitialY : Integrable (fun a => lyapunov control (right a)) γ)
include hex hCoupling hB hEnv hInitialY

/-- The prescribed-environment comparison configuration has the same exact
path symmetry, including the endpoint-held continuation after the horizon. -/
theorem ae_environment_relabel (e : Equiv.Perm (Fin N)) :
    ∀ᵐ p ∂law γ (Label N D), ∀ t : ℝ, 0 ≤ t →
      DeterministicEnvironmentConfiguration.process control hN hActivity v T hT hv right (sampleRelabel e p) t =
        relabel e (DeterministicEnvironmentConfiguration.process control hN hActivity v T hT hv right p t) :=
  ae_process_relabel control hN (DeterministicEnvironmentConfiguration.rate κ q v T)
    (DeterministicEnvironmentConfiguration.exists_uniform_rate_bounds control hN hActivity v T hT hv)
    right γ hex
    (DeterministicEnvironmentConfiguration.ae_exhaustive control hN hActivity v T hT hv right γ
      hCoupling measurable_right B hB hEnv hInitialY) e
    (environment_rate_relabel v T e) (fun _ => rfl)

end Environment
end CarryingCapacity.ConfigurationRelabeling
