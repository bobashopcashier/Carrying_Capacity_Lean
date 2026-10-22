import CarryingCapacity.NonlinearSkorokhodArray
import CarryingCapacity.PopulationFixedTimeChaos

/-!
# Focal chaos in the genuine vector-valued J1 path space

The limit is the law of k independent actual nonlinear trajectories viewed as
one path in the finite product state space. All coordinates therefore share a
single J1 time change. The actual synchronous coupling makes the entire paths
identical outside an explicit focal discrepancy event of vanishing probability.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal NNReal

namespace CarryingCapacity.PopulationPathChaos
open CommonInitialNoise ConfigurationLocalization PopulationCouplingInitialization SkorokhodJ1

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}

theorem uniformContinuous_first {N : ℕ} (k : ℕ) :
    UniformContinuous (PopulationFixedTimeChaos.first (N := N) (D := D) k) := by
  apply uniformContinuous_pi.mpr
  intro i
  by_cases h : i.val < N
  · have hm : UniformContinuous (fun z : Configuration N D => z ⟨i.val, h⟩) :=
      uniformContinuous_pi.mp uniformContinuous_id _
    simpa only [PopulationFixedTimeChaos.first, dif_pos h] using hm
  · simpa only [PopulationFixedTimeChaos.first, dif_neg h] using
      (uniformContinuous_const : UniformContinuous (fun _ : Configuration N D => (0 : State D)))

/-- First-k projection with the manuscript adapted state metric. -/
def adaptedFirst {N : ℕ} (κ : MomentScale) (k : ℕ) (z : Configuration N D) :
    Fin k → AdaptedState κ D :=
  (AdaptedState.piUniformEquiv κ D k).symm (PopulationFixedTimeChaos.first k z)

theorem uniformContinuous_adaptedFirst {N : ℕ} (κ : MomentScale) (k : ℕ) :
    UniformContinuous (adaptedFirst (N := N) (D := D) κ k) :=
  (AdaptedState.piUniformEquiv κ D k).symm.uniformContinuous.comp (uniformContinuous_first k)

variable (control : LyapunovControl κ q)

/-- The actual interacting first-k path, including the terminal value. -/
def interactingPath {A : Type*} [MeasurableSpace A] {N : ℕ} (hN : 0 < N)
    (initial : A → Configuration N D) (T : ℝ≥0) (k : ℕ)
    (p : Sample A (Label N D)) : Path T (Fin k → AdaptedState κ D) :=
  (CanonicalSkorokhodPaths.configurationPath control hN initial T p).map (adaptedFirst κ k)
    (uniformContinuous_adaptedFirst κ k).continuous

theorem aemeasurable_interactingPath {A : Type*} [MeasurableSpace A] {N : ℕ} (hN : 0 < N)
    (initial : A → Configuration N D) (T : ℝ≥0) (k : ℕ)
    (μ : Measure A) [IsProbabilityMeasure μ] (hinit : Measurable initial)
    (hV : Integrable (fun a => lyapunov control (initial a)) μ) :
    AEMeasurable (interactingPath control hN initial T k) (law μ (Label N D)) :=
  (measurable_path_map (adaptedFirst κ k) (uniformContinuous_adaptedFirst κ k)).comp_aemeasurable
    (CanonicalSkorokhodPaths.aemeasurable_configurationPath control hN initial T μ hinit hV)

theorem ae_interactingPath_apply {A : Type*} [MeasurableSpace A] {N : ℕ} (hN : 0 < N)
    (initial : A → Configuration N D) (T : ℝ≥0) (k : ℕ)
    (μ : Measure A) [IsProbabilityMeasure μ] (hinit : Measurable initial)
    (hV : Integrable (fun a => lyapunov control (initial a)) μ) :
    ∀ᵐ p ∂law μ (Label N D), ∀ t : Time T,
      interactingPath control hN initial T k p t =
        adaptedFirst κ k (ConfigurationTimeDependent.process control hN initial p t) := by
  filter_upwards [CanonicalSkorokhodPaths.ae_configurationPath_apply control hN initial T μ hinit hV]
    with p hp
  intro t
  exact congrArg (adaptedFirst κ k) (hp t)

variable (hActivity : MomentActivityBound κ q) (ν : MomentLaw κ D) (T : ℝ≥0)
  (hCoupling : MomentCouplingBound κ q) (hMoment : Integrable control.function ν.measure)

local notation "v" => NonlinearFixedPoint.environment control hActivity ν T T.coe_nonneg hCoupling hMoment
local notation "hv" => Continuous.continuousOn (NonlinearFixedPoint.continuous_environment control hActivity ν T T.coe_nonneg hCoupling hMoment)

/-- A concrete null-measurable focal event; no measurability of path inequality is
used in the law comparison. -/
def badEvent (n k : ℕ) : Set (Sample (Record (n + 1) D) (Label (n + 1) D)) :=
  {p | ENNReal.ofReal (1 / 2 : ℝ) < PopulationFocalApproximation.focalPathDiscrepancy
    control hActivity ν T T.coe_nonneg hCoupling hMoment n k T p}

theorem nullMeasurable_badEvent (n k : ℕ)
    (γ : Measure (Record (n + 1) D)) [IsProbabilityMeasure γ]
    (hright : γ.map right = Measure.pi (fun _ : Fin (n + 1) => ν.measure))
    (hV : Integrable (fun a => lyapunov control (left a)) γ) :
    NullMeasurableSet (badEvent control hActivity ν T hCoupling hMoment n k)
      (law γ (Label (n + 1) D)) := by
  have hIY := NonlinearParticleConfiguration.integrable_initial_lyapunov control ν hMoment
    right measurable_right γ hright
  have hm := PopulationFocalProbability.aemeasurable_focalRunningCost control (Nat.succ_pos n)
    hActivity v T T.coe_nonneg hv left right γ hCoupling measurable_left measurable_right
    (PopulationStoppedGronwall.environmentBound control ν T)
    (PopulationStoppedGronwall.environmentBound_nonnegative control ν T T.coe_nonneg)
    (PopulationStoppedGronwall.environment_lyapunov_le_bound control hActivity ν T T.coe_nonneg hCoupling hMoment)
    hV hIY (PopulationFocalProbability.focalIndices (n + 1) k) T
  exact hm.nullMeasurable measurableSet_Ioi

/-- On one common full-probability event, absence of the focal discrepancy
forces equality of the entire vector-valued paths, not merely fixed-time laws. -/
theorem ae_paths_eq_outside_badEvent (n k : ℕ) (hkn : k ≤ n + 1)
    (γ : Measure (Record (n + 1) D)) [IsProbabilityMeasure γ]
    (hright : γ.map right = Measure.pi (fun _ : Fin (n + 1) => ν.measure))
    (hV : Integrable (fun a => lyapunov control (left a)) γ) :
    ∀ᵐ p ∂law γ (Label (n + 1) D),
      p ∉ badEvent control hActivity ν T hCoupling hMoment n k →
        interactingPath control (Nat.succ_pos n) left T k p =
          NonlinearSkorokhodArray.comparison control hActivity ν T hCoupling hMoment right k p := by
  filter_upwards [ae_interactingPath_apply control (Nat.succ_pos n) left T k γ measurable_left hV,
    NonlinearSkorokhodArray.ae_comparison_apply control hActivity ν T hCoupling hMoment
      right measurable_right γ hright hkn,
    NonlinearParticleConfiguration.ae_path_eq_configuration control hActivity ν T T.coe_nonneg
      hCoupling hMoment right measurable_right γ hright (Nat.succ_pos n)] with p hp hcomp hY
  intro hbad
  apply SkorokhodJ1.Path.ext
  intro t
  funext i
  rw [hp t, hcomp t i]
  change AdaptedState.ofState κ D (PopulationFixedTimeChaos.first k
    (ConfigurationTimeDependent.process control (Nat.succ_pos n) left p t) i) = _
  rw [PopulationFixedTimeChaos.first_cast hkn]
  apply congrArg (AdaptedState.ofState κ D)
  have he := congrFun (hY t t.property.1) (Fin.castLE hkn i)
  change NonlinearParticleArray.process control hActivity ν T T.coe_nonneg hCoupling hMoment
    right (Fin.castLE hkn i) p t = _ at he
  rw [he]
  by_contra hne
  have hsep := one_le_adaptedDistance_of_ne (κ := κ) _ _ hne
  have hdom : ENNReal.ofReal (adaptedDistance κ
      (ConfigurationTimeDependent.process control (Nat.succ_pos n) left p t (Fin.castLE hkn i))
      (DeterministicEnvironmentConfiguration.process control (Nat.succ_pos n) hActivity
        v T T.coe_nonneg hv right p t (Fin.castLE hkn i))) ≤
      PopulationCouplingRemoval.coordinateRunningCost control (Nat.succ_pos n) hActivity
        v T T.coe_nonneg hv left right (Fin.castLE hkn i) T p :=
    le_iSup_of_le t le_rfl
  apply hbad
  apply (PopulationFocalApproximation.lt_focalPathDiscrepancy_iff control hActivity ν T T.coe_nonneg
    hCoupling hMoment n k hkn T p _).mpr
  refine ⟨i, lt_of_lt_of_le ?_ hdom⟩
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr
    (lt_of_lt_of_le (by norm_num) hsep)

/-- The actual focal path law on an arbitrary canonical initial/noise space. -/
def interactingLaw {A : Type*} [MeasurableSpace A] {N : ℕ} (hN : 0 < N)
    (initial : A → Configuration N D) (T : ℝ≥0) (k : ℕ)
    (μ : Measure A) [IsProbabilityMeasure μ] (hinit : Measurable initial)
    (hV : Integrable (fun a => lyapunov control (initial a)) μ) :
    ProbabilityMeasure (Path T (Fin k → AdaptedState κ D)) :=
  CoupledPathLawConvergence.imageLaw (law μ (Label N D))
    (interactingPath control hN initial T k)
    (aemeasurable_interactingPath control hN initial T k μ hinit hV)

/-- Vanishing actual focal discrepancies give weak convergence of vector-path
laws. The only intermediate convergence input is the already-proved focal
estimate; the final canonical theorem below discharges it. -/
theorem coupled_laws_tendsto
    (γ : ∀ n, Measure (Record (n + 1) D)) [∀ n, IsProbabilityMeasure (γ n)]
    (hright : ∀ n, (γ n).map right = Measure.pi (fun _ : Fin (n + 1) => ν.measure))
    (hV : ∀ n, Integrable (fun a => lyapunov control (left a)) (γ n))
    (k : ℕ)
    (hfocal : Tendsto (fun n => (law (γ n) (Label (n + 1) D)).real
      (badEvent control hActivity ν T hCoupling hMoment n k)) atTop (𝓝 0)) :
    Tendsto (fun n => interactingLaw control (Nat.succ_pos n) left T k (γ n) measurable_left (hV n))
      atTop (𝓝 (NonlinearSkorokhodArray.pathLaw control hActivity ν T hCoupling hMoment k)) := by
  let X := fun n => interactingPath control (Nat.succ_pos n) left T k
  let Y := fun n : ℕ => NonlinearSkorokhodArray.comparison control hActivity ν T hCoupling hMoment (right (N := n + 1)) k
  let B := fun n => if k ≤ n + 1 then badEvent control hActivity ν T hCoupling hMoment n k else Set.univ
  have hB n : NullMeasurableSet (B n) (law (γ n) (Label (n + 1) D)) := by
    dsimp [B]
    split_ifs
    · exact nullMeasurable_badEvent control hActivity ν T hCoupling hMoment n k (γ n) (hright n) (hV n)
    · exact MeasurableSet.univ.nullMeasurableSet
  have heq n : ∀ᵐ p ∂law (γ n) (Label (n + 1) D), p ∉ B n → X n p = Y n p := by
    by_cases hkn : k ≤ n + 1
    · simpa only [B, if_pos hkn] using
        ae_paths_eq_outside_badEvent control hActivity ν T hCoupling hMoment n k hkn (γ n) (hright n) (hV n)
    · exact Eventually.of_forall (fun p hp => False.elim (hp (by simp [B, hkn])))
  have hbad : Tendsto (fun n => (law (γ n) (Label (n + 1) D)).real (B n)) atTop (𝓝 0) := by
    apply hfocal.congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    simp only [B, if_pos (hn.trans (Nat.le_succ n))]
  apply CoupledPathLawConvergence.tendsto_imageLaw_of_badEvent
    (fun n => law (γ n) (Label (n + 1) D)) X Y
    (fun n => aemeasurable_interactingPath control (Nat.succ_pos n) left T k (γ n) measurable_left (hV n))
    (fun n => NonlinearSkorokhodArray.aemeasurable_comparison control hActivity ν T hCoupling hMoment
      right measurable_right (γ n) (hright n) k) B hB heq _ _ hbad
  filter_upwards [eventually_ge_atTop k] with n hn
  exact NonlinearSkorokhodArray.comparison_map control hActivity ν T hCoupling hMoment
    right measurable_right (γ n) (hright n) (hn.trans (Nat.le_succ n))

/-- Exact transfer of the sampled initial vector to its canonical configuration
record, preserving the entire actual trajectory on every sample. -/
theorem interactingPath_initialProjection {A : Type*} [MeasurableSpace A] {N : ℕ}
    (hN : 0 < N) (initial : A → Configuration N D) (T : ℝ≥0) (k : ℕ)
    (p : Sample A (Label N D)) :
    interactingPath control hN id T k (PopulationEmpiricalLimit.initialProjection initial p) =
      interactingPath control hN initial T k p := by
  rfl

/-- The genuine path law on original vector law times the canonical noise.
Its initial Lyapunov integrability is transferred from the supplied vector. -/
def canonicalLaw {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (hN : 0 < N)
    (P : Measure Ω) [IsProbabilityMeasure P] (z : Ω → Configuration N D)
    (hz : Measurable z) (hΨ : Integrable (fun ω => lyapunov control (z ω)) P)
    (T : ℝ≥0) (k : ℕ) : ProbabilityMeasure (Path T (Fin k → AdaptedState κ D)) := by
  letI : IsProbabilityMeasure (P.map z) := isProbabilityMeasure_map hz.aemeasurable
  have hI : Integrable (lyapunov control (N := N)) (P.map z) :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable hz.aemeasurable).mpr hΨ
  exact interactingLaw control hN id T k (P.map z) measurable_id hI

/-- Focal path-space chaos under the manuscript's original initialization.
The limit is the joint law of independent nonlinear trajectories in the
single vector-valued adapted-metric J1 space. No coupling or path-law
convergence premise is supplied. -/
theorem canonical_laws_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (z : ∀ n, Ω → Configuration (n + 1) D) (hz : ∀ n, Measurable (z n))
    (hex : ∀ n, ExchangeableMatching.ExchangeableLaw (P.map (z n)))
    (hΨ : ∀ n, Integrable (fun ω => lyapunov control (z n ω)) P)
    (C : ℝ) (hbound : ∀ n, (∫ ω, lyapunov control (z n ω) ∂P) ≤ C)
    (hconv : TendstoInMeasure P
      (fun n ω => wasserstein (empiricalLaw κ (Nat.succ_pos n) (z n ω)) ν) atTop 0)
    (k : ℕ) :
    Tendsto (fun n => canonicalLaw control (Nat.succ_pos n) P (z n) (hz n) (hΨ n) T k)
      atTop (𝓝 (NonlinearSkorokhodArray.pathLaw control hActivity ν T hCoupling hMoment k)) := by
  obtain ⟨γ, hp, _he, hl, hr, _hs, _ha, _hm, hf⟩ :=
    PopulationFocalApproximation.exists_full_synchronous_approximation
      control hActivity ν T T.coe_nonneg hCoupling hMoment P z hz hex hΨ C hbound hconv
  letI : ∀ n, IsProbabilityMeasure (γ n) := hp
  have hV n : Integrable (fun a => lyapunov control (left a)) (γ n) :=
    integrable_initial_of_map control (γ n) P left (z n) measurable_left (hz n) (hl n) (hΨ n)
  have hc := coupled_laws_tendsto control hActivity ν T hCoupling hMoment γ hr hV k
    (hf k (1 / 2) (by norm_num))
  have heq n : interactingLaw control (Nat.succ_pos n) left T k (γ n) measurable_left (hV n) =
      canonicalLaw control (Nat.succ_pos n) P (z n) (hz n) (hΨ n) T k := by
    letI : IsProbabilityMeasure (P.map (z n)) := isProbabilityMeasure_map (hz n).aemeasurable
    have hI : Integrable (lyapunov control (N := n + 1)) (P.map (z n)) :=
      (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable (hz n).aemeasurable).mpr (hΨ n)
    let π := PopulationEmpiricalLimit.initialProjection (left (N := n + 1) (D := D))
    have hπ : MeasurePreserving π (law (γ n) (Label (n + 1) D))
        (law (P.map (z n)) (Label (n + 1) D)) := by
      refine ⟨PopulationEmpiricalLimit.measurable_initialProjection left measurable_left, ?_⟩
      rw [PopulationEmpiricalLimit.initialProjection_map left (γ n) measurable_left, hl n]
    have hpath : AEMeasurable (interactingPath control (Nat.succ_pos n) id T k)
        ((law (γ n) (Label (n + 1) D)).map π) := by
      rw [hπ.map_eq]
      exact aemeasurable_interactingPath control (Nat.succ_pos n) id T k (P.map (z n)) measurable_id hI
    apply Subtype.ext
    change (law (γ n) (Label (n + 1) D)).map (interactingPath control (Nat.succ_pos n) left T k) =
      (law (P.map (z n)) (Label (n + 1) D)).map (interactingPath control (Nat.succ_pos n) id T k)
    rw [← hπ.map_eq, AEMeasurable.map_map_of_aemeasurable hpath hπ.measurable.aemeasurable]
    rfl
  exact hc.congr' (Eventually.of_forall heq)

end CarryingCapacity.PopulationPathChaos
