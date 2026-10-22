import CarryingCapacity.CanonicalSkorokhodPaths
import CarryingCapacity.AdaptedStateSpace
import CarryingCapacity.ConcentratingLaw
import CarryingCapacity.PopulationEmpiricalLimit

/-!
# Actual empirical path-law convergence in Skorokhod space

The empirical path is a measurable transformation of the genuine configuration
path. Uniform empirical convergence controls its true J1 distance to the
continuous nonlinear law curve. Concentration then gives weak convergence of
the actual path laws to the Dirac law of that curve.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical Topology ENNReal NNReal

namespace CarryingCapacity.PopulationSkorokhodLimit
open CommonInitialNoise ConfigurationLocalization SkorokhodJ1
open CoupledPathLawConvergence PopulationCouplingInitialization

variable {D N : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}

theorem uniformContinuous_empirical (hN : 0 < N) :
    UniformContinuous (empiricalLaw κ hN : Configuration N D → MomentLaw κ D) :=
  (AdaptedState.uniformContinuous_empiricalLaw κ D hN).comp
    (AdaptedState.piUniformEquiv κ D N).symm.uniformContinuous

variable (control : LyapunovControl κ q) (T : ℝ≥0)

/-- The actual empirical path, with the same exceptional-sample convention
as the underlying constructed configuration path. -/
def empiricalPath {A : Type*} [MeasurableSpace A] (hN : 0 < N)
    (initial : A → Configuration N D) (p : Sample A (Label N D)) : Path T (MomentLaw κ D) :=
  (CanonicalSkorokhodPaths.configurationPath control hN initial T p).map
    (empiricalLaw κ hN) (uniformContinuous_empirical hN).continuous

theorem aemeasurable_empiricalPath {A : Type*} [MeasurableSpace A] (hN : 0 < N)
    (initial : A → Configuration N D) (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (hV : Integrable (fun a => lyapunov control (initial a)) μ) :
    AEMeasurable (empiricalPath control T hN initial) (law μ (Label N D)) :=
  (measurable_path_map (empiricalLaw κ hN) (uniformContinuous_empirical hN)).comp_aemeasurable
    (CanonicalSkorokhodPaths.aemeasurable_configurationPath control hN initial T μ hinit hV)

theorem ae_empiricalPath_apply {A : Type*} [MeasurableSpace A] (hN : 0 < N)
    (initial : A → Configuration N D) (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (hV : Integrable (fun a => lyapunov control (initial a)) μ) :
    ∀ᵐ p ∂law μ (Label N D), ∀ t : Time T, empiricalPath control T hN initial p t =
      empiricalLaw κ hN (ConfigurationTimeDependent.process control hN initial p t) := by
  filter_upwards [CanonicalSkorokhodPaths.ae_configurationPath_apply
    control hN initial T μ hinit hV] with p hp
  intro t
  exact congrArg (empiricalLaw κ hN) (hp t)

variable (hActivity : MomentActivityBound κ q) (ν : MomentLaw κ D)
  (hCoupling : MomentCouplingBound κ q) (hMoment : Integrable control.function ν.measure)

/-- The genuinely continuous nonlinear law curve as one deterministic J1 path. -/
def limitPath : Path T (MomentLaw κ D) :=
  Path.ofContinuous
    (fun t => NonlinearFixedPoint.environment control hActivity ν T T.coe_nonneg hCoupling hMoment t)
    ((NonlinearFixedPoint.continuous_environment control hActivity ν T T.coe_nonneg
      hCoupling hMoment).comp continuous_subtype_val)

@[simp] theorem limitPath_apply (t : Time T) :
    limitPath control T hActivity ν hCoupling hMoment t =
      NonlinearFixedPoint.environment control hActivity ν T T.coe_nonneg hCoupling hMoment t := rfl

/-- The actual J1 distance is bounded by the already proved all-real uniform
empirical transport error on one full-probability event. -/
theorem ae_edist_le_runningError {A : Type*} [MeasurableSpace A] (n : ℕ)
    (initial : A → Configuration (n + 1) D) (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (hV : Integrable (fun a => lyapunov control (initial a)) μ) :
    ∀ᵐ p ∂law μ (Label (n + 1) D),
      edist (empiricalPath control T (Nat.succ_pos n) initial p)
          (limitPath control T hActivity ν hCoupling hMoment) ≤
        PopulationEmpiricalLimit.runningError control hActivity ν T T.coe_nonneg
          hCoupling hMoment n initial p := by
  filter_upwards [ae_empiricalPath_apply control T (Nat.succ_pos n) initial μ hinit hV] with p hp
  apply (edist_le_uniform_edist _ _).trans
  apply iSup_le
  intro t
  rw [hp t, limitPath_apply, edist_dist, momentLaw_dist]
  exact le_iSup_of_le t le_rfl

/-- The actual empirical trajectory law on the canonical original-vector space. -/
def canonicalLaw (n : ℕ) (α : ProbabilityMeasure (Configuration (n + 1) D))
    (hV : Integrable (lyapunov control) α.toMeasure) : ProbabilityMeasure (Path T (MomentLaw κ D)) :=
  imageLaw (law α.toMeasure (Label (n + 1) D))
    (empiricalPath control T (Nat.succ_pos n) id)
    (aemeasurable_empiricalPath control T (Nat.succ_pos n) id α.toMeasure measurable_id hV)

section ManuscriptInitialization
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (z : ∀ n, Ω → Configuration (n + 1) D) (hz : ∀ n, Measurable (z n))
  (hex : ∀ n, ExchangeableMatching.ExchangeableLaw (P.map (z n)))
  (hΨ : ∀ n, Integrable (fun ω => lyapunov control (z n ω)) P)
  (C : ℝ) (hbound : ∀ n, (∫ ω, lyapunov control (z n ω) ∂P) ≤ C)
  (hconv : TendstoInMeasure P
    (fun n ω => wasserstein (empiricalLaw κ (Nat.succ_pos n) (z n ω)) ν) atTop 0)

include hz hex hΨ hbound hconv

/-- The genuine J1 distance to the deterministic nonlinear curve tends to
zero in probability under the exact manuscript initialization. -/
theorem probability_distance_gt_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (P.map (z n)) (Label (n + 1) D)).real
      {p | ε < dist (empiricalPath control T (Nat.succ_pos n) id p)
        (limitPath control T hActivity ν hCoupling hMoment)}) atTop (𝓝 0) := by
  letI : ∀ n, IsProbabilityMeasure (P.map (z n)) :=
    fun n => isProbabilityMeasure_map (hz n).aemeasurable
  apply squeeze_zero (fun _ => measureReal_nonneg) _
    (PopulationEmpiricalLimit.probability_runningError_gt_tendsto_zero
      control hActivity ν T T.coe_nonneg hCoupling hMoment P z hz hex hΨ C hbound hconv ε hε)
  intro n
  have hV : Integrable (lyapunov control) (P.map (z n)) :=
    integrable_initial_of_map control (P.map (z n)) P id (z n)
      measurable_id (hz n) (by simp) (hΨ n)
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [ae_edist_le_runningError control T hActivity ν hCoupling hMoment
    n id (P.map (z n)) measurable_id hV] with p hp
  intro hdist
  have he : ENNReal.ofReal ε <
      edist (empiricalPath control T (Nat.succ_pos n) id p)
        (limitPath control T hActivity ν hCoupling hMoment) := by
    rw [edist_dist]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε.le |>.mpr hdist
  exact he.trans_le hp

/-- The empirical process converges weakly in the genuine J1 path space to
the Dirac law of the nonlinear curve. No path measurability, uniform limit,
or weak convergence conclusion is included as a hypothesis. -/
theorem canonical_laws_tendsto :
    Tendsto (fun n => canonicalLaw control T n (imageLaw P (z n) (hz n).aemeasurable)
      (integrable_initial_of_map control (P.map (z n)) P id (z n)
        measurable_id (hz n) (by simp) (hΨ n)))
      atTop (𝓝 (ConcentratingLaw.pointLaw (limitPath control T hActivity ν hCoupling hMoment))) := by
  letI : ∀ n, IsProbabilityMeasure (P.map (z n)) :=
    fun n => isProbabilityMeasure_map (hz n).aemeasurable
  apply ConcentratingLaw.tendsto_imageLaw_of_probability_distance
    (fun n => law (P.map (z n)) (Label (n + 1) D))
    (fun n => empiricalPath control T (Nat.succ_pos n) id)
    (fun n => aemeasurable_empiricalPath control T (Nat.succ_pos n) id (P.map (z n))
      measurable_id (integrable_initial_of_map control (P.map (z n)) P id (z n)
        measurable_id (hz n) (by simp) (hΨ n)))
    (limitPath control T hActivity ν hCoupling hMoment)
  exact probability_distance_gt_tendsto_zero control T hActivity ν hCoupling hMoment
    P z hz hex hΨ C hbound hconv

end ManuscriptInitialization
end CarryingCapacity.PopulationSkorokhodLimit
