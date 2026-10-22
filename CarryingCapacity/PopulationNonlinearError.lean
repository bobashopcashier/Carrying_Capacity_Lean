import CarryingCapacity.PopulationStoppedCoupling
import CarryingCapacity.NonlinearParticleConfiguration
import CarryingCapacity.NonlinearParticleEmpirical

/-!
# Actual nonlinear configuration error and the independent empirical error

Pathwise uniqueness identifies the prescribed-environment configuration with
the scalar nonlinear copies on the same sample and original noise. The actual
configuration's empirical discrepancy therefore has precisely the independent
array's error and expectation. Fixed-time and sample-time integrability are
derived from its genuine iid marginals, before any real integral is used.
All self-consistent law and time-integrability statements are on `[0,T]`.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal

namespace CarryingCapacity.PopulationNonlinearError
open CommonInitialNoise ConfigurationLocalization

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)
  {A : Type*} [MeasurableSpace A] (n : ℕ)
  (initial : A → Configuration (n + 1) D)

local notation "v" => NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment
local notation "hv" => Continuous.continuousOn (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment)

/-- The actual prescribed-environment configuration's empirical error. -/
def error (p : Sample A (Label (n + 1) D)) (s : ℝ) : ℝ :=
  PopulationStoppedCoupling.empiricalError control (Nat.succ_pos n) hActivity v T hT hv initial p s

omit [MeasurableSpace A] in
theorem error_nonnegative (p : Sample A (Label (n + 1) D)) (s : ℝ) :
    0 ≤ error control hActivity ν T hT hCoupling hMoment n initial p s := wasserstein_nonneg _ _

variable (hInitial : Measurable initial) (γ : Measure A) [IsProbabilityMeasure γ]
  (hright : γ.map initial = Measure.pi (fun _ : Fin (n + 1) => ν.measure))
include hInitial hright

/-- Equality is on one event simultaneously at every nonnegative time. It
compares two genuine constructions using their actual same-noise path identity. -/
theorem ae_error_eq_array : ∀ᵐ p ∂law γ (Label (n + 1) D), ∀ s : ℝ, 0 ≤ s →
    error control hActivity ν T hT hCoupling hMoment n initial p s =
      NonlinearParticleEmpirical.error control hActivity ν T hT hCoupling hMoment n initial s p := by
  filter_upwards [NonlinearParticleConfiguration.ae_path_eq_configuration
    control hActivity ν T hT hCoupling hMoment initial hInitial γ hright (Nat.succ_pos n)] with p hp
  intro s hs
  unfold error PopulationStoppedCoupling.empiricalError NonlinearParticleEmpirical.error
  rw [← hp s hs]
  rfl

/-- Integrability of the actual configuration error follows from the proved
iid marginal law, with no additional discrepancy moment hypothesis. -/
theorem integrable_error (s : ℝ) (hs : s ∈ Icc 0 T) :
    Integrable (fun p => error control hActivity ν T hT hCoupling hMoment n initial p s)
      (law γ (Label (n + 1) D)) :=
  (NonlinearParticleEmpirical.integrable_error control hActivity ν T hT hCoupling hMoment
    n initial γ hInitial hright ⟨s,hs⟩).congr
      ((ae_error_eq_array control hActivity ν T hT hCoupling hMoment n initial hInitial γ hright).mono
        (fun _ hp => (hp s hs.1).symm))

/-- The actual expected configuration discrepancy. -/
def expectedError (s : ℝ) : ℝ :=
  ∫ p, error control hActivity ν T hT hCoupling hMoment n initial p s ∂law γ (Label (n + 1) D)

/-- Exact expected-error identification, not an estimate or a convergence premise. -/
theorem expectedError_eq_beta (s : ℝ) (hs : 0 ≤ s) :
    expectedError control hActivity ν T hT hCoupling hMoment n initial γ s =
      NonlinearParticleEmpirical.beta control hActivity ν T hT hCoupling hMoment n initial γ s := by
  apply integral_congr_ae
  filter_upwards [ae_error_eq_array control hActivity ν T hT hCoupling hMoment n initial hInitial γ hright]
    with p hp
  exact hp s hs

omit hInitial hright [IsProbabilityMeasure γ] in
theorem expectedError_nonnegative (s : ℝ) :
    0 ≤ expectedError control hActivity ν T hT hCoupling hMoment n initial γ s :=
  integral_nonneg (fun p => error_nonnegative control hActivity ν T hT hCoupling hMoment n initial p s)

/-- The actual expectation has the same uniform manuscript-envelope bound. -/
theorem expectedError_le_envelope (s : ℝ) (hs : s ∈ Icc 0 T) :
    expectedError control hActivity ν T hT hCoupling hMoment n initial γ s ≤
      2 * DeterministicEnvironmentLyapunov.manuscriptBound control ν
        (DeterministicEnvironmentLyapunov.driftConstant control) T := by
  rw [expectedError_eq_beta control hActivity ν T hT hCoupling hMoment n initial hInitial γ hright s hs.1]
  exact NonlinearParticleEmpirical.beta_le_envelope control hActivity ν T hT hCoupling hMoment
    n initial γ hInitial hright ⟨s,hs⟩

/-- The true expected error is Lebesgue integrable in time on the horizon. -/
theorem integrableOn_expectedError :
    IntegrableOn (expectedError control hActivity ν T hT hCoupling hMoment n initial γ) (Icc 0 T) volume := by
  apply (NonlinearParticleEmpirical.integrableOn_beta control hActivity ν T hT hCoupling hMoment
    n initial γ hInitial hright).congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact (expectedError_eq_beta control hActivity ν T hT hCoupling hMoment n initial hInitial γ hright s hs.1).symm

/-- The half-open interval version required by the actual compensated estimate. -/
theorem integrableOn_expectedError_Ioc :
    IntegrableOn (expectedError control hActivity ν T hT hCoupling hMoment n initial γ) (Ioc 0 T) volume :=
  (integrableOn_expectedError control hActivity ν T hT hCoupling hMoment n initial hInitial γ hright).mono_set
    Ioc_subset_Icc_self

/-- Genuine sample-time integrability is obtained by Fubini for the independent
error and then the one-event actual configuration identity. -/
theorem integrable_error_prod :
    Integrable (fun p : Sample A (Label (n + 1) D) × ℝ =>
      error control hActivity ν T hT hCoupling hMoment n initial p.1 p.2)
      ((law γ (Label (n + 1) D)).prod (volume.restrict (Ioc 0 T))) := by
  have hi : Integrable (Function.uncurry
      (NonlinearParticleEmpirical.error control hActivity ν T hT hCoupling hMoment n initial))
      ((volume.restrict (Ioc 0 T)).prod (law γ (Label (n + 1) D))) := by
    apply (integrable_prod_iff
      (NonlinearParticleEmpirical.measurable_error control hActivity ν T hT hCoupling hMoment
        n initial hInitial).aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact NonlinearParticleEmpirical.integrable_error control hActivity ν T hT hCoupling hMoment
        n initial γ hInitial hright ⟨s,hs.1.le,hs.2⟩
    · simpa only [Function.uncurry_apply_pair,
        Real.norm_of_nonneg (NonlinearParticleEmpirical.error_nonnegative
          control hActivity ν T hT hCoupling hMoment n initial _ _)] using
        (NonlinearParticleEmpirical.integrableOn_beta control hActivity ν T hT hCoupling hMoment
          n initial γ hInitial hright).mono_set Ioc_subset_Icc_self
  apply hi.swap.congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
    (ae_error_eq_array control hActivity ν T hT hCoupling hMoment n initial hInitial γ hright),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)] with p hp ht
  exact (hp p.2 ht.1.le).symm

/-- The exact real time integral is the already-proved independent beta
integral. Both integrability statements were proved above. -/
theorem integral_expectedError_eq_beta :
    (∫ s in Ioc 0 T, expectedError control hActivity ν T hT hCoupling hMoment n initial γ s) =
      ∫ s in Ioc 0 T, NonlinearParticleEmpirical.beta control hActivity ν T hT hCoupling hMoment n initial γ s := by
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  exact expectedError_eq_beta control hActivity ν T hT hCoupling hMoment n initial hInitial γ hright s hs.1.le

end CarryingCapacity.PopulationNonlinearError

namespace CarryingCapacity.PopulationNonlinearError
open CommonInitialNoise ConfigurationLocalization

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)
  {A : ℕ → Type*} [∀ n, MeasurableSpace (A n)]
  (initial : ∀ n, A n → Configuration (n + 1) D) (hInitial : ∀ n, Measurable (initial n))
  (γ : ∀ n, Measure (A n)) [∀ n, IsProbabilityMeasure (γ n)]
  (hright : ∀ n, (γ n).map (initial n) = Measure.pi (fun _ : Fin (n + 1) => ν.measure))
include hInitial hright

/-- The actual comparison configurations inherit the proved vanishing
integrated empirical error; no convergence premise is added. Row spaces and
initial couplings may depend on the population size. -/
theorem integral_expectedError_tendsto_zero :
    Tendsto (fun n => ∫ s in Ioc 0 T,
      expectedError control hActivity ν T hT hCoupling hMoment n (initial n) (γ n) s)
      atTop (nhds 0) := by
  have he : (fun n => ∫ s in Ioc 0 T,
      expectedError control hActivity ν T hT hCoupling hMoment n (initial n) (γ n) s) =
      (fun n => ∫ s in Ioc 0 T,
        NonlinearParticleEmpirical.beta control hActivity ν T hT hCoupling hMoment n (initial n) (γ n) s) := by
    funext n
    exact integral_expectedError_eq_beta control hActivity ν T hT hCoupling hMoment n
      (initial n) (hInitial n) (γ n) (hright n)
  rw [he]
  exact NonlinearParticleEmpirical.integral_Ioc_beta_tendsto_zero control hActivity ν T hT hCoupling hMoment
    initial hInitial γ hright

end CarryingCapacity.PopulationNonlinearError
