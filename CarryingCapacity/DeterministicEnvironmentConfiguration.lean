import CarryingCapacity.ConfigurationLocalization
import CarryingCapacity.DeterministicEnvironmentProcess

/-!
# A finite configuration in a prescribed deterministic environment

Every label consists of a particle index and an original jump direction. The
configuration uses the same endpoint-clamped environment for every particle.
The exact generator, averaged activity, and averaged Lyapunov drift are derived
from the single-particle assumptions. Actual spatial localization and exit
exhaustion then construct a nonexplosive configuration on the shared noise.

This module does not identify that configuration with an array of scalar
realizations, nor assert independence of its coordinates.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal Topology BigOperators

namespace CarryingCapacity.DeterministicEnvironmentConfiguration
open CommonInitialNoise ConfigurationLocalization

variable {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}

/-- The environment is fixed externally; only the selected coordinate is read. -/
def rate (κ : MomentScale) (q : Rates D (MomentLaw κ D))
    (v : ℝ → MomentLaw κ D) (T : ℝ) (h : Label N D) (t : ℝ)
    (z : Configuration N D) : ℝ :=
  DeterministicEnvironmentFrozen.timeRate κ q v T h.2 t (z h.1)

theorem rate_nonnegative (v : ℝ → MomentLaw κ D) (T : ℝ)
    (h : Label N D) (t : ℝ) (z : Configuration N D) :
    0 ≤ rate κ q v T h t z :=
  DeterministicEnvironmentFrozen.timeRate_nonnegative κ q v T h.2 t (z h.1)

theorem rate_eq_on_horizon (v : ℝ → MomentLaw κ D) (T : ℝ)
    (h : Label N D) (t : ℝ) (ht : t ∈ Icc 0 T) (z : Configuration N D) :
    rate κ q v T h t z = q.rate h.2 (z h.1) (v t) :=
  DeterministicEnvironmentFrozen.timeRate_eq κ q v T h.2 t ht (z h.1)

theorem measurable_rate (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T)
    (hv : ContinuousOn v (Icc 0 T)) (hCoupling : MomentCouplingBound κ q) :
    ∀ h : Label N D, ∀ z, Measurable (fun t => rate κ q v T h t z) :=
  fun h z => DeterministicEnvironmentFrozen.measurable_timeRate κ q v T hv hCoupling hT h.2 (z h.1)

/-- The genuine configuration generator with time-dependent rates. -/
def generator (κ : MomentScale) (q : Rates D (MomentLaw κ D))
    (v : ℝ → MomentLaw κ D) (T : ℝ) (F : Configuration N D → ℝ)
    (t : ℝ) (z : Configuration N D) : ℝ :=
  ∑ h : Label N D, rate κ q v T h t z * (F (jump h z) - F z)

theorem generator_eq_systemGenerator (v : ℝ → MomentLaw κ D) (T : ℝ)
    (F : Configuration N D → ℝ) (t : ℝ) (z : Configuration N D) :
    generator κ q v T F t z = FiniteGenerator.systemGenerator Jump.advance q.rate
      (fun _ => v (max 0 (min t T))) F z := by
  unfold generator FiniteGenerator.systemGenerator
  rw [Fintype.sum_prod_type]
  rfl

/-- A coordinate average has exactly the averaged scalar generator. -/
theorem generator_empiricalMean (v : ℝ → MomentLaw κ D) (T : ℝ)
    (f : State D → ℝ) (t : ℝ) (z : Configuration N D) :
    generator κ q v T (FiniteGenerator.empiricalMean f) t z =
      (N : ℝ)⁻¹ * ∑ i, q.generator (v (max 0 (min t T))) f (z i) := by
  rw [generator_eq_systemGenerator]
  exact FiniteGenerator.systemGenerator_empiricalMean Jump.advance q.rate
    (fun _ => v (max 0 (min t T))) f z

/-- Weighted proposal activity, normalized by the number of particles. -/
def normalizedActivity (κ : MomentScale) (q : Rates D (MomentLaw κ D))
    (v : ℝ → MomentLaw κ D) (T : ℝ) (t : ℝ) (z : Configuration N D) : ℝ :=
  (N : ℝ)⁻¹ * ∑ h : Label N D, rate κ q v T h t z *
    adaptedDistance κ (Jump.advance h.2 (z h.1)) (z h.1)

theorem normalizedActivity_eq (v : ℝ → MomentLaw κ D) (T t : ℝ)
    (z : Configuration N D) :
    normalizedActivity κ q v T t z =
      (N : ℝ)⁻¹ * ∑ i, weightedActivity κ q (z i) (v (max 0 (min t T))) := by
  unfold normalizedActivity
  rw [Fintype.sum_prod_type]
  rfl

variable (control : LyapunovControl κ q)

/-- The normalized activity coefficient is independent of particle number. -/
theorem normalizedActivity_le (hActivity : MomentActivityBound κ q)
    (v : ℝ → MomentLaw κ D) (T t : ℝ) (z : Configuration N D) :
    normalizedActivity κ q v T t z ≤
      DeterministicEnvironmentRates.activityConstant κ q hActivity * lyapunov control z *
        (1 + moment (v (max 0 (min t T)))) := by
  rw [normalizedActivity_eq]
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ i, DeterministicEnvironmentRates.activityConstant κ q hActivity *
        control.function (z i) * (1 + moment (v (max 0 (min t T)))) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => ?_))
        (inv_nonneg.mpr (Nat.cast_nonneg N))
      apply ((Classical.choose_spec hActivity).2 (z i) _).trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (control.dominates (z i))
          (DeterministicEnvironmentRates.activityConstant_nonnegative κ q hActivity))
        (by have hm := moment_nonneg (v (max 0 (min t T))); positivity)
    _ = _ := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum, lyapunov, FiniteGenerator.empiricalMean]
      ring

/-- The exact averaged Lyapunov generator. -/
theorem generator_lyapunov (v : ℝ → MomentLaw κ D) (T t : ℝ)
    (z : Configuration N D) :
    generator κ q v T (lyapunov control) t z =
      (N : ℝ)⁻¹ * ∑ i, q.generator (v (max 0 (min t T))) control.function (z i) :=
  generator_empiricalMean v T control.function t z

/-- A genuine environment Lyapunov bound yields an averaged additive drift,
with the single-lineage constant and no dependence on N. -/
theorem generator_lyapunov_le (hN : 0 < N) (v : ℝ → MomentLaw κ D)
    (T : ℝ) (hT : 0 ≤ T) (B : ℝ) (hB : 0 ≤ B)
    (hEnv : ∀ s ∈ Icc 0 T,
      LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
    (t : ℝ) (z : Configuration N D) :
    generator κ q v T (lyapunov control) t z ≤
      DeterministicEnvironmentLyapunov.driftConstant control * (1 + lyapunov control z + B) := by
  rw [generator_lyapunov]
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ i, DeterministicEnvironmentLyapunov.driftConstant control *
        (1 + control.function (z i) + B) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => ?_))
        (inv_nonneg.mpr (Nat.cast_nonneg N))
      exact DeterministicEnvironmentLyapunov.clamped_generator_le control v T hT B hB hEnv t (z i)
    _ = _ := by
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
      simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
        lyapunov, FiniteGenerator.empiricalMean]
      field_simp [hNr]
      ring_nf
      simp

/-- The same affine coefficient works for all positive particle numbers. -/
theorem generator_lyapunov_affine (hN : 0 < N) (v : ℝ → MomentLaw κ D)
    (T : ℝ) (hT : 0 ≤ T) (B : ℝ) (hB : 0 ≤ B)
    (hEnv : ∀ s ∈ Icc 0 T,
      LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
    (t : ℝ) (z : Configuration N D) :
    generator κ q v T (lyapunov control) t z ≤
      DeterministicEnvironmentLyapunov.affineConstant control B * (1 + lyapunov control z) := by
  apply (generator_lyapunov_le control hN v T hT B hB hEnv t z).trans
  have hV := lyapunov_nonnegative control z
  have hC := DeterministicEnvironmentLyapunov.driftConstant_nonnegative control
  unfold DeterministicEnvironmentLyapunov.affineConstant
  have hprod : 0 ≤ B * lyapunov control z := mul_nonneg hB hV
  nlinarith

/-- Every finite active configuration region has a positive uniform rate cap.
The finite union of its coordinate states reduces this to the scalar bound. -/
theorem exists_positive_uniform_rate_bounds (hN : 0 < N)
    (hActivity : MomentActivityBound κ q) (v : ℝ → MomentLaw κ D)
    (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T)) :
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ z ∈ LyapunovLocalization.active (lyapunov control) (finite_sublevel control hN) n,
        ∀ j t, rate κ q v T j t z ≤ C := by
  intro n
  let G := LyapunovLocalization.active (lyapunov control) (finite_sublevel control hN) n
  let H : Finset (State D) := G.biUnion (fun z => Finset.univ.image z)
  obtain ⟨C, hC, hbound⟩ := DeterministicEnvironmentRates.exists_positive_rate_bound_on_Icc
    κ q hActivity H v T hv
  refine ⟨C, hC, fun z hz j t => ?_⟩
  apply hbound (z j.1) _ j.2 _ ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  exact Finset.mem_biUnion.mpr ⟨z, hz, Finset.mem_image.mpr ⟨j.1, Finset.mem_univ _, rfl⟩⟩

/-- The exact finite-region premise of the global construction is derived. -/
theorem exists_uniform_rate_bounds (hN : 0 < N)
    (hActivity : MomentActivityBound κ q) (v : ℝ → MomentLaw κ D)
    (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T)) :
    ∀ n : ℕ, ∃ C : ℝ,
      ∀ z ∈ LyapunovLocalization.active (lyapunov control) (finite_sublevel control hN) n,
        ∀ j t, rate κ q v T j t z ≤ C := by
  intro n
  obtain ⟨C, _, hC⟩ := exists_positive_uniform_rate_bounds control hN hActivity v T hT hv n
  exact ⟨C, hC⟩

end CarryingCapacity.DeterministicEnvironmentConfiguration

namespace CarryingCapacity.DeterministicEnvironmentConfiguration
open CommonInitialNoise ConfigurationLocalization DeterministicEnvironmentLyapunov

variable {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N) (hActivity : MomentActivityBound κ q)
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))
  {A : Type*} [MeasurableSpace A] (initial : A → Configuration N D)

/-- The actual frozen approximation at a canonical spatial level. -/
def localizedPath (n : ℕ) (p : Sample A (Label N D)) (t : ℝ) : Configuration N D :=
  TimeDependentLocalization.path (lyapunov control) (finite_sublevel control hN) jump
    (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv) initial n p t

/-- The genuine exit of the same localized path. -/
def exit (n : ℕ) (p : Sample A (Label N D)) : ℝ≥0∞ :=
  TimeDependentLocalization.exit (lyapunov control) (finite_sublevel control hN) jump
    (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv) initial n p

/-- The actual all-sample measurable limit of the spatial localizations.
The definition has no environmental Lyapunov bound or initial moment input. -/
def process (p : Sample A (Label N D)) (t : ℝ) : Configuration N D :=
  TimeDependentGlobalProcess.process (lyapunov control) (finite_sublevel control hN) jump
    (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv) initial 0 p t

/-- Its joint measurability follows from the paper's rate coupling assumption. -/
theorem measurable_process (hCoupling : MomentCouplingBound κ q) (hinit : Measurable initial) :
    Measurable (fun p : Sample A (Label N D) × ℝ => process control hN hActivity v T hT hv initial p.1 p.2) :=
  TimeDependentGlobalProcess.measurable_process (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv)
      initial 0 (measurable_rate v T hT hv hCoupling) hinit

/-- Every actual time evaluation is measurable in the raw initial/noise history. -/
theorem measurable_process_at (hCoupling : MomentCouplingBound κ q) (hinit : Measurable initial)
    (t : ℝ) : Measurable[filtration A (Label N D) t]
      (fun p => process control hN hActivity v T hT hv initial p t) :=
  TimeDependentGlobalProcess.measurable_process_at (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv)
      initial 0 (measurable_rate v T hT hv hCoupling) hinit t

theorem adapted_process (hCoupling : MomentCouplingBound κ q) (hinit : Measurable initial) :
    Adapted (filtration A (Label N D))
      (fun t p => process control hN hActivity v T hT hv initial p t) :=
  fun t => (measurable_process_at control hN hActivity v T hT hv initial hCoupling hinit t).stronglyMeasurable

/-- Correct initial value holds without an initial moment or environmental bound. -/
theorem ae_initial (μ : Measure A) : ∀ᵐ p ∂law μ (Label N D),
    process control hN hActivity v T hT hv initial p 0 = initial p.1 :=
  TimeDependentGlobalProcess.ae_process_zero (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv) initial 0 μ

/-- The actual global path has exactly the prescribed pushed-forward initial law. -/
theorem initial_law (μ : Measure A) [IsProbabilityMeasure μ] (hinit : Measurable initial) :
    (law μ (Label N D)).map (fun p => process control hN hActivity v T hT hv initial p 0) = μ.map initial :=
  TimeDependentGlobalProcess.process_zero_law (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv)
      initial 0 μ hinit

variable (μ : Measure A) [IsProbabilityMeasure μ]
  (hCoupling : MomentCouplingBound κ q) (hinit : Measurable initial)
  (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ t ∈ Icc 0 T, LyapunovFlowSpace.lyapunovIntegral control.function (v t) ≤ ENNReal.ofReal B)
  (hInitial : Integrable (fun a => (lyapunov control) (initial a)) μ)
include hCoupling hinit hB hEnv hInitial

/-- Reciprocal tails for the actual first exits, with every stochastic bound
derived from the exact paper assumptions. -/
theorem exit_probability_le (n : ℕ) (S : ℝ) (hS : 0 ≤ S) :
    (law μ (Label N D)) {p | exit control hN hActivity v T hT hv initial n p ≤ ENNReal.ofReal S} ≤
      ENNReal.ofReal ((1 + ∫ a, (lyapunov control) (initial a) ∂μ) *
        Real.exp (affineConstant control B * S) - 1) / ((n + 1 : ℕ) : ℝ≥0∞) :=
  TimeDependentNonexplosion.exit_probability_le (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv)
      initial 0 μ (measurable_rate v T hT hv hCoupling)
      hinit (affineConstant control B) (affineConstant_nonnegative control B hB)
      (lyapunov_nonnegative control) (fun x j t _ => rate_nonnegative v T j t x) hInitial
      (fun x t _ => generator_lyapunov_affine control hN v T hT B hB hEnv t x) n S hS

/-- Genuine exits exhaust every finite horizon almost surely. -/
theorem ae_exhaustive : ∀ᵐ p ∂law μ (Label N D), ∀ S : ℝ≥0, ∃ n : ℕ,
    (S : ℝ≥0∞) < exit control hN hActivity v T hT hv initial n p :=
  TimeDependentNonexplosion.ae_exhaustive (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv)
      initial 0 μ (measurable_rate v T hT hv hCoupling)
      hinit (affineConstant control B) (affineConstant_nonnegative control B hB)
      (lyapunov_nonnegative control) (fun x j t _ => rate_nonnegative v T j t x) hInitial
      (fun x t _ => generator_lyapunov_affine control hN v T hT B hB hEnv t x)

/-- The actual global path agrees throughout each finite horizon with every
sufficiently high canonical frozen path. -/
theorem ae_agrees_on_horizon : ∀ᵐ p ∂law μ (Label N D), ∀ S : ℝ≥0, ∃ n, ∀ m, n ≤ m →
    ∀ t : ℝ, 0 ≤ t → t ≤ S → process control hN hActivity v T hT hv initial p t =
      localizedPath control hN hActivity v T hT hv initial m p t :=
  TimeDependentGlobalProcess.ae_agrees_on_horizon (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv)
      initial 0 μ (ae_exhaustive control hN hActivity v T hT hv initial μ hCoupling hinit B hB hEnv hInitial)

/-- Nonexplosion yields actual right-continuous paths with left limits. -/
theorem ae_cadlag : ∀ᵐ p ∂law μ (Label N D),
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt
      (process control hN hActivity v T hT hv initial p) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : Configuration N D, Tendsto
      (process control hN hActivity v T hT hv initial p) (𝓝[<] t) (𝓝 y)) :=
  TimeDependentGlobalProcess.ae_process_cadlag (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv)
      initial 0 μ (ae_exhaustive control hN hActivity v T hT hv initial μ hCoupling hinit B hB hEnv hInitial)

/-- Only finitely many actual proposals can change the global path on a
bounded horizon; no finite-activity premise is supplied. -/
theorem ae_finite_activity : ∀ᵐ p ∂law μ (Label N D), ∀ S : ℝ≥0, ∃ times : Finset ℝ,
    (times : Set ℝ) ⊆ Ioc 0 S ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ S →
      (∀ u ∈ times, u ∉ Ioc s t) →
        process control hN hActivity v T hT hv initial p s = process control hN hActivity v T hT hv initial p t := by
  filter_upwards [TimeDependentGlobalActivity.ae_finite_activity (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv)
      initial 0 μ (ae_exhaustive control hN hActivity v T hT hv initial μ hCoupling hinit B hB hEnv hInitial)]
    with p hp
  intro S
  obtain ⟨n, hn, he⟩ := hp S
  exact ⟨_, hn, he⟩

/-- The actual global Lyapunov value is integrable at every nonnegative time. -/
theorem integrable_lyapunov (S : ℝ) (hS : 0 ≤ S) :
    Integrable (fun p => (lyapunov control) (process control hN hActivity v T hT hv initial p S)) (law μ (Label N D)) :=
  TimeDependentGlobalMoment.integrable (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv)
      initial 0 μ (measurable_rate v T hT hv hCoupling)
      hinit (affineConstant control B) (affineConstant_nonnegative control B hB)
      (lyapunov_nonnegative control) (fun x j t _ => rate_nonnegative v T j t x) hInitial
      (fun x t _ => generator_lyapunov_affine control hN v T hT B hB hEnv t x) S hS

/-- Fatou transfers the finite-level bound to the genuine extended global moment. -/
theorem lyapunov_lintegral_le (S : ℝ) (hS : 0 ≤ S) :
    (∫⁻ p, ENNReal.ofReal ((lyapunov control) (process control hN hActivity v T hT hv initial p S))
      ∂law μ (Label N D)) ≤ ENNReal.ofReal ((1 + ∫ a, (lyapunov control) (initial a) ∂μ) *
        Real.exp (affineConstant control B * S) - 1) :=
  TimeDependentGlobalMoment.lintegral_le (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv)
      initial 0 μ (measurable_rate v T hT hv hCoupling)
      hinit (affineConstant control B) (affineConstant_nonnegative control B hB)
      (lyapunov_nonnegative control) (fun x j t _ => rate_nonnegative v T j t x) hInitial
      (fun x t _ => generator_lyapunov_affine control hN v T hT B hB hEnv t x) S hS

/-- The same explicit bound holds for the ordinary global expectation. -/
theorem lyapunov_expectation_le (S : ℝ) (hS : 0 ≤ S) :
    (∫ p, (lyapunov control) (process control hN hActivity v T hT hv initial p S) ∂law μ (Label N D)) ≤
      (1 + ∫ a, (lyapunov control) (initial a) ∂μ) * Real.exp (affineConstant control B * S) - 1 :=
  TimeDependentGlobalMoment.expectation_le (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv)
      initial 0 μ (measurable_rate v T hT hv hCoupling)
      hinit (affineConstant control B) (affineConstant_nonnegative control B hB)
      (lyapunov_nonnegative control) (fun x j t _ => rate_nonnegative v T j t x) hInitial
      (fun x t _ => generator_lyapunov_affine control hN v T hT B hB hEnv t x) S hS

end CarryingCapacity.DeterministicEnvironmentConfiguration

namespace CarryingCapacity.DeterministicEnvironmentConfiguration
open CommonInitialNoise ConfigurationLocalization

variable {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N) (hActivity : MomentActivityBound κ q)
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))
  {A : Type*} [MeasurableSpace A] (initial : A → Configuration N D)

/-- The actual predictable pre-jump version of the global environment process. -/
def preState (p : Sample A (Label N D)) (t : ℝ) : Configuration N D :=
  TimeDependentGlobalCounting.preState (lyapunov control) (finite_sublevel control hN) jump
    (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv) initial 0 p t

/-- Actual accepted increments on a time horizon, with no spatial indicator or height cap. -/
def horizonIncrement (F : Configuration N D → ℝ) (j : Label N D) (S : ℝ) :
    Sample A (Label N D) × (ℝ × ℝ) → ℝ :=
  TimeDependentGlobalCounting.horizonIncrement (lyapunov control) (finite_sublevel control hN) jump
    (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv) initial 0 F j S

/-- Predictability is proved on every sample, independently of moment and exit estimates. -/
theorem measurable_horizonIncrement (hCoupling : MomentCouplingBound κ q)
    (hinit : Measurable initial) (F : Configuration N D → ℝ) (j : Label N D) (S : ℝ) :
    Measurable[PredictableSets.predictable (filtration A (Label N D))]
      (horizonIncrement control hN hActivity v T hT hv initial F j S) :=
  TimeDependentGlobalCounting.measurable_horizonIncrement (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv)
      initial 0 (measurable_rate v T hT hv hCoupling) hinit F j S

variable (μ : Measure A) [IsProbabilityMeasure μ]
  (hCoupling : MomentCouplingBound κ q) (hinit : Measurable initial)
  (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ t ∈ Icc 0 T, LyapunovFlowSpace.lyapunovIntegral control.function (v t) ≤ ENNReal.ofReal B)
  (hInitial : Integrable (fun a => (lyapunov control) (initial a)) μ)
include hCoupling hinit hB hEnv hInitial

/-- The predictable version is the actual global path's left limit, simultaneously
at every positive time, with exhaustion already derived from the paper hypotheses. -/
theorem ae_preState_eq_leftLim : ∀ᵐ p ∂law μ (Label N D), ∀ t : ℝ, 0 < t →
    preState control hN hActivity v T hT hv initial p t =
      Function.leftLim (process control hN hActivity v T hT hv initial p) t :=
  TimeDependentGlobalCounting.ae_preState_eq_leftLim (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv)
      initial 0 μ (ae_exhaustive control hN hActivity v T hT hv initial μ hCoupling hinit B hB hEnv hInitial)

/-- Actual pathwise integrability of every test increment on every finite horizon. -/
theorem ae_integrable_horizonIncrement : ∀ᵐ p ∂law μ (Label N D), ∀ (S : ℝ≥0) (F : Configuration N D → ℝ) (j : Label N D),
    Integrable (fun z => horizonIncrement control hN hActivity v T hT hv initial F j S (p,z))
      (MarkedNoise.countingMeasure j p.2) :=
  TimeDependentGlobalCounting.ae_integrable_horizonIncrement (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv)
      initial 0 μ (ae_exhaustive control hN hActivity v T hT hv initial μ hCoupling hinit B hB hEnv hInitial)

/-- The actual global path solves the no-cutoff counting equation, with no
counting identity or exhaustion supplied as a hypothesis. -/
theorem ae_counting_identity (F : Configuration N D → ℝ) : ∀ᵐ p ∂law μ (Label N D), ∀ S : ℝ≥0,
    F (process control hN hActivity v T hT hv initial p S) - F (initial p.1) =
      ∑ j, ∫ z, horizonIncrement control hN hActivity v T hT hv initial F j S (p,z)
        ∂MarkedNoise.countingMeasure j p.2 :=
  TimeDependentGlobalCounting.ae_testFunction_counting_identity (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv)
      initial 0 μ F (ae_exhaustive control hN hActivity v T hT hv initial μ hCoupling hinit B hB hEnv hInitial)

/-- The predictable version is the genuine left limit at every positive time. -/
theorem ae_tendsto_preState : ∀ᵐ p ∂law μ (Label N D), ∀ t : ℝ, 0 < t →
    Tendsto (process control hN hActivity v T hT hv initial p) (𝓝[<] t)
      (𝓝 (preState control hN hActivity v T hT hv initial p t)) :=
  TimeDependentGlobalCounting.ae_tendsto_preState (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q v T) (exists_uniform_rate_bounds control hN hActivity v T hT hv)
      initial 0 μ (ae_exhaustive control hN hActivity v T hT hv initial μ hCoupling hinit B hB hEnv hInitial)

/-- All configuration coordinate equations hold together on one event. -/
theorem ae_coordinate_counting_identity : ∀ᵐ p ∂law μ (Label N D),
    ∀ i : Fin N × Fin D, ∀ S : ℝ≥0,
    ((process control hN hActivity v T hT hv initial p S) i.1 i.2 : ℝ) - (initial p.1 i.1 i.2 : ℝ) =
      ∑ j, ∫ z, horizonIncrement control hN hActivity v T hT hv initial
        (fun x => (x i.1 i.2 : ℝ)) j S (p,z) ∂MarkedNoise.countingMeasure j p.2 :=
  ae_all_iff.mpr (fun i => ae_counting_identity control hN hActivity v T hT hv initial μ
    hCoupling hinit B hB hEnv hInitial (fun x => (x i.1 i.2 : ℝ)))

end CarryingCapacity.DeterministicEnvironmentConfiguration
