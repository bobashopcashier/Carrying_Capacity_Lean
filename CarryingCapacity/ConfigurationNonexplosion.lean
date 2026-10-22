import CarryingCapacity.ActualNonexplosion
import CarryingCapacity.ConfigurationLocalization

/-!
# Non-explosion for the manuscript's actual empirical particle system

The single-lineage LyapunovControl and an integrable initial empirical
Lyapunov value imply reciprocal exit tails, almost-sure localization exhaustion,
and a measurable adapted global configuration process with cadlag paths.
The configuration drift, finite sublevels, expectations and exit bounds are
all derived. This module does not assert a mean-field or propagation-of-chaos theorem.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.ConfigurationNonexplosion
open ConfigurationLocalization

variable {A : Type*} [MeasurableSpace A] {N D : ℕ}
  {κ : MomentScale} {q : Rates D (MomentLaw κ D)} (control : LyapunovControl κ q)
  (hN : 0 < N) (initial : A → Configuration N D)

/-- The actual global configuration process, patched from the genuine
common-noise localizations. Zero is only the total definition's fallback. -/
def process (p : CommonInitialNoise.Sample A (Label N D)) (t : ℝ) : Configuration N D :=
  GlobalLocalizedProcess.process (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q hN) initial 0 p t

/-- The generator hypothesis needed by the stochastic theorem follows from
the original one-lineage LyapunovControl at the actual empirical law. -/
theorem generator_affine_bound (z : Configuration N D) :
    (∑ j, rate κ q hN j z * (lyapunov control (jump j z) - lyapunov control z)) ≤
      (2 * driftConstant control) * (1 + lyapunov control z) := by
  have hd := generator_lyapunov_le control hN z
  have hC := driftConstant_nonnegative control
  change generator κ q hN (lyapunov control) z ≤ _
  nlinarith

/-- Joint raw measurability of the actual globally defined process. -/
theorem measurable_process (hinit : Measurable initial) : Measurable
    (fun p : CommonInitialNoise.Sample A (Label N D) × ℝ => process control hN initial p.1 p.2) :=
  GlobalLocalizedProcess.measurable_process (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q hN) initial 0 hinit

/-- Each global state is measurable in the initial-plus-noise history at its time. -/
theorem measurable_process_at (hinit : Measurable initial) (t : ℝ) :
    Measurable[CommonInitialNoise.filtration A (Label N D) t]
      (fun p => process control hN initial p t) :=
  GlobalLocalizedProcess.measurable_process_at (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q hN) initial 0 hinit t

/-- The global configuration has the prescribed initial state without
any initial moment or initial-map measurability requirement. -/
theorem ae_process_zero (μ : Measure A) :
    ∀ᵐ p ∂CommonInitialNoise.law μ (Label N D), process control hN initial p 0 = initial p.1 :=
  ActualNonexplosion.ae_global_initial (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q hN) initial 0 μ

variable (μ : Measure A) [IsProbabilityMeasure μ] (hinit : Measurable initial)
  (hV : Integrable (fun a => lyapunov control (initial a)) μ)

include hinit hV

/-- The model's actual exit probability has an explicit bound, uniform in
localization level, with the single-lineage drift constant. -/
theorem exit_probability_le (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    (CommonInitialNoise.law μ (Label N D))
      {p | exit control hN initial n p ≤ ENNReal.ofReal T} ≤
        ENNReal.ofReal ((1 + ∫ a, lyapunov control (initial a) ∂μ) *
          Real.exp ((2 * driftConstant control) * T) - 1) / ((n + 1 : ℕ) : ℝ≥0∞) :=
  ActualNonexplosion.exit_probability_le (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q hN) initial 0 μ hinit (2 * driftConstant control)
    (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
    (lyapunov_nonnegative control) (fun z j => rate_nonnegative κ q hN j z) hV
    (generator_affine_bound control hN) n T hT

/-- Actual exits tend beyond every finite horizon almost surely. No
expectation, exit bound, or exhaustion premise is required. -/
theorem ae_exhaustive : ∀ᵐ p ∂CommonInitialNoise.law μ (Label N D), ∀ T : ℝ≥0, ∃ n : ℕ,
    (T : ℝ≥0∞) < exit control hN initial n p :=
  ActualNonexplosion.ae_exhaustive (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q hN) initial 0 μ hinit (2 * driftConstant control)
    (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
    (lyapunov_nonnegative control) (fun z j => rate_nonnegative κ q hN j z) hV
    (generator_affine_bound control hN)

/-- On each finite horizon the actual global particle path is eventually
identical to every sufficiently high common-noise localization. -/
theorem ae_agrees_on_horizon : ∀ᵐ p ∂CommonInitialNoise.law μ (Label N D),
    ∀ T : ℝ≥0, ∃ n, ∀ m, n ≤ m → ∀ t : ℝ, 0 ≤ t → t ≤ T →
      process control hN initial p t = path control hN initial m p t :=
  ActualNonexplosion.ae_global_agrees_on_horizon (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q hN) initial 0 μ hinit (2 * driftConstant control)
    (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
    (lyapunov_nonnegative control) (fun z j => rate_nonnegative κ q hN j z) hV
    (generator_affine_bound control hN)

/-- The actual global configuration process has cadlag paths. -/
theorem ae_cadlag : ∀ᵐ p ∂CommonInitialNoise.law μ (Label N D),
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (process control hN initial p) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ z : Configuration N D,
      Tendsto (process control hN initial p) (𝓝[<] t) (𝓝 z)) :=
  ActualNonexplosion.ae_global_cadlag (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q hN) initial 0 μ hinit (2 * driftConstant control)
    (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
    (lyapunov_nonnegative control) (fun z j => rate_nonnegative κ q hN j z) hV
    (generator_affine_bound control hN)

/-- Every bounded horizon has only finitely many possible change times,
proved for the actual global particle path from the model assumptions. -/
theorem ae_finite_activity : ∀ᵐ p ∂CommonInitialNoise.law μ (Label N D),
    ∀ T : ℝ≥0, ∃ times : Finset ℝ, (times : Set ℝ) ⊆ Ioc 0 T ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        (∀ u ∈ times, u ∉ Ioc s t) → process control hN initial p s = process control hN initial p t := by
  filter_upwards [ActualNonexplosion.ae_global_finite_activity (lyapunov control)
    (finite_sublevel control hN) jump (rate κ q hN) initial 0 μ hinit
    (2 * driftConstant control) (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
    (lyapunov_nonnegative control) (fun z j => rate_nonnegative κ q hN j z) hV
    (generator_affine_bound control hN)] with p hp
  intro T
  obtain ⟨n, hn, hconst⟩ := hp T
  exact ⟨GlobalLocalizedActivity.horizonTimes (lyapunov control) (finite_sublevel control hN)
    (rate κ q hN) n p T, hn, hconst⟩

end CarryingCapacity.ConfigurationNonexplosion
