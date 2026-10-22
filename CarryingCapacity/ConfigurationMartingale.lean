import CarryingCapacity.PredictableCountingMartingale
import CarryingCapacity.GlobalHistoryIntegral
import CarryingCapacity.ArbitraryInitialNonexplosion

/-!
# The actual particle generator martingale

The finite-support backward-influence estimate proves integrability of the
actual predictable counting integrands. The global counting equation then
implies the martingale property in the initial-record/noise history filtration.
The compensator is identified with the time integral of the raw empirical
generator along the current state, almost surely at each horizon.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal

namespace CarryingCapacity.ConfigurationMartingale
open ConfigurationLocalization CommonInitialNoise MarkedIntensity

variable {A : Type*} [MeasurableSpace A] {N D : ℕ}
  {κ : MomentScale} {q : Rates D (MomentLaw κ D)} (control : LyapunovControl κ q)
  (hN : 0 < N) (initial : A → Configuration N D) (F : Configuration N D → ℝ)

/-- The actual global accepted jump increment, with no spatial cutoff. -/
def increment (j : Label N D) :
    InitialPredictableCompensation.SamplePoint A (Label N D) → ℝ :=
  GlobalLocalizedCountingIdentity.jumpIncrement (lyapunov control)
    (finite_sublevel control hN) jump (rate κ q hN) initial 0 F j

/-- A raw adapted version of the actual compensated test observable. -/
def martingaleProcess (t : ℝ≥0) (p : Sample A (Label N D)) : ℝ :=
  PredictableCountingMartingale.compensated
    (fun t p => F (ConfigurationNonexplosion.process control hN initial p t))
    (fun p => F (initial p.1)) (increment control hN initial F) t p

/-- The usual current-state formula for the generator martingale. -/
def generatorProcess (t : ℝ≥0) (p : Sample A (Label N D)) : ℝ :=
  F (ConfigurationNonexplosion.process control hN initial p t) - F (initial p.1) -
    ∫ s in Ioc 0 (t : ℝ), generator κ q hN F
      (ConfigurationNonexplosion.process control hN initial p s) ∂positiveVolume

variable (hF : (Function.support F).Finite)
  (μ : Measure A) [IsProbabilityMeasure μ] (hinit : Measurable initial)

include hinit

/-- Actual global increments are predictable with respect to the constructed history. -/
theorem measurable_increment (j : Label N D) :
    Measurable[PredictableSets.predictable (filtration A (Label N D))]
      (increment control hN initial F j) :=
  GlobalLocalizedCountingIdentity.measurable_jumpIncrement (lyapunov control)
    (finite_sublevel control hN) jump (rate κ q hN) initial 0 hinit F j

include hF

/-- Product integrability is derived from finite support, not assumed as a
martingale-problem hypothesis. -/
theorem integrable_increment_window (j : Label N D) (t : ℝ≥0) :
    Integrable (InitialConditionalCompensation.window (increment control hN initial F j) 0 t)
      (InitialPredictableIntegral.productIntensity μ (Label N D)) :=
  FiniteSupportGlobal.integrable_horizonIncrement control hN initial F hF μ hinit j t

/-- The actual nonexplosive empirical particle process solves the
finite-support generator martingale problem in its raw history filtration. -/
theorem martingale :
    Martingale (martingaleProcess control hN initial F)
      (PredictableCountingMartingale.nonnegativeFiltration A (Label N D)) (law μ (Label N D)) := by
  apply PredictableCountingMartingale.martingale_compensated _ _ _ μ
    (measurable_increment control hN initial F hinit)
    (integrable_increment_window control hN initial F hF μ hinit)
  · intro t
    filter_upwards [ArbitraryInitialNonexplosion.configuration_counting_identity
      control hN initial μ F] with p hp
    exact hp t
  · intro t
    exact ((measurable_of_countable F).comp
      (ConfigurationNonexplosion.measurable_process_at control hN initial hinit t)).stronglyMeasurable
  · exact ((measurable_of_countable F).comp
      (hinit.comp (measurable_initial_at 0))).stronglyMeasurable

/-- The proved raw adapted martingale agrees almost surely at each time with
the paper's current-state generator expression. -/
theorem ae_eq_generatorProcess (t : ℝ≥0) :
    martingaleProcess control hN initial F t =ᵐ[law μ (Label N D)]
      generatorProcess control hN initial F t := by
  filter_upwards [GlobalFiniteSupportDrift.ae_sum_intensity_eq_timeGenerator_of_exhaustion
    control hN initial F hF μ hinit
      (ArbitraryInitialNonexplosion.configuration_exhaustive control hN initial μ) t] with p hp
  exact congrArg (fun x => F (ConfigurationNonexplosion.process control hN initial p t) -
    F (initial p.1) - x) hp

omit hF [IsProbabilityMeasure μ] in
/-- The classical current-state generator expression is itself raw-adapted;
this uses all-sample history reconstruction, not an AE-measurability transfer. -/
theorem adapted_generatorProcess :
    Adapted (PredictableCountingMartingale.nonnegativeFiltration A (Label N D))
      (generatorProcess control hN initial F) := by
  intro t
  have hx := ((measurable_of_countable F).comp
    (ConfigurationNonexplosion.measurable_process_at control hN initial hinit t)).stronglyMeasurable
  have hy := ((measurable_of_countable F).comp
    (hinit.comp (measurable_initial_at (J := Label N D) t))).stronglyMeasurable
  have hi := (GlobalHistoryIntegral.measurable_timeGenerator
    control hN initial hinit F 0 t).stronglyMeasurable
  exact (hx.sub hy).sub hi

/-- The paper's actual current-state generator formula is a martingale in
the raw history filtration of the constructed particle system. -/
theorem generator_martingale :
    Martingale (generatorProcess control hN initial F)
      (PredictableCountingMartingale.nonnegativeFiltration A (Label N D)) (law μ (Label N D)) := by
  refine ⟨adapted_generatorProcess control hN initial F hinit, ?_⟩
  intro s t hst
  exact (condExp_congr_ae (ae_eq_generatorProcess control hN initial F hF μ hinit t).symm).trans
    (((martingale control hN initial F hF μ hinit).condExp_ae_eq hst).trans
      (ae_eq_generatorProcess control hN initial F hF μ hinit s))

/-- The actual current-state generator expression is integrable. -/
theorem integrable_generatorProcess (t : ℝ≥0) :
    Integrable (generatorProcess control hN initial F t) (law μ (Label N D)) :=
  ((martingale control hN initial F hF μ hinit).integrable t).congr
    (ae_eq_generatorProcess control hN initial F hF μ hinit t)

omit hF [IsProbabilityMeasure μ] hinit in
/-- The compensated process starts at zero almost surely. -/
theorem ae_zero : martingaleProcess control hN initial F 0 =ᵐ[law μ (Label N D)] fun _ => 0 := by
  filter_upwards [ConfigurationNonexplosion.ae_process_zero control hN initial μ] with p hp
  simp [martingaleProcess, PredictableCountingMartingale.compensated,
    InitialConditionalCompensation.window, PredictableSets.rectangle, hp]

/-- Dynkin's expectation identity for the genuine unrestricted particle system. -/
theorem expectation_generatorProcess_eq_zero (t : ℝ≥0) :
    ∫ p, generatorProcess control hN initial F t p ∂law μ (Label N D) = 0 := by
  have hm := martingale control hN initial F hF μ hinit
  have hc := hm.condExp_ae_eq (show (0 : ℝ≥0) ≤ t from zero_le _)
  have hi := integral_condExp (μ := law μ (Label N D)) (f := martingaleProcess control hN initial F t)
    ((PredictableCountingMartingale.nonnegativeFiltration A (Label N D)).le 0)
  rw [← integral_congr_ae (ae_eq_generatorProcess control hN initial F hF μ hinit t)]
  rw [← hi]
  rw [integral_congr_ae hc, integral_congr_ae (ae_zero control hN initial F μ), integral_zero]

end CarryingCapacity.ConfigurationMartingale
