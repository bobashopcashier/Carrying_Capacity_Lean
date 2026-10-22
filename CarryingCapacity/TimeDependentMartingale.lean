import CarryingCapacity.TimeDependentInitialCounting
import CarryingCapacity.PredictableCountingMartingale

/-!
# Actual time-dependent frozen martingales

The accepted increment is predictable and has integrable finite time-height
support. Conditional compensation and the actual chronological counting
identity imply the martingale property for every test function. Integrability
of the initial test function is not needed for its compensated change.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators NNReal

namespace CarryingCapacity.TimeDependentMartingale
open CommonInitialNoise TimeDependentInitial TimeDependentInitialCompensation
  TimeDependentInitialCounting InitialConditionalCompensation MarkedIntensity

variable {A J E : Type*} [MeasurableSpace A] [Fintype J] [DecidableEq E]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ) (initial : A → E)

/-- The raw-adapted compensated change of the actual frozen process. -/
def martingaleProcess (C : ℝ) (e : E) (V : E → ℝ)
    (t : ℝ≥0) (p : Sample A J) : ℝ :=
  PredictableCountingMartingale.compensated
    (fun t p => V (process active jump rate initial C p t))
    (fun p => V (initial p.1)) (jumpIncrement active jump rate initial C e V) t p

omit [MeasurableSpace A] [Fintype J] [Countable E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [PolishSpace E] [BorelSpace E] in
/-- The generic predictable window is exactly the actual finite-cutoff field. -/
theorem window_eq_horizonIncrement (C : ℝ) (e : E) (V : E → ℝ) (j : J) (T : ℝ) :
    window (jumpIncrement active jump rate initial C e V j) 0 T =
      horizonIncrement active jump rate initial C e V j T := by
  funext p
  by_cases hT : p.2.1 ≤ T <;> by_cases hC : p.2.2 ≤ C <;> by_cases hp : 0 < p.2.1 <;>
    simp [window, horizonIncrement, PredictableSets.rectangle, jumpIncrement,
      Set.indicator_apply, hT, hC, hp]

variable (μ : Measure A) [IsProbabilityMeasure μ]
  (hRate : ∀ j x, Measurable (fun t => rate j t x)) (hinit : Measurable initial)
  (C : ℝ) (e : E) (V : E → ℝ)

include hRate hinit

/-- The actual event-time recursion has a compensated martingale in the raw
initial-record/noise filtration. No martingale or moment property is an input. -/
theorem martingale :
    Martingale (martingaleProcess active jump rate initial C e V)
      (PredictableCountingMartingale.nonnegativeFiltration A J) (law μ J) := by
  apply PredictableCountingMartingale.martingale_compensated _ _ _ μ
    (measurable_jumpIncrement active jump rate initial hRate hinit C e V)
  · intro j t
    rw [window_eq_horizonIncrement]
    exact integrable_horizonIncrement_product active jump rate initial μ hRate hinit C e V j t
  · intro t
    filter_upwards [ae_testFunction_counting_identity active jump rate initial μ V,
      ae_process_zero active jump rate initial μ] with p hp hz
    simp_rw [window_eq_horizonIncrement]
    simpa only [hz C] using hp C e t
  · intro t
    exact ((measurable_of_countable V).comp
      (measurable_process_at active jump rate initial hRate hinit C t)).stronglyMeasurable
  · exact ((measurable_of_countable V).comp
      (hinit.comp (measurable_initial_at 0))).stronglyMeasurable

/-- Integrability of the actual compensated change follows from compensation. -/
theorem integrable_martingaleProcess (t : ℝ≥0) :
    Integrable (martingaleProcess active jump rate initial C e V t) (law μ J) :=
  (martingale active jump rate initial μ hRate hinit C e V).integrable t

omit hRate hinit [IsProbabilityMeasure μ] [Countable E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [PolishSpace E] [BorelSpace E] in
/-- The compensated process starts at zero almost surely. -/
theorem ae_zero :
    martingaleProcess active jump rate initial C e V 0 =ᵐ[law μ J] fun _ => 0 := by
  filter_upwards [ae_process_zero active jump rate initial μ] with p hp
  simp [martingaleProcess, PredictableCountingMartingale.compensated,
    window, PredictableSets.rectangle, hp]

/-- The compensated change has zero expectation at every deterministic time. -/
theorem expectation_eq_zero (t : ℝ≥0) :
    ∫ p, martingaleProcess active jump rate initial C e V t p ∂law μ J = 0 := by
  have hm := martingale active jump rate initial μ hRate hinit C e V
  have hc := hm.condExp_ae_eq (show (0 : ℝ≥0) ≤ t from zero_le _)
  have hi := integral_condExp (μ := law μ J)
    (f := martingaleProcess active jump rate initial C e V t)
    ((PredictableCountingMartingale.nonnegativeFiltration A J).le 0)
  rw [← hi, integral_congr_ae hc,
    integral_congr_ae (ae_zero active jump rate initial μ C e V), integral_zero]

end CarryingCapacity.TimeDependentMartingale
