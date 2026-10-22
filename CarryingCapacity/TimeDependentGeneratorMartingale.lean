import CarryingCapacity.TimeDependentMartingale
import CarryingCapacity.TimeDependentDynkin
import CarryingCapacity.TimeDependentHistoryIntegral

/-!
# Current-state generator martingales with time-dependent rates

The usual generator formula is raw-adapted by exact history reconstruction.
Height integration identifies it with the proved compensated counting
martingale. Bounds are needed only on active states and positive times;
the time-localized construction supplies such bounds on each chosen horizon.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators NNReal

namespace CarryingCapacity.TimeDependentMartingale
open CommonInitialNoise TimeDependentInitial TimeDependentInitialCompensation
  TimeDependentGeneratorIntegral MarkedIntensity

variable {A J E : Type*} [MeasurableSpace A] [Fintype J] [DecidableEq E]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ) (initial : A → E)

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

/-- The current-state generator expression of the actual time-dependent path. -/
def generatorProcess (C : ℝ) (V : E → ℝ) (t : ℝ≥0) (p : Sample A J) : ℝ :=
  V (process active jump rate initial C p t) - V (initial p.1) -
    ∫ s in Ioc 0 (t : ℝ), frozenGenerator active jump rate V s
      (process active jump rate initial C p s) ∂positiveVolume

variable (μ : Measure A) [IsProbabilityMeasure μ]
  (hRate : ∀ j x, Measurable (fun t => rate j t x)) (hinit : Measurable initial)
  (C : ℝ) (e : E) (V : E → ℝ)

include hRate hinit

/-- Generator identification needs the rate cap only on this finite horizon. -/
theorem ae_eq_generatorProcess (t : ℝ≥0)
    (hq : ∀ x ∈ active, ∀ j s, s ∈ Ioc 0 (t : ℝ) → 0 ≤ rate j s x)
    (hbound : ∀ x ∈ active, ∀ j s, s ∈ Ioc 0 (t : ℝ) → rate j s x ≤ C) :
    martingaleProcess active jump rate initial C e V t =ᵐ[law μ J]
      generatorProcess active jump rate initial C V t := by
  filter_upwards [TimeDependentDynkin.ae_sum_horizon_intensity_eq_timeGenerator
    active jump rate initial μ hRate hinit C e V t hq hbound] with p hp
  unfold martingaleProcess PredictableCountingMartingale.compensated generatorProcess
  simp_rw [window_eq_horizonIncrement]
  exact congrArg (fun x => V (process active jump rate initial C p t) - V (initial p.1) - x) hp

omit [TopologicalSpace E] [PolishSpace E] [BorelSpace E] in
/-- The classical formula itself is adapted to the raw filtration, rather
than being assigned adaptedness by an almost-sure replacement. -/
theorem adapted_generatorProcess :
    Adapted (PredictableCountingMartingale.nonnegativeFiltration A J)
      (generatorProcess active jump rate initial C V) := by
  intro t
  have hx := ((measurable_of_countable V).comp
    (measurable_process_at active jump rate initial hRate hinit C t)).stronglyMeasurable
  have hy := ((measurable_of_countable V).comp
    (hinit.comp (measurable_initial_at (J := J) t))).stronglyMeasurable
  have hf (x : E) : Measurable (fun s => frozenGenerator active jump rate V s x) :=
    (measurable_frozenGenerator active jump rate hRate V).comp
      (measurable_id.prodMk measurable_const)
  have hi := (TimeDependentHistoryIntegral.measurable_timeIntegral active jump rate initial
    hRate hinit C (frozenGenerator active jump rate V) hf positiveVolume 0 t).stronglyMeasurable
  exact (hx.sub hy).sub hi

include e

/-- Under the actual active-region rate cap, the current-state generator
formula is a martingale in the constructed raw history filtration. -/
theorem generator_martingale
    (hq : ∀ x ∈ active, ∀ j s, 0 < s → 0 ≤ rate j s x)
    (hbound : ∀ x ∈ active, ∀ j s, 0 < s → rate j s x ≤ C) :
    Martingale (generatorProcess active jump rate initial C V)
      (PredictableCountingMartingale.nonnegativeFiltration A J) (law μ J) := by
  have he (t : ℝ≥0) := ae_eq_generatorProcess active jump rate initial μ hRate hinit C e V t
    (fun x hx j s hs => hq x hx j s hs.1) (fun x hx j s hs => hbound x hx j s hs.1)
  refine ⟨adapted_generatorProcess active jump rate initial hRate hinit C V, ?_⟩
  intro s t hst
  exact (condExp_congr_ae (he t).symm).trans
    (((martingale active jump rate initial μ hRate hinit C e V).condExp_ae_eq hst).trans (he s))

/-- Integrability of the actual generator expression needs only horizon-local bounds. -/
theorem integrable_generatorProcess (t : ℝ≥0)
    (hq : ∀ x ∈ active, ∀ j s, s ∈ Ioc 0 (t : ℝ) → 0 ≤ rate j s x)
    (hbound : ∀ x ∈ active, ∀ j s, s ∈ Ioc 0 (t : ℝ) → rate j s x ≤ C) :
    Integrable (generatorProcess active jump rate initial C V t) (law μ J) :=
  (integrable_martingaleProcess active jump rate initial μ hRate hinit C e V t).congr
    (ae_eq_generatorProcess active jump rate initial μ hRate hinit C e V t hq hbound)

/-- The usual current-state generator martingale has zero expectation. -/
theorem expectation_generatorProcess_eq_zero (t : ℝ≥0)
    (hq : ∀ x ∈ active, ∀ j s, s ∈ Ioc 0 (t : ℝ) → 0 ≤ rate j s x)
    (hbound : ∀ x ∈ active, ∀ j s, s ∈ Ioc 0 (t : ℝ) → rate j s x ≤ C) :
    ∫ p, generatorProcess active jump rate initial C V t p ∂law μ J = 0 := by
  rw [← integral_congr_ae
    (ae_eq_generatorProcess active jump rate initial μ hRate hinit C e V t hq hbound)]
  exact expectation_eq_zero active jump rate initial μ hRate hinit C e V t

end CarryingCapacity.TimeDependentMartingale
