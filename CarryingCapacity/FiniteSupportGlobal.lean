import CarryingCapacity.FiniteSupportGeometry
import CarryingCapacity.ActualGlobalCounting
import CarryingCapacity.FrozenIntensity

/-!
# Integrability of global finite-support test increments

The finite backward influence set of a test function controls every nonzero
increment of the actual global particle process. A deterministic bound on the
rates there supplies a finite time-height box. The unrestricted global
integrand equals the finite-region integrand pointwise, so deterministic
product integrability follows from actual predictable pre-state measurability.
No expected jump-activity bound or initial Lyapunov moment is assumed here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal

namespace CarryingCapacity.FiniteSupportGlobal
open ConfigurationLocalization FiniteSupportGeometry MarkedIntensity PredictableSets

variable {A : Type*} [MeasurableSpace A] {N D : ℕ}
  {κ : MomentScale} {q : Rates D (MomentLaw κ D)} (control : LyapunovControl κ q)
  (hN : 0 < N) (initial : A → Configuration N D)
  (F : Configuration N D → ℝ) (hF : (Function.support F).Finite)

/-- The finite test-support region supplies a positive deterministic rate cutoff. -/
def rateCap : ℝ :=
  Classical.choose (FrozenProcess.exists_positive_rate_bound (influence F hF) (rate κ q hN))

theorem rateCap_positive : 0 < rateCap (q := q) hN F hF :=
  (Classical.choose_spec (FrozenProcess.exists_positive_rate_bound (influence F hF) (rate κ q hN))).1

theorem rate_le_cap (z : Configuration N D) (hz : z ∈ influence F hF) (j : Label N D) :
    rate κ q hN j z ≤ rateCap (q := q) hN F hF :=
  (Classical.choose_spec (FrozenProcess.exists_positive_rate_bound (influence F hF) (rate κ q hN))).2 z hz j

/-- The unrestricted accepted-increment field of the actual global particle process. -/
def integrand (j : Label N D) (T : ℝ) :
    CommonInitialNoise.Sample A (Label N D) × (ℝ × ℝ) → ℝ :=
  GlobalLocalizedCountingIdentity.horizonIncrement
    (lyapunov control) (finite_sublevel control hN) jump (rate κ q hN) initial 0 F j T

omit [MeasurableSpace A] in
/-- All nonzero increments already lie in a deterministic finite region and
below a deterministic rate cap, with equality on every sample and marked point. -/
theorem integrand_eq_localized (j : Label N D) (T : ℝ) :
    integrand control hN initial F j T =
      FrozenIntensity.localizedIncrement (influence F hF) jump (rate κ q hN) F j
        (fun p => GlobalLocalizedCountingIdentity.preState
          (lyapunov control) (finite_sublevel control hN) jump (rate κ q hN) initial 0 p.1 p.2.1)
        T (rateCap (q := q) hN F hF) := by
  funext p
  rcases p with ⟨p, ⟨t,u⟩⟩
  rw [integrand, GlobalLocalizedCountingIdentity.horizonIncrement_apply]
  let z := GlobalLocalizedCountingIdentity.preState
    (lyapunov control) (finite_sublevel control hN) jump (rate κ q hN) initial 0 p t
  change (if t ∈ Ioc 0 T ∧ u ≤ rate κ q hN j z then F (jump j z) - F z else 0) =
    (if t ∈ Ioc 0 T ∧ z ∈ influence F hF ∧ u ≤ rateCap (q := q) hN F hF ∧ u ≤ rate κ q hN j z
      then F (jump j z) - F z else 0)
  by_cases hz : z ∈ influence F hF
  · have hh : u ≤ rateCap (q := q) hN F hF ∧ u ≤ rate κ q hN j z ↔ u ≤ rate κ q hN j z :=
      ⟨And.right, fun h => ⟨h.trans (rate_le_cap (q := q) hN F hF z hz j),h⟩⟩
    simp only [hz, true_and, hh]
  · simp only [hz, false_and, and_false, if_false,
      increment_eq_zero_of_not_mem F hF z hz j, ite_self]

omit [MeasurableSpace A] in
/-- A deterministic constant on a deterministic time-height box bounds the
actual unrestricted global test-function increment. -/
theorem norm_integrand_le (j : Label N D) (T : ℝ)
    (p : CommonInitialNoise.Sample A (Label N D) × (ℝ × ℝ)) :
    ‖integrand control hN initial F j T p‖ ≤
      (univ ×ˢ (Ioc 0 T ×ˢ Iic (rateCap (q := q) hN F hF))).indicator
        (fun _ => FrozenIntensity.incrementBound (influence F hF) jump F j) p := by
  rw [integrand_eq_localized control hN initial F hF j T]
  exact FrozenIntensity.norm_localizedIncrement_le _ _ _ _ _ _ _ _ _

/-- Predictability of the actual field is already established for the global pre-state. -/
theorem measurable_integrand (hinit : Measurable initial) (j : Label N D) (T : ℝ) :
    Measurable[predictable (CommonInitialNoise.filtration A (Label N D))]
      (integrand control hN initial F j T) :=
  GlobalLocalizedCountingIdentity.measurable_horizonIncrement
    (lyapunov control) (finite_sublevel control hN) jump (rate κ q hN) initial 0 hinit F j T

include hF

/-- Finite backward test support proves deterministic product integrability
for the actual global counting integrand, without an expected-activity input. -/
theorem integrable_horizonIncrement (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (j : Label N D) (T : ℝ) :
    Integrable (integrand control hN initial F j T)
      ((CommonInitialNoise.law μ (Label N D)).prod (positiveVolume.prod positiveVolume)) := by
  rw [integrand_eq_localized control hN initial F hF j T]
  exact FrozenIntensity.integrable_localizedIncrement
    (CommonInitialNoise.law μ (Label N D)) (influence F hF) jump (rate κ q hN) F j _
    ((GlobalLocalizedCountingIdentity.measurable_preState (lyapunov control)
      (finite_sublevel control hN) jump (rate κ q hN) initial 0 hinit).mono (predictable_le _) le_rfl)
    T (rateCap (q := q) hN F hF)

/-- F evaluated at the actual global state is integrable under any initial
probability law, since finite support supplies a global uniform bound. -/
theorem integrable_testFunction_at (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (t : ℝ) :
    Integrable (fun p => F (ConfigurationNonexplosion.process control hN initial p t))
      (CommonInitialNoise.law μ (Label N D)) := by
  have hp := (ConfigurationNonexplosion.measurable_process control hN initial hinit).comp
    (measurable_id.prodMk (measurable_const (a := t)))
  exact (integrable_const (functionBound F hF)).mono'
    ((measurable_of_countable F).comp hp).aestronglyMeasurable
    (Eventually.of_forall (fun p => norm_le_functionBound F hF _))

/-- The raw empirical generator of F evaluated along the actual global path
is integrable, despite allowing globally unbounded particle rates. -/
theorem integrable_generator_at (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (t : ℝ) :
    Integrable (fun p => generator κ q hN F
      (ConfigurationNonexplosion.process control hN initial p t))
      (CommonInitialNoise.law μ (Label N D)) := by
  have hp := (ConfigurationNonexplosion.measurable_process control hN initial hinit).comp
    (measurable_id.prodMk (measurable_const (a := t)))
  exact (integrable_const (generatorBound κ q hN F hF)).mono'
    ((measurable_of_countable (generator κ q hN F)).comp hp).aestronglyMeasurable
    (Eventually.of_forall (fun p => norm_generator_le κ q hN F hF _))

end CarryingCapacity.FiniteSupportGlobal
