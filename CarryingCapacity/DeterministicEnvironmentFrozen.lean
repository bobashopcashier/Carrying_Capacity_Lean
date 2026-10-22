import CarryingCapacity.DeterministicEnvironmentRates
import CarryingCapacity.TimeDependentRateLocalization
import CarryingCapacity.TimeDependentGeneratorMartingale

/-!
# Actual frozen paths along continuous moment-law environments

The paper's coupling and activity assumptions supply every coefficient
measurability and finite-active-region rate bound used here. The environment
is clamped to its endpoints outside the selected horizon, and the rate cap
is chosen from the proved compact-horizon bound. The resulting process is the
actual common-noise recursion, with adaptedness, càdlàg paths, a counting
identity, Dynkin's formula, and a raw-filtration generator martingale.

This is a finite-active-set construction. It does not assert global
nonexplosion or uniqueness of the deterministic-environment forward law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators NNReal Topology

namespace CarryingCapacity.DeterministicEnvironmentFrozen
open DeterministicEnvironmentRates CommonInitialNoise

variable {D : ℕ} (κ : MomentScale) (q : Rates D (MomentLaw κ D))
  (hActivity : MomentActivityBound κ q) (active : Finset (State D))
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hv : ContinuousOn v (Icc 0 T))

/-- A genuine strictly positive bound obtained from the activity assumption. -/
def rateCap : ℝ := Classical.choose
  (exists_positive_rate_bound_on_Icc κ q hActivity active v T hv)

theorem rateCap_pos : 0 < rateCap κ q hActivity active v T hv :=
  (Classical.choose_spec (exists_positive_rate_bound_on_Icc κ q hActivity active v T hv)).1

theorem rate_le_cap (x : State D) (hx : x ∈ active) (j : Jump D)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    q.rate j x (v t) ≤ rateCap κ q hActivity active v T hv :=
  (Classical.choose_spec (exists_positive_rate_bound_on_Icc κ q hActivity active v T hv)).2 x hx j t ht

/-- The rate is extended in time by keeping the environment at its endpoints. -/
def timeRate (j : Jump D) (t : ℝ) (x : State D) : ℝ :=
  q.rate j x (v (max 0 (min t T)))

theorem timeRate_nonnegative (j : Jump D) (t : ℝ) (x : State D) :
    0 ≤ timeRate κ q v T j t x := q.nonnegative _ _ _

theorem timeRate_eq (j : Jump D) (t : ℝ) (ht : t ∈ Icc 0 T) (x : State D) :
    timeRate κ q v T j t x = q.rate j x (v t) := by
  simp only [timeRate, min_eq_left ht.2, max_eq_right ht.1]

theorem timeRate_le_cap (hT : 0 ≤ T) (x : State D) (hx : x ∈ active)
    (j : Jump D) (t : ℝ) :
    timeRate κ q v T j t x ≤ rateCap κ q hActivity active v T hv :=
  rate_le_cap κ q hActivity active v T hv x hx j _
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

include hv in
theorem measurable_timeRate (hCoupling : MomentCouplingBound κ q) (hT : 0 ≤ T)
    (j : Jump D) (x : State D) : Measurable (fun t => timeRate κ q v T j t x) :=
  measurable_clamped_timeRate κ q hCoupling v T hT hv j x

variable {A : Type*} [MeasurableSpace A] (initial : A → State D)

/-- The actual frozen path on the independent initial-record/noise product. -/
def process (p : Sample A (Jump D)) (t : ℝ) : State D :=
  TimeDependentInitial.process active Jump.advance (timeRate κ q v T) initial
    (rateCap κ q hActivity active v T hv) p t

/-- The actual strict-past predictable version, with fixed zero fallback. -/
def preState (p : Sample A (Jump D)) (t : ℝ) : State D :=
  TimeDependentInitial.preState active Jump.advance (timeRate κ q v T) initial
    (rateCap κ q hActivity active v T hv) 0 p t

/-- The accepted test-function increment against the original counting measure. -/
def horizonIncrement (F : State D → ℝ) (j : Jump D) (t : ℝ) :
    Sample A (Jump D) × (ℝ × ℝ) → ℝ :=
  TimeDependentInitialCompensation.horizonIncrement active Jump.advance (timeRate κ q v T)
    initial (rateCap κ q hActivity active v T hv) 0 F j t

/-- The generator of the actual frozen path, with the selected clamped environment. -/
def generator (F : State D → ℝ) (t : ℝ) (x : State D) : ℝ :=
  TimeDependentGeneratorIntegral.frozenGenerator active Jump.advance (timeRate κ q v T) F t x

/-- On the original horizon this is exactly the paper's single-lineage generator,
with the active-set freezing indicator. -/
theorem generator_eq (F : State D → ℝ) (t : ℝ) (ht : t ∈ Icc 0 T) (x : State D) :
    generator κ q active v T F t x =
      if x ∈ active then q.generator (v t) F x else 0 := by
  simp only [generator, TimeDependentGeneratorIntegral.frozenGenerator,
    FrozenProcess.frozenGenerator, Rates.generator, timeRate_eq κ q v T _ t ht]

/-- Joint measurability follows from the coupling assumption, not a new rate premise. -/
theorem measurable_process (hCoupling : MomentCouplingBound κ q) (hT : 0 ≤ T)
    (hinit : Measurable initial) :
    Measurable (fun p : Sample A (Jump D) × ℝ =>
      process κ q hActivity active v T hv initial p.1 p.2) :=
  TimeDependentInitial.measurable_process active Jump.advance (timeRate κ q v T) initial
    (measurable_timeRate κ q v T hv hCoupling hT) hinit _

/-- The actual path is measurable in its raw initial-record/noise history. -/
theorem measurable_process_at (hCoupling : MomentCouplingBound κ q) (hT : 0 ≤ T)
    (hinit : Measurable initial) (t : ℝ) :
    Measurable[filtration A (Jump D) t]
      (fun p => process κ q hActivity active v T hv initial p t) :=
  TimeDependentInitial.measurable_process_at active Jump.advance (timeRate κ q v T) initial
    (measurable_timeRate κ q v T hv hCoupling hT) hinit _ t

/-- The sampled initial value is retained, with no initial moment premise. -/
theorem ae_initial (μ : Measure A) : ∀ᵐ p ∂law μ (Jump D),
    process κ q hActivity active v T hv initial p 0 = initial p.1 := by
  filter_upwards [TimeDependentInitial.ae_process_zero active Jump.advance
    (timeRate κ q v T) initial μ] with p hp
  exact hp _

/-- Càdlàg regularity of the actual finite-active path for arbitrary initial laws. -/
theorem ae_cadlag (μ : Measure A) : ∀ᵐ p ∂law μ (Jump D),
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt
      (process κ q hActivity active v T hv initial p) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : State D,
      Tendsto (process κ q hActivity active v T hv initial p) (𝓝[<] t) (𝓝 y)) := by
  filter_upwards [ae_noise μ (TimeDependentFrozenProcess.ae_process_cadlag
    active Jump.advance (timeRate κ q v T))] with p hp
  exact hp _ (initial p.1)

/-- Actual pathwise counting integrability, simultaneous in time, tests and labels. -/
theorem ae_integrable_horizonIncrement (μ : Measure A) : ∀ᵐ p ∂law μ (Jump D),
    ∀ t F j, Integrable (fun z => horizonIncrement κ q hActivity active v T hv initial F j t (p,z))
      (MarkedNoise.countingMeasure j p.2) := by
  filter_upwards [TimeDependentInitialCounting.ae_integrable_horizonIncrement active Jump.advance
    (timeRate κ q v T) initial μ] with p hp
  exact fun t F j => hp _ 0 t F j

/-- The exact frozen counting equation against the actual common marked noise. -/
theorem ae_counting_identity (μ : Measure A) (F : State D → ℝ) : ∀ᵐ p ∂law μ (Jump D),
    ∀ t, F (process κ q hActivity active v T hv initial p t) - F (initial p.1) =
      ∑ j, ∫ z, horizonIncrement κ q hActivity active v T hv initial F j t (p,z)
        ∂MarkedNoise.countingMeasure j p.2 := by
  filter_upwards [TimeDependentInitialCounting.ae_testFunction_counting_identity active
    Jump.advance (timeRate κ q v T) initial μ F,
    ae_initial κ q hActivity active v T hv initial μ] with p hp hzero
  intro t
  have he := hp (rateCap κ q hActivity active v T hv) 0 t
  change F (process κ q hActivity active v T hv initial p t) -
    F (process κ q hActivity active v T hv initial p 0) = _ at he
  rw [hzero] at he
  exact he

variable (μ : Measure A) [IsProbabilityMeasure μ]
  (hCoupling : MomentCouplingBound κ q) (hT : 0 ≤ T) (hinit : Measurable initial)
include hCoupling hT hinit

/-- Signed changes are genuinely integrable without an initial test moment. -/
theorem integrable_change (F : State D → ℝ) (t : ℝ) :
    Integrable (fun p => F (process κ q hActivity active v T hv initial p t) - F (initial p.1))
      (law μ (Jump D)) :=
  TimeDependentDynkin.integrable_testFunction_change active Jump.advance (timeRate κ q v T)
    initial μ (measurable_timeRate κ q v T hv hCoupling hT) hinit _ 0 F t

/-- Dynkin's identity for the actual frozen path, with every rate assumption
supplied by the paper hypotheses and the proved compact-horizon bound. -/
theorem dynkin_change (F : State D → ℝ) (t : ℝ) :
    (∫ p, F (process κ q hActivity active v T hv initial p t) - F (initial p.1) ∂law μ (Jump D)) =
      ∫ p, ∫ s in Ioc 0 t, generator κ q active v T F s
        (process κ q hActivity active v T hv initial p s) ∂MarkedIntensity.positiveVolume
          ∂law μ (Jump D) :=
  TimeDependentDynkin.dynkin_change active Jump.advance (timeRate κ q v T) initial μ
    (measurable_timeRate κ q v T hv hCoupling hT) hinit _ 0 F t
    (fun x _ j s _ => timeRate_nonnegative κ q v T j s x)
    (fun x hx j s _ => timeRate_le_cap κ q hActivity active v T hv hT x hx j s)

/-- At every time up to the selected horizon, the drift uses the original
unclamped environment and the exact paper generator. -/
theorem dynkin_change_on_horizon (F : State D → ℝ) (t : ℝ) (ht : t ≤ T) :
    (∫ p, F (process κ q hActivity active v T hv initial p t) - F (initial p.1) ∂law μ (Jump D)) =
      ∫ p, ∫ s in Ioc 0 t,
        (if process κ q hActivity active v T hv initial p s ∈ active then
          q.generator (v s) F (process κ q hActivity active v T hv initial p s) else 0)
            ∂MarkedIntensity.positiveVolume ∂law μ (Jump D) := by
  rw [dynkin_change κ q hActivity active v T hv initial μ hCoupling hT hinit F t]
  apply integral_congr_ae
  exact Eventually.of_forall (fun p => setIntegral_congr_fun measurableSet_Ioc
    (fun s hs => generator_eq κ q active v T F s ⟨hs.1.le, hs.2.trans ht⟩ _))

/-- The classical current-state generator expression is a martingale in the
raw filtration. It needs no initial test-function moment. -/
theorem generator_martingale (F : State D → ℝ) :
    Martingale
      (TimeDependentMartingale.generatorProcess active Jump.advance (timeRate κ q v T)
        initial (rateCap κ q hActivity active v T hv) F)
      (PredictableCountingMartingale.nonnegativeFiltration A (Jump D)) (law μ (Jump D)) :=
  TimeDependentMartingale.generator_martingale active Jump.advance (timeRate κ q v T)
    initial μ (measurable_timeRate κ q v T hv hCoupling hT) hinit _ 0 F
    (fun x _ j s _ => timeRate_nonnegative κ q v T j s x)
    (fun x hx j s _ => timeRate_le_cap κ q hActivity active v T hv hT x hx j s)

end CarryingCapacity.DeterministicEnvironmentFrozen
