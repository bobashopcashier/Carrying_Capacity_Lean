import CarryingCapacity.ActualGlobalCounting
import CarryingCapacity.TimeDependentNonexplosion
import CarryingCapacity.TimeDependentGlobalUniqueness

/-!
# The interacting configuration in the time-dependent construction

The actual empirical configuration rates are constant in their time argument.
Their finite active-region bounds and averaged Lyapunov drift discharge the
time-dependent construction hypotheses. Pathwise uniqueness then identifies
that construction with the existing autonomous interacting particle process on
the same initial records and the same original counting measures.

This is a construction-identification bridge for the localized synchronous
comparison. No empirical convergence or stopped comparison estimate is assumed
or concluded here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.ConfigurationTimeDependent
open CommonInitialNoise ConfigurationLocalization

variable {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}

/-- The empirical configuration rate, regarded as a time-dependent rate. -/
def timeRate (κ : MomentScale) (q : Rates D (MomentLaw κ D)) (hN : 0 < N)
    (j : Label N D) (_t : ℝ) (z : Configuration N D) : ℝ := rate κ q hN j z

@[simp] theorem timeRate_apply (hN : 0 < N) (j : Label N D) (t : ℝ)
    (z : Configuration N D) : timeRate κ q hN j t z = q.rate j.2 (z j.1) (empiricalLaw κ hN z) := rfl

theorem timeRate_nonnegative (hN : 0 < N) (j : Label N D) (t : ℝ)
    (z : Configuration N D) : 0 ≤ timeRate κ q hN j t z := rate_nonnegative κ q hN j z

theorem measurable_timeRate (hN : 0 < N) :
    ∀ j : Label N D, ∀ z, Measurable (fun t => timeRate κ q hN j t z) :=
  fun _ _ => measurable_const

variable (control : LyapunovControl κ q) (hN : 0 < N)

/-- The finite active-region cap is the one already derived for the actual
empirical rates; it holds at every real time. -/
theorem uniform_rate_bounds : ∀ n : ℕ, ∃ C : ℝ,
    ∀ z ∈ LyapunovLocalization.active (lyapunov control) (finite_sublevel control hN) n,
      ∀ j t, timeRate κ q hN j t z ≤ C := by
  intro n
  exact ⟨rateBound control hN n, fun z hz j _ => rate_le_bound control hN n z hz j⟩

/-- The actual averaged drift is unchanged when the rate gains a time argument. -/
theorem generator_affine_bound (z : Configuration N D) (t : ℝ) :
    (∑ j, timeRate κ q hN j t z * (lyapunov control (jump j z) - lyapunov control z)) ≤
      (2 * driftConstant control) * (1 + lyapunov control z) :=
  ConfigurationNonexplosion.generator_affine_bound control hN z

variable {A : Type*} [MeasurableSpace A] (initial : A → Configuration N D)

/-- The actual time-dependent construction with the empirical configuration rates. -/
def process (p : Sample A (Label N D)) (t : ℝ) : Configuration N D :=
  TimeDependentGlobalProcess.process (lyapunov control) (finite_sublevel control hN)
    jump (timeRate κ q hN) (uniform_rate_bounds control hN) initial 0 p t

/-- Its genuine canonical localization exits. -/
def exit (n : ℕ) (p : Sample A (Label N D)) : ℝ≥0∞ :=
  TimeDependentLocalization.exit (lyapunov control) (finite_sublevel control hN)
    jump (timeRate κ q hN) (uniform_rate_bounds control hN) initial n p

/-- The predictable version of its pre-jump configuration. -/
def preState (p : Sample A (Label N D)) (t : ℝ) : Configuration N D :=
  TimeDependentGlobalCounting.preState (lyapunov control) (finite_sublevel control hN)
    jump (timeRate κ q hN) (uniform_rate_bounds control hN) initial 0 p t

/-- The unrestricted accepted test increment in the common comparison convention. -/
def horizonIncrement (f : Configuration N D → ℝ) (j : Label N D) (T : ℝ) :
    Sample A (Label N D) × (ℝ × ℝ) → ℝ :=
  TimeDependentGlobalCounting.horizonIncrement (lyapunov control) (finite_sublevel control hN)
    jump (timeRate κ q hN) (uniform_rate_bounds control hN) initial 0 f j T

theorem measurable_process (hinit : Measurable initial) :
    Measurable (fun p : Sample A (Label N D) × ℝ => process control hN initial p.1 p.2) :=
  TimeDependentGlobalProcess.measurable_process (lyapunov control) (finite_sublevel control hN)
    jump (timeRate κ q hN) (uniform_rate_bounds control hN) initial 0
      (measurable_timeRate hN) hinit

theorem measurable_process_at (hinit : Measurable initial) (t : ℝ) :
    Measurable[filtration A (Label N D) t] (fun p => process control hN initial p t) :=
  TimeDependentGlobalProcess.measurable_process_at (lyapunov control) (finite_sublevel control hN)
    jump (timeRate κ q hN) (uniform_rate_bounds control hN) initial 0
      (measurable_timeRate hN) hinit t

/-- The prescribed initial value needs no moment assumption. -/
theorem ae_initial (μ : Measure A) :
    ∀ᵐ p ∂law μ (Label N D), process control hN initial p 0 = initial p.1 :=
  TimeDependentGlobalProcess.ae_process_zero (lyapunov control) (finite_sublevel control hN)
    jump (timeRate κ q hN) (uniform_rate_bounds control hN) initial 0 μ

omit [MeasurableSpace A] in
/-- The autonomous equation is precisely the candidate equation for constant
time-dependent rates, as an all-sample identity of integrands. -/
theorem candidateIncrement_eq_autonomous (f : Configuration N D → ℝ)
    (j : Label N D) (T : ℝ) (p : Sample A (Label N D)) (r : ℝ × ℝ) :
    TimeDependentGlobalUniqueness.candidateIncrement jump (timeRate κ q hN)
      (ConfigurationNonexplosion.process control hN initial) 0 f j T (p,r) =
    GlobalLocalizedCountingIdentity.horizonIncrement (lyapunov control) (finite_sublevel control hN)
      jump (rate κ q hN) initial 0 f j T (p,r) := by
  rw [GlobalLocalizedCountingIdentity.horizonIncrement_apply]
  rfl

variable (μ : Measure A) [IsProbabilityMeasure μ] (hinit : Measurable initial)
  (hV : Integrable (fun a => lyapunov control (initial a)) μ)
include hinit hV

/-- The time-dependent patch exhausts its genuine exits, derived from the
existing N-independent empirical Lyapunov drift. -/
theorem ae_exhaustive : ∀ᵐ p ∂law μ (Label N D), ∀ T : ℝ≥0, ∃ n : ℕ,
    (T : ℝ≥0∞) < exit control hN initial n p :=
  TimeDependentNonexplosion.ae_exhaustive (lyapunov control) (finite_sublevel control hN)
    jump (timeRate κ q hN) (uniform_rate_bounds control hN) initial 0 μ
      (measurable_timeRate hN) hinit (2 * driftConstant control)
      (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
      (lyapunov_nonnegative control) (fun z j t _ => timeRate_nonnegative hN j t z) hV
      (fun z t _ => generator_affine_bound control hN z t)

/-- The same explicit reciprocal exit estimate holds for this construction. -/
theorem exit_probability_le (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    (law μ (Label N D)) {p | exit control hN initial n p ≤ ENNReal.ofReal T} ≤
      ENNReal.ofReal ((1 + ∫ a, lyapunov control (initial a) ∂μ) *
        Real.exp ((2 * driftConstant control) * T) - 1) / ((n + 1 : ℕ) : ℝ≥0∞) :=
  TimeDependentNonexplosion.exit_probability_le (lyapunov control) (finite_sublevel control hN)
    jump (timeRate κ q hN) (uniform_rate_bounds control hN) initial 0 μ
      (measurable_timeRate hN) hinit (2 * driftConstant control)
      (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
      (lyapunov_nonnegative control) (fun z j t _ => timeRate_nonnegative hN j t z) hV
      (fun z t _ => generator_affine_bound control hN z t) n T hT

/-- Actual unrestricted counting equations, without an exhaustion premise. -/
theorem ae_counting_identity (f : Configuration N D → ℝ) :
    ∀ᵐ p ∂law μ (Label N D), ∀ T : ℝ≥0,
      f (process control hN initial p T) - f (initial p.1) =
        ∑ j, ∫ r, horizonIncrement control hN initial f j T (p,r)
          ∂MarkedNoise.countingMeasure j p.2 :=
  TimeDependentGlobalCounting.ae_testFunction_counting_identity (lyapunov control) (finite_sublevel control hN)
    jump (timeRate κ q hN) (uniform_rate_bounds control hN) initial 0 μ f
      (ae_exhaustive control hN initial μ hinit hV)

/-- The two genuine constructions agree on one event at every nonnegative time.
Only their actual equations, regularity and derived nonexplosion are used. -/
theorem ae_autonomous_eq_process : ∀ᵐ p ∂law μ (Label N D), ∀ t : ℝ, 0 ≤ t →
    ConfigurationNonexplosion.process control hN initial p t = process control hN initial p t := by
  apply TimeDependentGlobalUniqueness.ae_candidate_eq_process_of_separating_tests
    (lyapunov control) (finite_sublevel control hN) jump (timeRate κ q hN)
    (uniform_rate_bounds control hN) initial 0 μ
    (fun i : Fin N × Fin D => fun z : Configuration N D => (z i.1 i.2 : ℝ))
  · intro x y hxy
    funext i d
    exact_mod_cast hxy (i,d)
  · exact ae_exhaustive control hN initial μ hinit hV
  · exact ConfigurationNonexplosion.ae_cadlag control hN initial μ hinit hV
  · exact ConfigurationNonexplosion.ae_process_zero control hN initial μ
  · intro i
    filter_upwards [ActualGlobalCounting.configuration_counting_identity control hN initial μ hinit hV
      (fun z => (z i.1 i.2 : ℝ))] with p hp
    intro T
    rw [hp T]
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    exact Eventually.of_forall (fun r => (candidateIncrement_eq_autonomous control hN initial
      (fun z => (z i.1 i.2 : ℝ)) j T p r).symm)

/-- The bridge in the direction used when substituting the comparison process. -/
theorem ae_process_eq_autonomous : ∀ᵐ p ∂law μ (Label N D), ∀ t : ℝ, 0 ≤ t →
    process control hN initial p t = ConfigurationNonexplosion.process control hN initial p t := by
  filter_upwards [ae_autonomous_eq_process control hN initial μ hinit hV] with p hp
  exact fun t ht => (hp t ht).symm

/-- The time-dependent predictable version is the actual left limit. -/
theorem ae_tendsto_preState : ∀ᵐ p ∂law μ (Label N D), ∀ t : ℝ, 0 < t →
    Tendsto (process control hN initial p) (𝓝[<] t) (𝓝 (preState control hN initial p t)) :=
  TimeDependentGlobalCounting.ae_tendsto_preState (lyapunov control) (finite_sublevel control hN)
    jump (timeRate κ q hN) (uniform_rate_bounds control hN) initial 0 μ
      (ae_exhaustive control hN initial μ hinit hV)

/-- The two constructions have identical genuine pre-jump states on one event
at every positive time. This follows from the actual path identity and limits. -/
theorem ae_preState_eq_autonomous : ∀ᵐ p ∂law μ (Label N D), ∀ t : ℝ, 0 < t →
    preState control hN initial p t = GlobalLocalizedCountingIdentity.preState
      (lyapunov control) (finite_sublevel control hN) jump (rate κ q hN) initial 0 p t := by
  filter_upwards [ae_autonomous_eq_process control hN initial μ hinit hV,
    ae_tendsto_preState control hN initial μ hinit hV,
    GlobalLocalizedCountingIdentity.ae_tendsto_preState (lyapunov control) (finite_sublevel control hN)
      jump (rate κ q hN) initial 0 μ
        (ConfigurationNonexplosion.ae_exhaustive control hN initial μ hinit hV)] with p heq htime haut
  intro t ht
  have hevent : ConfigurationNonexplosion.process control hN initial p =ᶠ[𝓝[<] t]
      process control hN initial p := by
    filter_upwards [(eventually_gt_nhds ht).filter_mono nhdsWithin_le_nhds] with s hs
    exact heq s hs.le
  exact tendsto_nhds_unique (htime t ht) ((haut t ht).congr' hevent)

/-- Accepted integrands agree pointwise in time and height, simultaneously for
all tests, labels and horizons, on one event. Counting-integral substitution is
therefore legitimate without any new integrability assumption. -/
theorem ae_horizonIncrement_eq_autonomous : ∀ᵐ p ∂law μ (Label N D),
    ∀ (f : Configuration N D → ℝ) (j : Label N D) (T : ℝ) (r : ℝ × ℝ),
    horizonIncrement control hN initial f j T (p,r) =
      GlobalLocalizedCountingIdentity.horizonIncrement (lyapunov control) (finite_sublevel control hN)
        jump (rate κ q hN) initial 0 f j T (p,r) := by
  filter_upwards [ae_preState_eq_autonomous control hN initial μ hinit hV] with p hp
  intro f j T r
  rw [horizonIncrement, TimeDependentGlobalCounting.horizonIncrement_apply,
    GlobalLocalizedCountingIdentity.horizonIncrement_apply]
  by_cases ht : r.1 ∈ Ioc 0 T
  · change (if r.1 ∈ Ioc 0 T ∧ r.2 ≤ timeRate κ q hN j r.1 (preState control hN initial p r.1)
      then f (jump j (preState control hN initial p r.1)) - f (preState control hN initial p r.1)
      else 0) = _
    rw [hp r.1 ht.1]
    rfl
  · simp only [ht, false_and, ↓reduceIte]

/-- Pathwise integrability of all unrestricted time-dependent increments is
proved from the actual finite-horizon construction. -/
theorem ae_integrable_horizonIncrement : ∀ᵐ p ∂law μ (Label N D),
    ∀ (T : ℝ≥0) (f : Configuration N D → ℝ) (j : Label N D),
    Integrable (fun r => horizonIncrement control hN initial f j T (p,r))
      (MarkedNoise.countingMeasure j p.2) :=
  TimeDependentGlobalCounting.ae_integrable_horizonIncrement (lyapunov control) (finite_sublevel control hN)
    jump (timeRate κ q hN) (uniform_rate_bounds control hN) initial 0 μ
      (ae_exhaustive control hN initial μ hinit hV)

/-- The original interacting path is thus itself a solution in the generic
time-dependent comparison convention, on the original noise space. -/
theorem ae_autonomous_counting_identity (f : Configuration N D → ℝ) :
    ∀ᵐ p ∂law μ (Label N D), ∀ T : ℝ≥0,
      f (ConfigurationNonexplosion.process control hN initial p T) - f (initial p.1) =
        ∑ j, ∫ r, horizonIncrement control hN initial f j T (p,r)
          ∂MarkedNoise.countingMeasure j p.2 := by
  filter_upwards [ae_counting_identity control hN initial μ hinit hV f,
    ae_autonomous_eq_process control hN initial μ hinit hV] with p heq hp
  intro T
  rw [hp T T.coe_nonneg]
  exact heq T

end CarryingCapacity.ConfigurationTimeDependent
