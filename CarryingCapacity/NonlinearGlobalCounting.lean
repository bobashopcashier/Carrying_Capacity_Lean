import CarryingCapacity.NonlinearGlobalProcess

/-!
# The all-time nonlinear counting equation

The strict-past predictable version of the single global nonlinear process is
its actual left limit. On each integer horizon it agrees with the corresponding
constructed finite-horizon pre-state. This transfers genuine pathwise integral
finiteness and the accepted-increment equation, with rates evaluated at the
global process's own marginal law and no final-time clamp. The same countable
compatibility event transfers finite activity on every bounded interval.
-/

noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped Classical ENNReal NNReal Topology BigOperators

namespace CarryingCapacity.NonlinearGlobalCounting
open CommonInitialNoise NonlinearGlobalProcess PredictableStepApproximation
open PredictableSets PredictableTime DeterministicEnvironmentLyapunov

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)

local notation "X" => process control hActivity ν hCoupling hMoment
local notation "v" => environment control hActivity ν hCoupling hMoment
private def integerEnvironment (n : ℕ) : ℝ → MomentLaw κ D :=
  NonlinearFixedPoint.environment control hActivity ν n (Nat.cast_nonneg n) hCoupling hMoment

private theorem continuous_integerEnvironment (n : ℕ) :
    Continuous (integerEnvironment control hActivity ν hCoupling hMoment n) :=
  NonlinearFixedPoint.continuous_environment control hActivity ν n (Nat.cast_nonneg n) hCoupling hMoment

private theorem continuousOn_integerEnvironment (n : ℕ) :
    ContinuousOn (integerEnvironment control hActivity ν hCoupling hMoment n) (Icc 0 (n : ℝ)) :=
  (continuous_integerEnvironment control hActivity ν hCoupling hMoment n).continuousOn

local notation "vN" => integerEnvironment control hActivity ν hCoupling hMoment
local notation "hvN" => continuousOn_integerEnvironment control hActivity ν hCoupling hMoment

/-- A predictable strict-past version of the actual global path. -/
def preState (p : Sample (State D) (Jump D)) (t : ℝ) : State D :=
  pastLimit (fun s p => X p s) 0 p t

/-- Rates use the actual all-time nonlinear marginal environment. -/
def rate (j : Jump D) (t : ℝ) (x : State D) : ℝ := q.rate j x (v t)

set_option maxHeartbeats 800000 in
theorem measurable_rate (j : Jump D) (x : State D) :
    Measurable (fun t => rate control hActivity ν hCoupling hMoment j t x) := by
  have hm : Measurable (fun z : ℝ × ℕ => q.rate j x (vN z.2 z.1)) :=
    measurable_from_prod_countable (fun n =>
      ((DeterministicEnvironmentRates.continuous_rate κ q hCoupling j x).comp
        (continuous_integerEnvironment control hActivity ν hCoupling hMoment n)).measurable)
  have hs : Measurable (fun t : ℝ => (t, horizon t)) :=
    measurable_id.prodMk measurable_horizon
  have hc := hm.comp hs
  simpa only [Function.comp_def, integerEnvironment, rate, environment] using hc

/-- No active-set or height cutoff remains in the physical accepted increment. -/
def jumpIncrement (f : State D → ℝ) (j : Jump D)
    (p : Sample (State D) (Jump D) × (ℝ × ℝ)) : ℝ :=
  if 0 < p.2.1 ∧ p.2.2 ≤ rate control hActivity ν hCoupling hMoment j p.2.1
      (preState control hActivity ν hCoupling hMoment p.1 p.2.1)
  then f (Jump.advance j (preState control hActivity ν hCoupling hMoment p.1 p.2.1)) -
    f (preState control hActivity ν hCoupling hMoment p.1 p.2.1)
  else 0

/-- Restriction to an arbitrary finite time interval `(0,S]`. -/
def horizonIncrement (f : State D → ℝ) (j : Jump D) (S : ℝ) :=
  (rectangle univ 0 S univ).indicator (jumpIncrement control hActivity ν hCoupling hMoment f j)

theorem horizonIncrement_apply (f : State D → ℝ) (j : Jump D) (S : ℝ)
    (p : Sample (State D) (Jump D)) (z : ℝ × ℝ) :
    horizonIncrement control hActivity ν hCoupling hMoment f j S (p,z) =
      if z.1 ∈ Ioc 0 S ∧ z.2 ≤ q.rate j
          (preState control hActivity ν hCoupling hMoment p z.1) (v z.1)
      then f (Jump.advance j (preState control hActivity ν hCoupling hMoment p z.1)) -
        f (preState control hActivity ν hCoupling hMoment p z.1) else 0 := by
  by_cases ht : z.1 ∈ Ioc 0 S
  · simp [horizonIncrement, rectangle, jumpIncrement, rate, Set.indicator_apply, ht, ht.1]
  · have ht' : ¬ (0 < z.1 ∧ z.1 ≤ S) := ht
    simp [horizonIncrement, rectangle, Set.indicator_apply, ht']

theorem measurable_preState : Measurable[predictable (filtration (State D) (Jump D))]
    (fun p : Sample (State D) (Jump D) × (ℝ × ℝ) =>
      preState control hActivity ν hCoupling hMoment p.1 p.2.1) :=
  measurable_pastLimit _ _
    (fun s _ => (adapted_process control hActivity ν hCoupling hMoment s).measurable) 0

theorem measurable_jumpIncrement (f : State D → ℝ) (j : Jump D) :
    Measurable[predictable (filtration (State D) (Jump D))]
      (jumpIncrement control hActivity ν hCoupling hMoment f j) := by
  letI : MeasurableSpace (Sample (State D) (Jump D) × (ℝ × ℝ)) :=
    predictable (filtration (State D) (Jump D))
  have hz := measurable_preState control hActivity ν hCoupling hMoment
  have hr := measurable_evaluation (filtration (State D) (Jump D))
    (rate control hActivity ν hCoupling hMoment j)
    (measurable_rate control hActivity ν hCoupling hMoment j) _ hz
  have hf := ((measurable_of_countable (fun x => f (Jump.advance j x))).comp hz).sub
    ((measurable_of_countable f).comp hz)
  have hm : Measurable (fun p : Sample (State D) (Jump D) × (ℝ × ℝ) =>
      if 0 < p.2.1 ∧ positiveHeight p ≤ rate control hActivity ν hCoupling hMoment j
          (positiveTime p) (preState control hActivity ν hCoupling hMoment p.1 p.2.1)
      then f (Jump.advance j (preState control hActivity ν hCoupling hMoment p.1 p.2.1)) -
        f (preState control hActivity ν hCoupling hMoment p.1 p.2.1) else 0) :=
    hf.ite ((measurableSet_positive _).inter (measurableSet_le (measurable_positiveHeight _) hr))
      measurable_const
  convert hm using 1
  funext p
  by_cases ht : 0 < p.2.1 <;> simp [jumpIncrement, positiveHeight, positiveTime, ht]

theorem measurable_horizonIncrement (f : State D → ℝ) (j : Jump D) (S : ℝ) :
    Measurable[predictable (filtration (State D) (Jump D))]
      (horizonIncrement control hActivity ν hCoupling hMoment f j S) :=
  (measurable_jumpIncrement control hActivity ν hCoupling hMoment f j).indicator
    (measurableSet_predictable_rectangle _ 0 S le_rfl univ MeasurableSet.univ univ MeasurableSet.univ)

/-- One event identifies the predictable version as the genuine left limit
at every positive time. -/
theorem ae_tendsto_preState : ∀ᵐ p ∂law ν.measure (Jump D), ∀ t : ℝ, 0 < t →
    Tendsto (X p) (𝓝[<] t) (𝓝 (preState control hActivity ν hCoupling hMoment p t)) := by
  filter_upwards [ae_process_cadlag control hActivity ν hCoupling hMoment] with p hp
  intro t ht
  obtain ⟨y, hy⟩ := hp.2 t ht
  have he : preState control hActivity ν hCoupling hMoment p t = y :=
    pastLimit_eq_of_tendsto _ 0 p t ht y hy
  rwa [he]

theorem ae_preState_eq_leftLim : ∀ᵐ p ∂law ν.measure (Jump D), ∀ t : ℝ, 0 < t →
    preState control hActivity ν hCoupling hMoment p t = Function.leftLim (X p) t := by
  filter_upwards [ae_tendsto_preState control hActivity ν hCoupling hMoment] with p hp
  exact fun t ht => (leftLim_eq_of_tendsto (neBot_iff.mp inferInstance) (hp t ht)).symm

/-- Prefix agreement also identifies every left state, including the right
endpoint, simultaneously for all integer horizons. -/
theorem ae_preState_eq_integer_horizon : ∀ᵐ p ∂law ν.measure (Jump D), ∀ n : ℕ,
    ∀ t ∈ Ioc (0 : ℝ) n, preState control hActivity ν hCoupling hMoment p t =
      NonlinearFixedPoint.preState control hActivity ν n (Nat.cast_nonneg _) hCoupling hMoment p t := by
  have hc := ae_all_iff.mpr (fun n : ℕ =>
    NonlinearFixedPoint.ae_process_cadlag control hActivity ν n (Nat.cast_nonneg _) hCoupling hMoment)
  have hl := ae_all_iff.mpr (fun n : ℕ =>
    NonlinearFixedPoint.ae_preState_eq_leftLim control hActivity ν n (Nat.cast_nonneg _) hCoupling hMoment)
  filter_upwards [ae_process_eq_integer_horizon control hActivity ν hCoupling hMoment, hc, hl]
    with p hp hc hl
  intro n t ht
  obtain ⟨y, hy⟩ := (hc n).2 t ht.1
  have hg : Tendsto (X p) (𝓝[<] t) (𝓝 y) := by
    apply hy.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht.1)] with s hs hs0
    exact (hp n ⟨hs0.le, hs.le.trans ht.2⟩).symm
  change pastLimit (fun s p => X p s) 0 p t = _
  rw [pastLimit_eq_of_tendsto _ 0 p t ht.1 y hg, hl n t ht.1,
    leftLim_eq_of_tendsto (neBot_iff.mp inferInstance) hy]

/-- The original sampled state is retained by the all-time construction. -/
theorem ae_initial : ∀ᵐ p ∂law ν.measure (Jump D), X p 0 = p.1 := by
  have hz := DeterministicEnvironmentProcess.ae_initial control hActivity (vN (0 : ℕ))
    (0 : ℕ) (Nat.cast_nonneg 0) (hvN (0 : ℕ)) id ν.measure
  filter_upwards [ae_process_eq_integer_horizon control hActivity ν hCoupling hMoment, hz]
    with p hp hz
  exact (hp 0 ⟨by norm_num, by norm_num⟩).trans hz

private theorem integer_environment_bound (n : ℕ) : ∀ t ∈ Icc (0 : ℝ) n,
    LyapunovFlowSpace.lyapunovIntegral control.function (vN n t) ≤
      ENNReal.ofReal (manuscriptBound control ν (driftConstant control) n) :=
  fun t _ => manuscriptExtension_bound control ν (driftConstant control) n
    (driftConstant_nonnegative control) (Nat.cast_nonneg _)
    (NonlinearFixedPoint.fixedCurve control hActivity ν n (Nat.cast_nonneg _) hCoupling hMoment) t

/-- Every global increment agrees at all time-height points with a genuine
finite-horizon increment whenever the horizon covers the integration interval. -/
theorem ae_horizonIncrement_eq_integer : ∀ᵐ p ∂law ν.measure (Jump D), ∀ n : ℕ,
    ∀ (S : ℝ≥0), (S : ℝ) ≤ n → ∀ (f : State D → ℝ) (j : Jump D) (z : ℝ × ℝ),
    horizonIncrement control hActivity ν hCoupling hMoment f j S (p,z) =
      DeterministicEnvironmentProcess.horizonIncrement control hActivity (vN n)
        n (Nat.cast_nonneg _) (hvN n) id f j S (p,z) := by
  filter_upwards [ae_preState_eq_integer_horizon control hActivity ν hCoupling hMoment] with p hp
  intro n S hS f j z
  rw [horizonIncrement_apply,
    DeterministicEnvironmentProcess.horizonIncrement_apply_on_horizon
      control hActivity (vN n) n (Nat.cast_nonneg _) (hvN n) id f j S hS p z]
  by_cases ht : z.1 ∈ Ioc (0 : ℝ) S
  · rw [hp n z.1 ⟨ht.1, ht.2.trans hS⟩,
      environment_eq_integer_horizon control hActivity ν hCoupling hMoment n z.1
        ⟨ht.1.le, ht.2.trans hS⟩]
    rfl
  · simp only [ht, false_and, ↓reduceIte]

/-- Actual pathwise integrability holds simultaneously for every finite
horizon, test function, and jump label. It is inherited from the finite
constructed paths rather than assumed of the counting equation. -/
theorem ae_integrable_horizonIncrement : ∀ᵐ p ∂law ν.measure (Jump D),
    ∀ (S : ℝ≥0) (f : State D → ℝ) (j : Jump D),
    Integrable (fun z => horizonIncrement control hActivity ν hCoupling hMoment f j S (p,z))
      (MarkedNoise.countingMeasure j p.2) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  have hi := ae_all_iff.mpr (fun n : ℕ =>
    DeterministicEnvironmentProcess.ae_integrable_horizonIncrement control hActivity (vN n)
      n (Nat.cast_nonneg _) (hvN n) id ν.measure hCoupling measurable_id
      (manuscriptBound control ν (driftConstant control) n)
      (manuscriptBound_nonnegative control ν (driftConstant control) n
        (driftConstant_nonnegative control) (Nat.cast_nonneg _))
      (integer_environment_bound control hActivity ν hCoupling hMoment n) hMoment)
  filter_upwards [ae_horizonIncrement_eq_integer control hActivity ν hCoupling hMoment, hi]
    with p hp hi
  intro S f j
  exact (hi (horizon S) S f j).congr (Eventually.of_forall
    (fun z => (hp (horizon S) S (lt_horizon S).le f j z).symm))

/-- The all-time process solves the genuine counting equation with its own
marginal environment. Each fixed test has one event supporting every horizon;
the increment is integrable by the preceding theorem. -/
theorem ae_counting_identity (f : State D → ℝ) : ∀ᵐ p ∂law ν.measure (Jump D), ∀ S : ℝ≥0,
    f (X p S) - f p.1 = ∑ j,
      ∫ z, horizonIncrement control hActivity ν hCoupling hMoment f j S (p,z)
        ∂MarkedNoise.countingMeasure j p.2 := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  have he := ae_all_iff.mpr (fun n : ℕ =>
    DeterministicEnvironmentProcess.ae_counting_identity control hActivity (vN n)
      n (Nat.cast_nonneg _) (hvN n) id ν.measure hCoupling measurable_id
      (manuscriptBound control ν (driftConstant control) n)
      (manuscriptBound_nonnegative control ν (driftConstant control) n
        (driftConstant_nonnegative control) (Nat.cast_nonneg _))
      (integer_environment_bound control hActivity ν hCoupling hMoment n) hMoment f)
  filter_upwards [ae_process_eq_integer_horizon control hActivity ν hCoupling hMoment,
    ae_horizonIncrement_eq_integer control hActivity ν hCoupling hMoment, he] with p hp hi he
  intro S
  rw [hp (horizon S) ⟨S.coe_nonneg, (lt_horizon S).le⟩]
  exact (he (horizon S) S).trans (Finset.sum_congr rfl (fun j _ =>
    integral_congr_ae (Eventually.of_forall
      (fun z => (hi (horizon S) S (lt_horizon S).le f j z).symm))))

/-- Only finitely many actual proposal times can change the all-time path
on any bounded interval, on one common probability-one event. -/
theorem ae_finite_activity : ∀ᵐ p ∂law ν.measure (Jump D), ∀ S : ℝ≥0,
    ∃ times : Finset ℝ, (times : Set ℝ) ⊆ Ioc 0 S ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ S →
        (∀ u ∈ times, u ∉ Ioc s t) → X p s = X p t := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  have hf := ae_all_iff.mpr (fun n : ℕ =>
    DeterministicEnvironmentProcess.ae_finite_activity control hActivity (vN n)
      n (Nat.cast_nonneg _) (hvN n) id ν.measure hCoupling measurable_id
      (manuscriptBound control ν (driftConstant control) n)
      (manuscriptBound_nonnegative control ν (driftConstant control) n
        (driftConstant_nonnegative control) (Nat.cast_nonneg _))
      (integer_environment_bound control hActivity ν hCoupling hMoment n) hMoment)
  filter_upwards [ae_process_eq_integer_horizon control hActivity ν hCoupling hMoment, hf] with p hp hf
  intro S
  obtain ⟨times, htimes, he⟩ := hf (horizon S) S
  refine ⟨times, htimes, fun s t hs hst ht hno => ?_⟩
  rw [hp (horizon S) ⟨hs, (hst.trans ht).trans (lt_horizon S).le⟩,
    hp (horizon S) ⟨hs.trans hst, ht.trans (lt_horizon S).le⟩]
  exact he s t hs hst ht hno

/-- On every bounded interval, the selected integer realization has a genuine
spatial exit strictly beyond that interval. These are constructed exits, not
an assumed nonexplosion event. -/
theorem ae_integer_exits_exhaustive : ∀ᵐ p ∂law ν.measure (Jump D), ∀ S : ℝ≥0,
    ∃ k : ℕ, (S : ℝ≥0∞) < NonlinearFixedPoint.exit control hActivity ν (horizon S)
      (Nat.cast_nonneg _) hCoupling hMoment k p := by
  have he := ae_all_iff.mpr (fun n : ℕ =>
    NonlinearFixedPoint.ae_exhaustive control hActivity ν n (Nat.cast_nonneg _) hCoupling hMoment)
  filter_upwards [he] with p hp
  exact fun S => hp (horizon S) S

/-- Genuine spatial localization still describes the entire all-time path
on each finite interval, although a different integer horizon can be used
for different intervals. No nonexplosion or compatibility premise is added. -/
theorem ae_agrees_with_localized_on_horizon : ∀ᵐ p ∂law ν.measure (Jump D), ∀ S : ℝ≥0,
    ∃ k : ℕ, ∀ m : ℕ, k ≤ m → ∀ t ∈ Icc (0 : ℝ) S,
      X p t = DeterministicEnvironmentProcess.localizedPath control hActivity (vN (horizon S))
        (horizon S) (Nat.cast_nonneg _) (hvN (horizon S)) id m p t := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  have hl := ae_all_iff.mpr (fun n : ℕ =>
    DeterministicEnvironmentProcess.ae_agrees_on_horizon control hActivity (vN n)
      n (Nat.cast_nonneg _) (hvN n) id ν.measure hCoupling measurable_id
      (manuscriptBound control ν (driftConstant control) n)
      (manuscriptBound_nonnegative control ν (driftConstant control) n
        (driftConstant_nonnegative control) (Nat.cast_nonneg _))
      (integer_environment_bound control hActivity ν hCoupling hMoment n) hMoment)
  filter_upwards [ae_process_eq_integer_horizon control hActivity ν hCoupling hMoment, hl] with p hp hl
  intro S
  obtain ⟨k, hk⟩ := hl (horizon S) S
  refine ⟨k, fun m hm t ht => ?_⟩
  exact (hp (horizon S) ⟨ht.1, ht.2.trans (lt_horizon S).le⟩).trans
    (hk m hm t ht.1 ht.2)

end CarryingCapacity.NonlinearGlobalCounting
