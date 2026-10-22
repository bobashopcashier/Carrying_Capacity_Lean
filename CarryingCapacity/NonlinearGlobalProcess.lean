import CarryingCapacity.NonlinearPathConsistency

/-!
# One nonlinear realization on all nonnegative times

At a time `t` we use the already constructed process with integer horizon
strictly larger than `t`. Pathwise compatibility makes this choice agree,
on one event, with every integer-horizon realization on its interval. This
gives one measurable adapted càdlàg process whose actual marginals form the
consistent nonlinear law and satisfy the exact moment envelope for every time.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace CarryingCapacity.NonlinearGlobalProcess
open CommonInitialNoise DeterministicEnvironmentLyapunov LyapunovFlowSpace

/-- A deterministic integer horizon strictly beyond the selected real time. -/
def horizon (t : ℝ) : ℕ := Nat.ceil t + 1

theorem lt_horizon (t : ℝ) : t < (horizon t : ℝ) := by
  have h := Nat.le_ceil t
  simp only [horizon, Nat.cast_add, Nat.cast_one]
  linarith

theorem measurable_horizon : Measurable horizon := Nat.measurable_ceil.add_const 1

-- Keep the integer selector abstract when checking dependent horizon casts.
attribute [local irreducible] horizon

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)

/-- Integer realizations packaged without a dependent horizon in their result type. -/
def integerProcess (n : ℕ) : Sample (State D) (Jump D) → ℝ → State D :=
  NonlinearFixedPoint.process control hActivity ν n (Nat.cast_nonneg n) hCoupling hMoment

theorem measurable_integerProcess (n : ℕ) : Measurable
    (fun p : Sample (State D) (Jump D) × ℝ =>
      integerProcess control hActivity ν hCoupling hMoment n p.1 p.2) :=
  NonlinearFixedPoint.measurable_process control hActivity ν n (Nat.cast_nonneg n) hCoupling hMoment

/-- The single all-time process uses no additional random input. -/
def process (p : Sample (State D) (Jump D)) (t : ℝ) : State D :=
  integerProcess control hActivity ν hCoupling hMoment (horizon t) p t

/-- The consistent nonlinear environment, without a final-time cutoff. -/
def environment (t : ℝ) : MomentLaw κ D :=
  NonlinearFixedPoint.environment control hActivity ν (horizon t) (Nat.cast_nonneg _)
    hCoupling hMoment t

/-- The global law equals any integer-horizon law on that horizon. -/
theorem environment_eq_integer_horizon (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 (n : ℝ)) :
    environment control hActivity ν hCoupling hMoment t =
      NonlinearFixedPoint.environment control hActivity ν n (Nat.cast_nonneg n) hCoupling hMoment t := by
  unfold environment
  rcases le_total (horizon t) n with hmn | hnm
  · exact NonlinearHorizonConsistency.environment_eq_on_overlap control ν (horizon t) n
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hmn) hActivity hCoupling hMoment
      ⟨ht.1, (lt_horizon t).le⟩
  · exact (NonlinearHorizonConsistency.environment_eq_on_overlap control ν n (horizon t)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hnm) hActivity hCoupling hMoment ht).symm

/-- The actual global path agrees with all integer-horizon paths at once. -/
theorem ae_process_eq_integer_horizon : ∀ᵐ p ∂law ν.measure (Jump D), ∀ n : ℕ,
    EqOn (process control hActivity ν hCoupling hMoment p)
      (NonlinearFixedPoint.process control hActivity ν n (Nat.cast_nonneg n) hCoupling hMoment p)
      (Icc 0 (n : ℝ)) := by
  filter_upwards [NonlinearPathConsistency.ae_integer_compatible control hActivity ν hCoupling hMoment]
    with p hp
  intro n t ht
  unfold process
  rcases le_total (horizon t) n with hmn | hnm
  · exact hp (horizon t) n hmn ⟨ht.1, (lt_horizon t).le⟩
  · exact (hp n (horizon t) hnm ht).symm

section JointMeasurability
attribute [local irreducible] integerProcess

/-- Joint measurability comes from countably many actual measurable realizations. -/
theorem measurable_process : Measurable
    (fun p : Sample (State D) (Jump D) × ℝ => process control hActivity ν hCoupling hMoment p.1 p.2) := by
  let F : ℕ → Sample (State D) (Jump D) × ℝ → State D := fun n p =>
    integerProcess control hActivity ν hCoupling hMoment n p.1 p.2
  have hf (n : ℕ) : Measurable (F n) :=
    measurable_integerProcess control hActivity ν hCoupling hMoment n
  have hm : Measurable (fun z : (Sample (State D) (Jump D) × ℝ) × ℕ => F z.2 z.1) :=
    measurable_from_prod_countable hf
  have hc : Measurable (fun p : Sample (State D) (Jump D) × ℝ => (p, horizon p.2)) :=
    measurable_id.prodMk (measurable_horizon.comp measurable_snd)
  change Measurable (fun p : Sample (State D) (Jump D) × ℝ => F (horizon p.2) p)
  exact hm.comp hc

end JointMeasurability

/-- The horizon choice is deterministic, so the raw-noise adaptedness is preserved. -/
theorem adapted_process : Adapted (filtration (State D) (Jump D))
    (fun t p => process control hActivity ν hCoupling hMoment p t) := by
  intro t
  exact NonlinearFixedPoint.adapted_process control hActivity ν (horizon t)
    (Nat.cast_nonneg _) hCoupling hMoment t

/-- Every nonnegative-time marginal is the genuine untruncated nonlinear law. -/
theorem environment_measure_eq_marginal (t : ℝ) (ht : 0 ≤ t) :
    (environment control hActivity ν hCoupling hMoment t).measure =
      (law ν.measure (Jump D)).map (fun p => process control hActivity ν hCoupling hMoment p t) :=
  NonlinearFixedPoint.environment_measure_eq_marginal control hActivity ν (horizon t)
    (Nat.cast_nonneg _) hCoupling hMoment ⟨t, ht, (lt_horizon t).le⟩

/-- Continuity follows locally from one horizon strictly larger than the time. -/
theorem continuousOn_environment :
    ContinuousOn (environment control hActivity ν hCoupling hMoment) (Ici 0) := by
  intro t ht
  let n := horizon t
  have he := environment_eq_integer_horizon control hActivity ν hCoupling hMoment n t
    ⟨ht, (lt_horizon t).le⟩
  rw [ContinuousWithinAt, he]
  apply (NonlinearFixedPoint.continuous_environment control hActivity ν n (Nat.cast_nonneg _)
    hCoupling hMoment).continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr'
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_horizon t))] with s hs hsn
  exact (environment_eq_integer_horizon control hActivity ν hCoupling hMoment n s ⟨hs, hsn.le⟩).symm

/-- One probability-one event gives càdlàg paths on the whole half-line. -/
theorem ae_process_cadlag : ∀ᵐ p ∂law ν.measure (Jump D),
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (process control hActivity ν hCoupling hMoment p) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : State D,
      Tendsto (process control hActivity ν hCoupling hMoment p) (𝓝[<] t) (𝓝 y)) := by
  have hr := ae_all_iff.mpr (fun n : ℕ =>
    NonlinearFixedPoint.ae_process_cadlag control hActivity ν n (Nat.cast_nonneg _) hCoupling hMoment)
  filter_upwards [ae_process_eq_integer_horizon control hActivity ν hCoupling hMoment, hr]
    with p hp hr
  constructor
  · intro t ht
    let n := horizon t
    have he := hp n ⟨ht, (lt_horizon t).le⟩
    rw [ContinuousWithinAt, he]
    apply (hr n).1 t ht |>.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_horizon t))] with s hs hsn
    exact (hp n ⟨ht.trans hs, hsn.le⟩).symm
  · intro t ht
    let n := horizon t
    obtain ⟨y, hy⟩ := (hr n).2 t ht
    refine ⟨y, hy.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht)] with s hs hs0
    exact (hp n ⟨hs0.le, hs.le.trans (lt_horizon t).le⟩).symm

/-- The exact manuscript moment bound holds at every nonnegative time. -/
theorem process_moment_bounds (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun p => control.function (process control hActivity ν hCoupling hMoment p t))
      (law ν.measure (Jump D)) ∧
    (∫ p, control.function (process control hActivity ν hCoupling hMoment p t)
      ∂law ν.measure (Jump D)) ≤
      exponentialEnvelope (∫ x, control.function x ∂ν.measure) (driftConstant control) t ∧
    (∫⁻ p, ENNReal.ofReal (control.function (process control hActivity ν hCoupling hMoment p t))
      ∂law ν.measure (Jump D)) ≤
      ENNReal.ofReal (exponentialEnvelope (∫ x, control.function x ∂ν.measure)
        (driftConstant control) t) :=
  NonlinearFixedPoint.process_moment_bounds control hActivity ν (horizon t) (Nat.cast_nonneg _)
    hCoupling hMoment t ⟨ht, (lt_horizon t).le⟩

/-- The global environment restricts to every real construction horizon. -/
theorem environment_eq_horizon (T : ℝ) (hT : 0 ≤ T) :
    EqOn (environment control hActivity ν hCoupling hMoment)
      (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment) (Icc 0 T) := by
  intro t ht
  rw [environment_eq_integer_horizon control hActivity ν hCoupling hMoment (horizon T) t
    ⟨ht.1, ht.2.trans (lt_horizon T).le⟩]
  exact (NonlinearHorizonConsistency.environment_eq_on_overlap control ν T (horizon T)
    hT (Nat.cast_nonneg _) (lt_horizon T).le hActivity hCoupling hMoment ht).symm

/-- Every chosen finite-horizon realization is the restriction of this
single all-time process, up to indistinguishability on the whole interval. -/
theorem ae_process_eq_horizon (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ p ∂law ν.measure (Jump D),
      EqOn (process control hActivity ν hCoupling hMoment p)
        (NonlinearFixedPoint.process control hActivity ν T hT hCoupling hMoment p) (Icc 0 T) := by
  filter_upwards [ae_process_eq_integer_horizon control hActivity ν hCoupling hMoment,
    NonlinearPathConsistency.ae_process_eq_on_overlap control hActivity ν hCoupling hMoment
      T (horizon T) hT (Nat.cast_nonneg _) (lt_horizon T).le] with p hp hc
  intro t ht
  exact (hp (horizon T) ⟨ht.1, ht.2.trans (lt_horizon T).le⟩).trans (hc ht).symm

end CarryingCapacity.NonlinearGlobalProcess
