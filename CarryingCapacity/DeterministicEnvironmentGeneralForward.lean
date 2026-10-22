import CarryingCapacity.DeterministicEnvironmentFiniteSupport
import CarryingCapacity.FiniteJumpForward

/-!
# Forward existence for a general prescribed environment

The environment need only be continuous on the construction interval and have
a uniformly bounded genuine Lyapunov moment. Its initial value need not equal
the initial law. Finite predecessor support proves all test integrability;
the actual global construction, signed compensation and Fubini then give a
weak forward solution for the original coefficients on the whole interval.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal

namespace CarryingCapacity.DeterministicEnvironmentGeneralForward
open CommonInitialNoise DeterministicEnvironmentLyapunov DeterministicEnvironmentFrozen
open MarkedIntensity PredictableSets
open DeterministicEnvironmentFiniteSupport (influence increment_eq_zero_of_not_mem functionBound norm_le_functionBound)

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))

/-- The actual marginal law of the existing globally constructed process. -/
def actualLaw (ν : MomentLaw κ D) (s : ℝ) : Measure (State D) :=
  (law ν.measure (Jump D)).map
    (fun p => DeterministicEnvironmentProcess.process control hActivity v T hT hv id p s)

/-- Original prescribed coefficients, before endpoint extension. -/
def originalRate (j : Jump D) (s : ℝ) (x : State D) : ℝ := q.rate j x (v s)

/-- The current generator along the actual clamped process. -/
def generatorAt (f : State D → ℝ) (p : Sample (State D) (Jump D) × ℝ) : ℝ :=
  FiniteJumpForward.generator Jump.advance (timeRate κ q v T) f p.2
    (DeterministicEnvironmentProcess.process control hActivity v T hT hv id p.1 p.2)

/-- A finite influence set supplies a deterministic positive cap on all relevant rates. -/
def rateCap (f : State D → ℝ) (hf : (Function.support f).Finite) : ℝ :=
  Classical.choose (DeterministicEnvironmentRates.exists_positive_rate_bound_on_Icc κ q hActivity
    (influence f hf) v T hv)

theorem rateCap_positive (f : State D → ℝ) (hf : (Function.support f).Finite) :
    0 < rateCap hActivity v T hv f hf :=
  (Classical.choose_spec (DeterministicEnvironmentRates.exists_positive_rate_bound_on_Icc κ q hActivity
    (influence f hf) v T hv)).1

include hT in
theorem rate_le_cap (f : State D → ℝ) (hf : (Function.support f).Finite)
    (x : State D) (hx : x ∈ influence f hf) (j : Jump D) (s : ℝ) :
    timeRate κ q v T j s x ≤ rateCap hActivity v T hv f hf :=
  (Classical.choose_spec (DeterministicEnvironmentRates.exists_positive_rate_bound_on_Icc κ q hActivity
    (influence f hf) v T hv)).2 x hx j _ ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

/-- The already defined global increment has deterministic finite influence
and bounded height, as an identity on every sample and time-height point. -/
theorem horizonIncrement_eq_localized (f : State D → ℝ) (hf : (Function.support f).Finite)
    (j : Jump D) (S : ℝ) :
    DeterministicEnvironmentProcess.horizonIncrement control hActivity v T hT hv id f j S =
      TimeDependentIntensity.localizedIncrement (influence f hf) Jump.advance (timeRate κ q v T) f j
        (fun p => DeterministicEnvironmentProcess.preState control hActivity v T hT hv id p.1 p.2.1)
        S (rateCap hActivity v T hv f hf) := by
  funext p
  rcases p with ⟨p, ⟨s,u⟩⟩
  change TimeDependentGlobalCounting.horizonIncrement _ _ _ _ _ _ _ _ _ _ _ = _
  rw [TimeDependentGlobalCounting.horizonIncrement_apply]
  let x := DeterministicEnvironmentProcess.preState control hActivity v T hT hv id p s
  change (if s ∈ Ioc 0 S ∧ u ≤ timeRate κ q v T j s x then f (Jump.advance j x) - f x else 0) =
    (if s ∈ Ioc 0 S ∧ x ∈ influence f hf ∧ u ≤ rateCap hActivity v T hv f hf ∧
      u ≤ timeRate κ q v T j s x then f (Jump.advance j x) - f x else 0)
  by_cases hx : x ∈ influence f hf
  · have hh : u ≤ rateCap hActivity v T hv f hf ∧ u ≤ timeRate κ q v T j s x ↔
        u ≤ timeRate κ q v T j s x :=
      ⟨And.right, fun h => ⟨h.trans (rate_le_cap hActivity v T hT hv f hf x hx j s),h⟩⟩
    simp only [hx, true_and, hh]
  · simp only [hx, false_and, and_false, if_false, increment_eq_zero_of_not_mem f hf x hx j, ite_self]

/-- The global generator of a finite-support test is exactly the finite
influence generator; the state dynamics themselves are not truncated. -/
theorem generator_eq_frozen (f : State D → ℝ) (hf : (Function.support f).Finite)
    (s : ℝ) (x : State D) :
    FiniteJumpForward.generator Jump.advance (timeRate κ q v T) f s x =
      TimeDependentGeneratorIntegral.frozenGenerator (influence f hf) Jump.advance (timeRate κ q v T) f s x := by
  by_cases hx : x ∈ influence f hf
  · simp only [FiniteJumpForward.generator, TimeDependentGeneratorIntegral.frozenGenerator,
      FrozenProcess.frozenGenerator, if_pos hx]
  · simp only [FiniteJumpForward.generator, TimeDependentGeneratorIntegral.frozenGenerator,
      FrozenProcess.frozenGenerator, if_neg hx, increment_eq_zero_of_not_mem f hf x hx,
      mul_zero, Finset.sum_const_zero]

variable (ν : MomentLaw κ D) (hCoupling : MomentCouplingBound κ q)
include hCoupling

theorem measurable_preState : Measurable[predictable (filtration (State D) (Jump D))]
    (fun p : Sample (State D) (Jump D) × (ℝ × ℝ) =>
      DeterministicEnvironmentProcess.preState control hActivity v T hT hv id p.1 p.2.1) :=
  TimeDependentGlobalCounting.measurable_preState control.function (finite_sublevels control)
    Jump.advance (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv) id 0
    (DeterministicEnvironmentFrozen.measurable_timeRate κ q v T hv hCoupling hT) measurable_id

/-- Finite predecessor support proves actual deterministic product integrability. -/
theorem integrable_horizonIncrement (f : State D → ℝ) (hf : (Function.support f).Finite)
    (j : Jump D) (S : ℝ) :
    Integrable (DeterministicEnvironmentProcess.horizonIncrement control hActivity v T hT hv id f j S)
      ((law ν.measure (Jump D)).prod (positiveVolume.prod positiveVolume)) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  rw [horizonIncrement_eq_localized control hActivity v T hT hv f hf j S]
  exact TimeDependentIntensity.integrable_localizedIncrement (law ν.measure (Jump D))
    (influence f hf) Jump.advance (timeRate κ q v T)
    (DeterministicEnvironmentFrozen.measurable_timeRate κ q v T hv hCoupling hT) f j _
    ((measurable_preState control hActivity v T hT hv hCoupling).mono (predictable_le _) le_rfl)
    S (rateCap hActivity v T hv f hf)

theorem integrable_counting_integral (f : State D → ℝ) (hf : (Function.support f).Finite)
    (j : Jump D) (S : ℝ) :
    Integrable (fun p => ∫ z,
      DeterministicEnvironmentProcess.horizonIncrement control hActivity v T hT hv id f j S (p,z)
      ∂MarkedNoise.countingMeasure j p.2) (law ν.measure (Jump D)) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact InitialPredictableIntegral.integrable_counting_integral ν.measure j _
    (DeterministicEnvironmentProcess.measurable_horizonIncrement control hActivity v T hT hv
      id hCoupling measurable_id f j S).stronglyMeasurable
    (integrable_horizonIncrement control hActivity v T hT hv ν hCoupling f hf j S)

theorem compensation_horizonIncrement (f : State D → ℝ) (hf : (Function.support f).Finite)
    (j : Jump D) (S : ℝ) :
    (∫ p, ∫ z, DeterministicEnvironmentProcess.horizonIncrement control hActivity v T hT hv id f j S (p,z)
      ∂MarkedNoise.countingMeasure j p.2 ∂law ν.measure (Jump D)) =
      ∫ p, ∫ z, DeterministicEnvironmentProcess.horizonIncrement control hActivity v T hT hv id f j S (p,z)
        ∂positiveVolume.prod positiveVolume ∂law ν.measure (Jump D) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact InitialPredictableIntegral.compensation_integrable ν.measure j _
    (DeterministicEnvironmentProcess.measurable_horizonIncrement control hActivity v T hT hv
      id hCoupling measurable_id f j S).stronglyMeasurable
    (integrable_horizonIncrement control hActivity v T hT hv ν hCoupling f hf j S)

/-- The current generator is genuinely jointly integrable on every finite horizon. -/
theorem integrable_generatorAt (f : State D → ℝ) (hf : (Function.support f).Finite) (S : ℝ) :
    Integrable (generatorAt control hActivity v T hT hv f)
      ((law ν.measure (Jump D)).prod (volume.restrict (Ioc 0 S))) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  change Integrable (fun p : Sample (State D) (Jump D) × ℝ =>
    FiniteJumpForward.generator Jump.advance (timeRate κ q v T) f p.2
      (DeterministicEnvironmentProcess.process control hActivity v T hT hv id p.1 p.2)) _
  simp_rw [generator_eq_frozen v T f hf]
  exact TimeDependentGeneratorIntegral.integrable_generatorField (law ν.measure (Jump D))
    (influence f hf) Jump.advance (timeRate κ q v T)
    (DeterministicEnvironmentFrozen.measurable_timeRate κ q v T hv hCoupling hT) f
    (DeterministicEnvironmentProcess.process control hActivity v T hT hv id)
    (DeterministicEnvironmentProcess.measurable_process control hActivity v T hT hv id hCoupling measurable_id)
    S (rateCap hActivity v T hv f hf)
    (fun x _ j s _ => timeRate_nonnegative κ q v T j s x)
    (fun x hx j s _ => rate_le_cap hActivity v T hT hv f hf x hx j s)

theorem integrable_test_at (f : State D → ℝ) (hf : (Function.support f).Finite) (s : ℝ) :
    Integrable (fun p => f (DeterministicEnvironmentProcess.process control hActivity v T hT hv id p s))
      (law ν.measure (Jump D)) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  have hp := (DeterministicEnvironmentProcess.measurable_process control hActivity v T hT hv id
    hCoupling measurable_id).comp (measurable_id.prodMk (measurable_const (a := s)))
  exact (integrable_const (functionBound f hf)).mono'
    ((measurable_of_countable f).comp hp).aestronglyMeasurable
    (Eventually.of_forall (fun _ => norm_le_functionBound f hf _))

theorem actualLaw_probability (s : ℝ) : IsProbabilityMeasure (actualLaw control hActivity v T hT hv ν s) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact isProbabilityMeasure_map ((DeterministicEnvironmentProcess.measurable_process control hActivity v T hT hv id
    hCoupling measurable_id).comp (measurable_id.prodMk (measurable_const (a := s)))).aemeasurable

theorem integral_actualLaw (f : State D → ℝ) (s : ℝ) :
    (∫ x, f x ∂actualLaw control hActivity v T hT hv ν s) =
      ∫ p, f (DeterministicEnvironmentProcess.process control hActivity v T hT hv id p s) ∂law ν.measure (Jump D) :=
  integral_map_of_stronglyMeasurable
    ((DeterministicEnvironmentProcess.measurable_process control hActivity v T hT hv id hCoupling measurable_id).comp
      (measurable_id.prodMk (measurable_const (a := s)))) (measurable_of_countable f).stronglyMeasurable

omit hCoupling in
/-- The expected current generator of the actual general-environment process. -/
def expectedGenerator (f : State D → ℝ) (s : ℝ) : ℝ :=
  ∫ p, generatorAt control hActivity v T hT hv f (p,s) ∂law ν.measure (Jump D)

/-- Product integrability supplies the tested drift's actual time integrability. -/
theorem integrableOn_expectedGenerator (f : State D → ℝ) (hf : (Function.support f).Finite) (S : ℝ) :
    IntegrableOn (expectedGenerator control hActivity v T hT hv ν f) (Ioc 0 S) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact (integrable_generatorAt control hActivity v T hT hv ν hCoupling f hf S).integral_prod_right

theorem intervalIntegrable_expectedGenerator (f : State D → ℝ) (hf : (Function.support f).Finite)
    (S : ℝ) (hS : 0 ≤ S) :
    IntervalIntegrable (expectedGenerator control hActivity v T hT hv ν f) volume 0 S :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hS).mpr
    (integrableOn_expectedGenerator control hActivity v T hT hv ν hCoupling f hf S)

/-- Generator expectations are genuine pushforward law integrals. -/
theorem integral_generator_actualLaw (f : State D → ℝ) (s : ℝ) :
    (∫ x, FiniteJumpForward.generator Jump.advance (timeRate κ q v T) f s x
      ∂actualLaw control hActivity v T hT hv ν s) =
      expectedGenerator control hActivity v T hT hv ν f s :=
  integral_actualLaw control hActivity v T hT hv ν hCoupling _ s

variable (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ s ∈ Icc 0 T, LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
  (hInitial : Integrable control.function ν.measure)
include hB hEnv hInitial

/-- The genuine moment hypothesis proves exit exhaustion before using the
pathwise counting identity; no stochastic equation is assumed. -/
theorem ae_counting_identity (f : State D → ℝ) :
    ∀ᵐ p ∂law ν.measure (Jump D), ∀ S : ℝ≥0,
      f (DeterministicEnvironmentProcess.process control hActivity v T hT hv id p S) - f p.1 =
        ∑ j, ∫ z, DeterministicEnvironmentProcess.horizonIncrement
          control hActivity v T hT hv id f j S (p,z) ∂MarkedNoise.countingMeasure j p.2 := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact DeterministicEnvironmentProcess.ae_counting_identity control hActivity v T hT hv
    id ν.measure hCoupling measurable_id B hB hEnv hInitial f

/-- Actual intensity integration gives the current-state time generator,
using the derived nonexplosion and the actual time-null jump set. -/
theorem ae_sum_intensity_eq_timeGenerator (f : State D → ℝ) (hf : (Function.support f).Finite)
    (S : ℝ) :
    (fun p => ∑ j, ∫ z, DeterministicEnvironmentProcess.horizonIncrement
      control hActivity v T hT hv id f j S (p,z) ∂positiveVolume.prod positiveVolume) =ᵐ[law ν.measure (Jump D)]
      (fun p => ∫ s in Ioc 0 S, generatorAt control hActivity v T hT hv f (p,s)) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  have hZ := (measurable_preState control hActivity v T hT hv hCoupling).mono (predictable_le _) le_rfl
  have hpos (x : State D) (_ : x ∈ influence f hf) (j : Jump D) (s : ℝ) (_ : s ∈ Ioc 0 S) :
      0 ≤ timeRate κ q v T j s x := timeRate_nonnegative κ q v T j s x
  have hcap (x : State D) (hx : x ∈ influence f hf) (j : Jump D) (s : ℝ) (_ : s ∈ Ioc 0 S) :
      timeRate κ q v T j s x ≤ rateCap hActivity v T hv f hf :=
    rate_le_cap hActivity v T hT hv f hf x hx j s
  have hl := ae_all_iff.mpr (fun j : Jump D =>
    TimeDependentGeneratorIntegral.ae_intensityIntegral_eq_timeDrift (law ν.measure (Jump D))
      (influence f hf) Jump.advance (timeRate κ q v T)
      (DeterministicEnvironmentFrozen.measurable_timeRate κ q v T hv hCoupling hT)
      f j (DeterministicEnvironmentProcess.preState control hActivity v T hT hv id) hZ S
      (rateCap hActivity v T hv f hf)
      (fun x hx s hs => hpos x hx j s hs) (fun x hx s hs => hcap x hx j s hs))
  have hg := TimeDependentGeneratorIntegral.ae_sum_timeDrift_eq_generator (law ν.measure (Jump D))
    (influence f hf) Jump.advance (timeRate κ q v T)
    (DeterministicEnvironmentFrozen.measurable_timeRate κ q v T hv hCoupling hT)
    f (DeterministicEnvironmentProcess.preState control hActivity v T hT hv id) hZ S
    (rateCap hActivity v T hv f hf) hpos hcap
  have hp := TimeDependentGlobalPreStateTime.ae_preState_eq_process_time control.function
    (finite_sublevels control) Jump.advance (timeRate κ q v T)
    (exists_uniform_rate_bounds control v T hT hActivity hv) id 0 ν.measure
    (DeterministicEnvironmentProcess.ae_exhaustive control hActivity v T hT hv
      id ν.measure hCoupling measurable_id B hB hEnv hInitial)
  filter_upwards [hl, hg, hp] with p hl hg hp
  calc
    _ = ∑ j, ∫ s in Ioc 0 S, TimeDependentGeneratorIntegral.labelDrift (influence f hf)
        Jump.advance (timeRate κ q v T) f j s
        (DeterministicEnvironmentProcess.preState control hActivity v T hT hv id p s)
        ∂positiveVolume := by
      apply Finset.sum_congr rfl
      intro j _
      rw [horizonIncrement_eq_localized control hActivity v T hT hv f hf j S]
      exact hl j
    _ = ∫ s in Ioc 0 S, TimeDependentGeneratorIntegral.frozenGenerator (influence f hf)
        Jump.advance (timeRate κ q v T) f s
        (DeterministicEnvironmentProcess.preState control hActivity v T hT hv id p s)
        ∂positiveVolume := hg
    _ = ∫ s in Ioc 0 S, generatorAt control hActivity v T hT hv f (p,s) ∂positiveVolume := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hp] with s hs
      rw [← generator_eq_frozen v T f hf]
      exact congrArg (FiniteJumpForward.generator Jump.advance (timeRate κ q v T) f s) hs
    _ = _ := by rw [TimeDependentDynkin.positiveVolume_restrict_Ioc_zero]

/-- The weak expectation equation is a consequence of the actual counting
identity and compensation, with Fubini justified by finite predecessor support. -/
theorem expectation_eq_initial_add_integral (f : State D → ℝ) (hf : (Function.support f).Finite)
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ p, f (DeterministicEnvironmentProcess.process control hActivity v T hT hv id p t) ∂law ν.measure (Jump D)) =
      (∫ x, f x ∂ν.measure) + ∫ s in (0 : ℝ)..t, expectedGenerator control hActivity v T hT hv ν f s := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  have hit := integrable_test_at control hActivity v T hT hv ν hCoupling f hf t
  have hi0 : Integrable (fun p : Sample (State D) (Jump D) => f p.1) (law ν.measure (Jump D)) :=
    (integrable_const (functionBound f hf)).mono'
      ((measurable_of_countable f).comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall (fun p => norm_le_functionBound f hf p.1))
  have hinit : (∫ p : Sample (State D) (Jump D), f p.1 ∂law ν.measure (Jump D)) = ∫ x, f x ∂ν.measure := by
    have he := integral_map_of_stronglyMeasurable (μ := law ν.measure (Jump D))
      measurable_fst (measurable_of_countable f).stronglyMeasurable
    rw [CommonInitialNoise.map_initial] at he
    exact he.symm
  have hcount (j : Jump D) := integrable_counting_integral control hActivity v T hT hv ν hCoupling f hf j t
  have hintensity (j : Jump D) :=
    (integrable_horizonIncrement control hActivity v T hT hv ν hCoupling f hf j t).integral_prod_left
  have he : (∫ p, f (DeterministicEnvironmentProcess.process control hActivity v T hT hv id p t) ∂law ν.measure (Jump D)) -
      (∫ x, f x ∂ν.measure) = ∫ s in Ioc 0 t, expectedGenerator control hActivity v T hT hv ν f s := by
    calc
      _ = ∫ p, (f (DeterministicEnvironmentProcess.process control hActivity v T hT hv id p t) - f p.1) ∂law ν.measure (Jump D) := by
        rw [integral_sub hit hi0, hinit]
      _ = ∫ p, ∑ j, ∫ z, DeterministicEnvironmentProcess.horizonIncrement
          control hActivity v T hT hv id f j t (p,z) ∂MarkedNoise.countingMeasure j p.2 ∂law ν.measure (Jump D) :=
        integral_congr_ae ((ae_counting_identity control hActivity v T hT hv ν hCoupling B hB hEnv hInitial f).mono
          (fun _ hp => hp ⟨t,ht⟩))
      _ = ∑ j, ∫ p, ∫ z, DeterministicEnvironmentProcess.horizonIncrement
          control hActivity v T hT hv id f j t (p,z) ∂MarkedNoise.countingMeasure j p.2 ∂law ν.measure (Jump D) :=
        integral_finset_sum _ (fun j _ => hcount j)
      _ = ∑ j, ∫ p, ∫ z, DeterministicEnvironmentProcess.horizonIncrement
          control hActivity v T hT hv id f j t (p,z) ∂positiveVolume.prod positiveVolume ∂law ν.measure (Jump D) := by
        apply Finset.sum_congr rfl
        intro j _
        exact compensation_horizonIncrement control hActivity v T hT hv ν hCoupling f hf j t
      _ = ∫ p, ∑ j, ∫ z, DeterministicEnvironmentProcess.horizonIncrement
          control hActivity v T hT hv id f j t (p,z) ∂positiveVolume.prod positiveVolume ∂law ν.measure (Jump D) :=
        (integral_finset_sum _ (fun j _ => hintensity j)).symm
      _ = ∫ p, ∫ s in Ioc 0 t, generatorAt control hActivity v T hT hv f (p,s) ∂volume ∂law ν.measure (Jump D) :=
        integral_congr_ae (ae_sum_intensity_eq_timeGenerator control hActivity v T hT hv ν hCoupling B hB hEnv hInitial f hf t)
      _ = _ := integral_integral_swap (integrable_generatorAt control hActivity v T hT hv ν hCoupling f hf t)
  rw [intervalIntegral.integral_of_le ht]
  linarith

/-- Every continuous prescribed environment with a genuine uniform Lyapunov
moment bound yields an actual weak forward solution for its clamped rates. -/
theorem isSolution_clamped : FiniteJumpForward.IsSolution Jump.advance
    (timeRate κ q v T) ν.measure (actualLaw control hActivity v T hT hv ν) T where
  probability := fun t _ => actualLaw_probability control hActivity v T hT hv ν hCoupling t
  integrable := by
    intro f hf
    simp_rw [integral_generator_actualLaw control hActivity v T hT hv ν hCoupling f]
    exact intervalIntegrable_expectedGenerator control hActivity v T hT hv ν hCoupling f hf T hT
  equation := by
    intro f hf t ht
    simp_rw [integral_generator_actualLaw control hActivity v T hT hv ν hCoupling f]
    rw [integral_actualLaw control hActivity v T hT hv ν hCoupling f t]
    exact expectation_eq_initial_add_integral control hActivity v T hT hv ν hCoupling B hB hEnv hInitial f hf t ht.1

omit hCoupling hB hEnv hInitial in
/-- The original and clamped generators agree on the original time interval. -/
theorem generator_eq_originalRate (f : State D → ℝ) (s : ℝ) (hs : s ∈ Icc 0 T) (x : State D) :
    FiniteJumpForward.generator Jump.advance (timeRate κ q v T) f s x =
      FiniteJumpForward.generator Jump.advance (originalRate (q := q) v) f s x := by
  unfold FiniteJumpForward.generator
  simp_rw [timeRate_eq κ q v T _ s hs]
  rfl

/-- General prescribed-environment forward existence for the original rates.
The initial law and the environmental value at zero need not agree. -/
theorem isSolution : FiniteJumpForward.IsSolution Jump.advance
    (fun j s x => q.rate j x (v s)) ν.measure (actualLaw control hActivity v T hT hv ν) T := by
  have hc := isSolution_clamped control hActivity v T hT hv ν hCoupling B hB hEnv hInitial
  refine ⟨hc.probability, ?_, ?_⟩
  · intro f hf
    apply (hc.integrable f hf).congr
    rw [uIoc_of_le hT]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => generator_eq_originalRate v T f s ⟨hs.1.le,hs.2⟩ x)
  · intro f hf t ht
    rw [hc.equation f hf t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => generator_eq_originalRate v T f s
      ⟨hs.1, hs.2.trans ht.2⟩ x)

/-- The actual law-tested original generator is interval integrable. -/
theorem intervalIntegrable_originalGenerator (f : State D → ℝ) (hf : (Function.support f).Finite) :
    IntervalIntegrable (fun s => ∫ x, q.generator (v s) f x
      ∂actualLaw control hActivity v T hT hv ν s) volume 0 T :=
  (isSolution control hActivity v T hT hv ν hCoupling B hB hEnv hInitial).integrable f hf

/-- The original environmental weak equation for the genuine actual laws. -/
theorem law_forward_equation (f : State D → ℝ) (hf : (Function.support f).Finite)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (∫ x, f x ∂actualLaw control hActivity v T hT hv ν t) = (∫ x, f x ∂ν.measure) +
      ∫ s in (0 : ℝ)..t, ∫ x, q.generator (v s) f x ∂actualLaw control hActivity v T hT hv ν s :=
  (isSolution control hActivity v T hT hv ν hCoupling B hB hEnv hInitial).equation f hf t ht

end CarryingCapacity.DeterministicEnvironmentGeneralForward
