import CarryingCapacity.FiniteSupportGeometry
import CarryingCapacity.DeterministicEnvironmentLaw
import CarryingCapacity.InitialPredictableIntegral
import CarryingCapacity.TimeDependentGlobalPreStateTime

/-!
# Finite-support tests for the actual prescribed-environment process

A finite test support has finitely many actual birth, death and mutation
predecessors. All nonzero increments therefore lie in a finite influence set.
The manuscript activity assumption bounds its rates uniformly over the
endpoint-clamped environment. This gives deterministic product integrability
and actual predictable compensation without an integrability hypothesis.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal

namespace CarryingCapacity.DeterministicEnvironmentFiniteSupport
open CommonInitialNoise LyapunovFlowSpace DeterministicEnvironmentLyapunov
open DeterministicEnvironmentProcess DeterministicEnvironmentLaw DeterministicEnvironmentFrozen
open MarkedIntensity PredictableSets

variable {D : ℕ}

/-- Each actual single-state jump has finite fibers, including boundary rejections. -/
theorem finite_advance_fiber (j : Jump D) (y : State D) :
    {x : State D | Jump.advance j x = y}.Finite := by
  apply (Set.finite_Iic (fun k : Fin D => y k + 1)).subset
  intro x hx k
  change Jump.advance j x = y at hx
  simpa only [hx] using FiniteSupportGeometry.coordinate_le_advance_add_one j x k

theorem finite_advance_preimage (j : Jump D) (s : Set (State D)) (hs : s.Finite) :
    (Jump.advance j ⁻¹' s).Finite := by
  apply (hs.biUnion (fun y _ => finite_advance_fiber j y)).subset
  intro x hx
  exact mem_iUnion.mpr ⟨Jump.advance j x, mem_iUnion.mpr ⟨hx, rfl⟩⟩

/-- The support and all its one-jump predecessors. -/
def influenceSet (f : State D → ℝ) : Set (State D) :=
  Function.support f ∪ ⋃ j : Jump D, Jump.advance j ⁻¹' Function.support f

theorem finite_influenceSet (f : State D → ℝ) (hf : (Function.support f).Finite) :
    (influenceSet f).Finite :=
  hf.union (Set.finite_iUnion (fun j => finite_advance_preimage j _ hf))

def influence (f : State D → ℝ) (hf : (Function.support f).Finite) : Finset (State D) :=
  (finite_influenceSet f hf).toFinset

@[simp] theorem mem_influence (f : State D → ℝ) (hf : (Function.support f).Finite) (x : State D) :
    x ∈ influence f hf ↔ f x ≠ 0 ∨ ∃ j : Jump D, f (Jump.advance j x) ≠ 0 := by
  simp only [influence, Set.Finite.mem_toFinset, influenceSet, mem_union, mem_iUnion,
    mem_preimage, Function.mem_support]

theorem increment_eq_zero_of_not_mem (f : State D → ℝ) (hf : (Function.support f).Finite)
    (x : State D) (hx : x ∉ influence f hf) (j : Jump D) : f (Jump.advance j x) - f x = 0 := by
  have hfx : f x = 0 := by
    by_contra h
    exact hx ((mem_influence f hf x).mpr (Or.inl h))
  have hfj : f (Jump.advance j x) = 0 := by
    by_contra h
    exact hx ((mem_influence f hf x).mpr (Or.inr ⟨j,h⟩))
  simp only [hfx, hfj, sub_self]

/-- A deterministic finite bound on the test itself. -/
def functionBound (f : State D → ℝ) (hf : (Function.support f).Finite) : ℝ :=
  ∑ x ∈ hf.toFinset, |f x|

theorem norm_le_functionBound (f : State D → ℝ) (hf : (Function.support f).Finite) (x : State D) :
    ‖f x‖ ≤ functionBound f hf := by
  by_cases hx : f x = 0
  · rw [hx, norm_zero]
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  · exact Finset.single_le_sum (f := fun y : State D => |f y|)
      (fun _ _ => abs_nonneg _) (hf.mem_toFinset.mpr hx)

variable {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T)
  (v : ManuscriptCurves control.function ν (driftConstant control) T hT)

/-- The actual endpoint-clamped rates used in the global construction. -/
def rate : Jump D → ℝ → State D → ℝ :=
  timeRate κ q (manuscriptExtension control ν (driftConstant control) T hT v) T

/-- The already constructed global pre-jump state. -/
def preState (p : Sample (State D) (Jump D)) (s : ℝ) : State D :=
  DeterministicEnvironmentProcess.preState control hActivity
    (manuscriptExtension control ν (driftConstant control) T hT v) T hT
    (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn id p s

/-- The existing unrestricted accepted-increment integrand. -/
def horizonIncrement (f : State D → ℝ) (j : Jump D) (S : ℝ) :
    Sample (State D) (Jump D) × (ℝ × ℝ) → ℝ :=
  DeterministicEnvironmentProcess.horizonIncrement control hActivity
    (manuscriptExtension control ν (driftConstant control) T hT v) T hT
    (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn id f j S

/-- A strictly positive deterministic cap derived on the finite influence set. -/
def rateCap (f : State D → ℝ) (hf : (Function.support f).Finite) : ℝ :=
  Classical.choose (DeterministicEnvironmentRates.exists_positive_rate_bound_on_Icc κ q hActivity
    (influence f hf) (manuscriptExtension control ν (driftConstant control) T hT v) T
    (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn)

theorem rateCap_positive (f : State D → ℝ) (hf : (Function.support f).Finite) :
    0 < rateCap control hActivity ν T hT v f hf :=
  (Classical.choose_spec (DeterministicEnvironmentRates.exists_positive_rate_bound_on_Icc κ q hActivity
    (influence f hf) (manuscriptExtension control ν (driftConstant control) T hT v) T
    (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn)).1

/-- Clamping retains the same bound at every real time. -/
theorem rate_le_cap (f : State D → ℝ) (hf : (Function.support f).Finite)
    (x : State D) (hx : x ∈ influence f hf) (j : Jump D) (s : ℝ) :
    rate control ν T hT v j s x ≤ rateCap control hActivity ν T hT v f hf :=
  (Classical.choose_spec (DeterministicEnvironmentRates.exists_positive_rate_bound_on_Icc κ q hActivity
    (influence f hf) (manuscriptExtension control ν (driftConstant control) T hT v) T
    (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn)).2
      x hx j _ ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

/-- The unrestricted field equals a finite-region bounded-height field on
every sample, since every other test increment vanishes identically. -/
theorem horizonIncrement_eq_localized (f : State D → ℝ) (hf : (Function.support f).Finite)
    (j : Jump D) (S : ℝ) :
    horizonIncrement control hActivity ν T hT v f j S =
      TimeDependentIntensity.localizedIncrement (influence f hf) Jump.advance (rate control ν T hT v) f j
        (fun p => preState control hActivity ν T hT v p.1 p.2.1) S
        (rateCap control hActivity ν T hT v f hf) := by
  funext p
  rcases p with ⟨p, ⟨s,u⟩⟩
  change TimeDependentGlobalCounting.horizonIncrement _ _ _ _ _ _ _ _ _ _ _ = _
  rw [TimeDependentGlobalCounting.horizonIncrement_apply]
  let x := preState control hActivity ν T hT v p s
  change (if s ∈ Ioc 0 S ∧ u ≤ rate control ν T hT v j s x then f (Jump.advance j x) - f x else 0) =
    (if s ∈ Ioc 0 S ∧ x ∈ influence f hf ∧ u ≤ rateCap control hActivity ν T hT v f hf ∧
      u ≤ rate control ν T hT v j s x then f (Jump.advance j x) - f x else 0)
  by_cases hx : x ∈ influence f hf
  · have hh : u ≤ rateCap control hActivity ν T hT v f hf ∧ u ≤ rate control ν T hT v j s x ↔
        u ≤ rate control ν T hT v j s x :=
      ⟨And.right, fun h => ⟨h.trans (rate_le_cap control hActivity ν T hT v f hf x hx j s),h⟩⟩
    simp only [hx, true_and, hh]
  · simp only [hx, false_and, and_false, if_false,
      increment_eq_zero_of_not_mem f hf x hx j, ite_self]

variable (hCoupling : MomentCouplingBound κ q)
include hCoupling

theorem measurable_preState : Measurable[predictable (filtration (State D) (Jump D))]
    (fun p : Sample (State D) (Jump D) × (ℝ × ℝ) => preState control hActivity ν T hT v p.1 p.2.1) :=
  TimeDependentGlobalCounting.measurable_preState control.function (finite_sublevels control)
    Jump.advance (rate control ν T hT v)
    (exists_uniform_rate_bounds control _ T hT hActivity
      (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn) id 0
    (manuscript_measurable_timeRate control hCoupling ν (driftConstant control) T hT v) measurable_id

theorem measurable_horizonIncrement (f : State D → ℝ) (j : Jump D) (S : ℝ) :
    Measurable[predictable (filtration (State D) (Jump D))]
      (horizonIncrement control hActivity ν T hT v f j S) :=
  DeterministicEnvironmentProcess.measurable_horizonIncrement control hActivity
    (manuscriptExtension control ν (driftConstant control) T hT v) T hT
    (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn
    id hCoupling measurable_id f j S

/-- The finite backward support proves actual deterministic product integrability. -/
theorem integrable_horizonIncrement (f : State D → ℝ) (hf : (Function.support f).Finite)
    (j : Jump D) (S : ℝ) :
    Integrable (horizonIncrement control hActivity ν T hT v f j S)
      ((law ν.measure (Jump D)).prod (positiveVolume.prod positiveVolume)) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  rw [horizonIncrement_eq_localized control hActivity ν T hT v f hf j S]
  exact TimeDependentIntensity.integrable_localizedIncrement (law ν.measure (Jump D))
    (influence f hf) Jump.advance (rate control ν T hT v)
    (manuscript_measurable_timeRate control hCoupling ν (driftConstant control) T hT v) f j _
    ((measurable_preState control hActivity ν T hT v hCoupling).mono (predictable_le _) le_rfl)
    S (rateCap control hActivity ν T hT v f hf)

/-- The actual random counting integral is integrable, not merely defined by convention. -/
theorem integrable_counting_integral (f : State D → ℝ) (hf : (Function.support f).Finite)
    (j : Jump D) (S : ℝ) :
    Integrable (fun p => ∫ z, horizonIncrement control hActivity ν T hT v f j S (p,z)
      ∂MarkedNoise.countingMeasure j p.2) (law ν.measure (Jump D)) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact InitialPredictableIntegral.integrable_counting_integral ν.measure j _
    (measurable_horizonIncrement control hActivity ν T hT v hCoupling f j S).stronglyMeasurable
    (integrable_horizonIncrement control hActivity ν T hT v hCoupling f hf j S)

/-- Signed compensation for the actual global finite-support increment. -/
theorem compensation_horizonIncrement (f : State D → ℝ) (hf : (Function.support f).Finite)
    (j : Jump D) (S : ℝ) :
    (∫ p, ∫ z, horizonIncrement control hActivity ν T hT v f j S (p,z)
      ∂MarkedNoise.countingMeasure j p.2 ∂law ν.measure (Jump D)) =
    ∫ p, ∫ z, horizonIncrement control hActivity ν T hT v f j S (p,z)
      ∂positiveVolume.prod positiveVolume ∂law ν.measure (Jump D) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact InitialPredictableIntegral.compensation_integrable ν.measure j _
    (measurable_horizonIncrement control hActivity ν T hT v hCoupling f j S).stronglyMeasurable
    (integrable_horizonIncrement control hActivity ν T hT v hCoupling f hf j S)

/-- The test itself remains integrable along the actual path. -/
theorem integrable_test_at (f : State D → ℝ) (hf : (Function.support f).Finite) (s : ℝ) :
    Integrable (fun p => f (manuscriptProcess control hActivity ν T hT v p s))
      (law ν.measure (Jump D)) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact (integrable_const (functionBound f hf)).mono'
    ((measurable_of_countable f).comp (measurable_at control hActivity ν T hT v hCoupling s)).aestronglyMeasurable
    (Eventually.of_forall (fun _ => norm_le_functionBound f hf _))

omit hCoupling in
/-- The actual clamped generator, without any spatial truncation. -/
def generator (f : State D → ℝ) (s : ℝ) (x : State D) : ℝ :=
  ∑ j, rate control ν T hT v j s x * (f (Jump.advance j x) - f x)

omit hCoupling in
theorem generator_eq_original (f : State D → ℝ) (s : ℝ) (hs : s ∈ Icc 0 T) (x : State D) :
    generator control ν T hT v f s x =
      q.generator (manuscriptExtension control ν (driftConstant control) T hT v s) f x := by
  unfold generator rate
  simp_rw [timeRate_eq κ q _ T _ s hs]
  rfl

omit hCoupling in
theorem generator_eq_frozen (f : State D → ℝ) (hf : (Function.support f).Finite)
    (s : ℝ) (x : State D) :
    generator control ν T hT v f s x =
      TimeDependentGeneratorIntegral.frozenGenerator (influence f hf) Jump.advance
        (rate control ν T hT v) f s x := by
  by_cases hx : x ∈ influence f hf
  · simp only [generator, TimeDependentGeneratorIntegral.frozenGenerator,
      FrozenProcess.frozenGenerator, if_pos hx]
  · simp only [generator, TimeDependentGeneratorIntegral.frozenGenerator,
      FrozenProcess.frozenGenerator, if_neg hx, increment_eq_zero_of_not_mem f hf x hx,
      mul_zero, Finset.sum_const_zero]

omit hCoupling in
/-- A finite deterministic bound for the globally untruncated generator. -/
def generatorBound (f : State D → ℝ) (hf : (Function.support f).Finite) : ℝ :=
  TimeDependentGeneratorIntegral.generatorBound (influence f hf) Jump.advance f
    (rateCap control hActivity ν T hT v f hf)

omit hCoupling in
theorem norm_generator_le (f : State D → ℝ) (hf : (Function.support f).Finite)
    (s : ℝ) (x : State D) :
    ‖generator control ν T hT v f s x‖ ≤ generatorBound control hActivity ν T hT v f hf := by
  rw [generator_eq_frozen control ν T hT v f hf s x]
  exact TimeDependentGeneratorIntegral.norm_frozenGenerator_le (influence f hf) Jump.advance
    (rate control ν T hT v) f _ s
    (fun x _ j => timeRate_nonnegative κ q _ T j s x)
    (fun x hx j => rate_le_cap control hActivity ν T hT v f hf x hx j s) x

/-- Joint measurability retains the actual time-dependent environment. -/
theorem measurable_generator (f : State D → ℝ) (hf : (Function.support f).Finite) :
    Measurable (fun p : ℝ × State D => generator control ν T hT v f p.1 p.2) := by
  simp_rw [generator_eq_frozen control ν T hT v f hf]
  exact TimeDependentGeneratorIntegral.measurable_frozenGenerator (influence f hf) Jump.advance
    (rate control ν T hT v) (manuscript_measurable_timeRate control hCoupling ν (driftConstant control) T hT v) f

omit hCoupling in
/-- The current-state generator field of the existing global process. -/
def generatorAt (f : State D → ℝ) (p : Sample (State D) (Jump D) × ℝ) : ℝ :=
  generator control ν T hT v f p.2 (manuscriptProcess control hActivity ν T hT v p.1 p.2)

theorem measurable_generatorAt (f : State D → ℝ) (hf : (Function.support f).Finite) :
    Measurable (generatorAt control hActivity ν T hT v f) :=
  (measurable_generator control ν T hT v hCoupling f hf).comp
    (measurable_snd.prodMk (measurable_manuscriptProcess control hActivity ν T hT v hCoupling))

/-- Genuine joint integrability of the current-state generator on any finite horizon. -/
theorem integrable_generatorAt (f : State D → ℝ) (hf : (Function.support f).Finite) (S : ℝ) :
    Integrable (generatorAt control hActivity ν T hT v f)
      ((law ν.measure (Jump D)).prod (volume.restrict (Ioc 0 S))) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  change Integrable (fun p : Sample (State D) (Jump D) × ℝ =>
    generator control ν T hT v f p.2 (manuscriptProcess control hActivity ν T hT v p.1 p.2)) _
  simp_rw [generator_eq_frozen control ν T hT v f hf]
  exact TimeDependentGeneratorIntegral.integrable_generatorField (law ν.measure (Jump D))
    (influence f hf) Jump.advance (rate control ν T hT v)
    (manuscript_measurable_timeRate control hCoupling ν (driftConstant control) T hT v) f
    (manuscriptProcess control hActivity ν T hT v)
    (measurable_manuscriptProcess control hActivity ν T hT v hCoupling) S
    (rateCap control hActivity ν T hT v f hf)
    (fun x _ j s _ => timeRate_nonnegative κ q _ T j s x)
    (fun x hx j s _ => rate_le_cap control hActivity ν T hT v f hf x hx j s)

/-- Pointwise-in-time generator integrability follows from the same derived bound. -/
theorem integrable_generator_at (f : State D → ℝ) (hf : (Function.support f).Finite) (s : ℝ) :
    Integrable (fun p => generatorAt control hActivity ν T hT v f (p,s))
      (law ν.measure (Jump D)) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact (integrable_const (generatorBound control hActivity ν T hT v f hf)).mono'
    ((measurable_generatorAt control hActivity ν T hT v hCoupling f hf).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    (Eventually.of_forall (fun _ => norm_generator_le control hActivity ν T hT v f hf s _))


/-- Finite-horizon generator integrals are integrable over the actual samples. -/
theorem integrable_timeGenerator (f : State D → ℝ) (hf : (Function.support f).Finite) (S : ℝ) :
    Integrable (fun p => ∫ s in Ioc 0 S, generatorAt control hActivity ν T hT v f (p,s))
      (law ν.measure (Jump D)) :=
  (integrable_generatorAt control hActivity ν T hT v hCoupling f hf S).integral_prod_left

/-- Actual intensity integration gives the current-state time generator.
The predictable/current replacement follows proved exit exhaustion and the
genuine time-null jump set; no generator identity is supplied as a premise. -/
theorem ae_sum_intensity_eq_timeGenerator (f : State D → ℝ) (hf : (Function.support f).Finite)
    (S : ℝ) :
    (fun p => ∑ j, ∫ z, horizonIncrement control hActivity ν T hT v f j S (p,z)
      ∂positiveVolume.prod positiveVolume) =ᵐ[law ν.measure (Jump D)]
      (fun p => ∫ s in Ioc 0 S, generatorAt control hActivity ν T hT v f (p,s)) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  have hZ := (measurable_preState control hActivity ν T hT v hCoupling).mono (predictable_le _) le_rfl
  have hpos (x : State D) (_ : x ∈ influence f hf) (j : Jump D) (s : ℝ) (_ : s ∈ Ioc 0 S) :
      0 ≤ rate control ν T hT v j s x := timeRate_nonnegative κ q _ T j s x
  have hcap (x : State D) (hx : x ∈ influence f hf) (j : Jump D) (s : ℝ) (_ : s ∈ Ioc 0 S) :
      rate control ν T hT v j s x ≤ rateCap control hActivity ν T hT v f hf :=
    rate_le_cap control hActivity ν T hT v f hf x hx j s
  have hl := ae_all_iff.mpr (fun j : Jump D =>
    TimeDependentGeneratorIntegral.ae_intensityIntegral_eq_timeDrift (law ν.measure (Jump D))
      (influence f hf) Jump.advance (rate control ν T hT v)
      (manuscript_measurable_timeRate control hCoupling ν (driftConstant control) T hT v)
      f j (preState control hActivity ν T hT v) hZ S (rateCap control hActivity ν T hT v f hf)
      (fun x hx s hs => hpos x hx j s hs) (fun x hx s hs => hcap x hx j s hs))
  have hg := TimeDependentGeneratorIntegral.ae_sum_timeDrift_eq_generator (law ν.measure (Jump D))
    (influence f hf) Jump.advance (rate control ν T hT v)
    (manuscript_measurable_timeRate control hCoupling ν (driftConstant control) T hT v)
    f (preState control hActivity ν T hT v) hZ S (rateCap control hActivity ν T hT v f hf) hpos hcap
  have hp := TimeDependentGlobalPreStateTime.ae_preState_eq_process_time control.function
    (finite_sublevels control) Jump.advance (rate control ν T hT v)
    (exists_uniform_rate_bounds control _ T hT hActivity
      (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn)
    id 0 ν.measure (manuscript_exhaustive control hActivity ν T hT v hCoupling)
  filter_upwards [hl, hg, hp] with p hl hg hp
  calc
    _ = ∑ j, ∫ s in Ioc 0 S, TimeDependentGeneratorIntegral.labelDrift (influence f hf)
        Jump.advance (rate control ν T hT v) f j s (preState control hActivity ν T hT v p s)
        ∂positiveVolume := by
      apply Finset.sum_congr rfl
      intro j _
      rw [horizonIncrement_eq_localized control hActivity ν T hT v f hf j S]
      exact hl j
    _ = ∫ s in Ioc 0 S, TimeDependentGeneratorIntegral.frozenGenerator (influence f hf)
        Jump.advance (rate control ν T hT v) f s (preState control hActivity ν T hT v p s)
        ∂positiveVolume := hg
    _ = ∫ s in Ioc 0 S, generatorAt control hActivity ν T hT v f (p,s) ∂positiveVolume := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hp] with s hs
      rw [← generator_eq_frozen control ν T hT v f hf]
      exact congrArg (generator control ν T hT v f s) hs
    _ = _ := by rw [TimeDependentDynkin.positiveVolume_restrict_Ioc_zero]

end CarryingCapacity.DeterministicEnvironmentFiniteSupport
