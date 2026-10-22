import CarryingCapacity.DeterministicEnvironmentFiniteSupport
import CarryingCapacity.FiniteJumpForward
import CarryingCapacity.NonlinearFixedPoint

/-!
# Actual prescribed-environment and nonlinear weak forward equations

The equation is derived from the actual global counting equation, finite-test
compensation, and genuine sample-time Fubini. Both the expected generator and
its time integral are integrable. Pushforward laws are actual probability
laws, and on the construction interval their generator uses the original
environment. Evaluation at the proved nonlinear fixed curve then gives the
nonlinear weak equation, without assuming a forward equation or uniqueness.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal

namespace CarryingCapacity.DeterministicEnvironmentForward
open CommonInitialNoise LyapunovFlowSpace DeterministicEnvironmentLyapunov
open DeterministicEnvironmentProcess DeterministicEnvironmentLaw DeterministicEnvironmentFrozen
open DeterministicEnvironmentFiniteSupport MarkedIntensity

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T)
  (v : ManuscriptCurves control.function ν (driftConstant control) T hT)

/-- Genuine time marginals, defined on the full real time line. -/
def lawCurve (s : ℝ) : Measure (State D) :=
  (law ν.measure (Jump D)).map (fun p => manuscriptProcess control hActivity ν T hT v p s)

/-- The expected current-state clamped generator. -/
def expectedGenerator (f : State D → ℝ) (s : ℝ) : ℝ :=
  ∫ p, generatorAt control hActivity ν T hT v f (p,s) ∂law ν.measure (Jump D)

/-- Original coefficients along the prescribed continuous environment. -/
def originalRate (j : Jump D) (s : ℝ) (x : State D) : ℝ :=
  q.rate j x (manuscriptExtension control ν (driftConstant control) T hT v s)

variable (hCoupling : MomentCouplingBound κ q)
include hCoupling

theorem lawCurve_probability (s : ℝ) : IsProbabilityMeasure (lawCurve control hActivity ν T hT v s) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact isProbabilityMeasure_map (measurable_at control hActivity ν T hT v hCoupling s).aemeasurable

theorem integral_lawCurve (f : State D → ℝ) (s : ℝ) :
    (∫ x, f x ∂lawCurve control hActivity ν T hT v s) =
      ∫ p, f (manuscriptProcess control hActivity ν T hT v p s) ∂law ν.measure (Jump D) :=
  integral_map_of_stronglyMeasurable (measurable_at control hActivity ν T hT v hCoupling s)
    (measurable_of_countable f).stronglyMeasurable

/-- Product integrability supplies genuine time integrability of the expected generator. -/
theorem integrableOn_expectedGenerator (f : State D → ℝ) (hf : (Function.support f).Finite) (S : ℝ) :
    IntegrableOn (expectedGenerator control hActivity ν T hT v f) (Ioc 0 S) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact (integrable_generatorAt control hActivity ν T hT v hCoupling f hf S).integral_prod_right

theorem intervalIntegrable_expectedGenerator (f : State D → ℝ) (hf : (Function.support f).Finite)
    (S : ℝ) (hS : 0 ≤ S) :
    IntervalIntegrable (expectedGenerator control hActivity ν T hT v f) volume 0 S :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hS).mpr
    (integrableOn_expectedGenerator control hActivity ν T hT v hCoupling f hf S)

/-- The actual counting equation, proved upstream by localization, on the
same initial-record/noise sample space as all expectations here. -/
theorem ae_counting_identity (f : State D → ℝ) :
    ∀ᵐ p ∂law ν.measure (Jump D), ∀ S : ℝ≥0,
      f (manuscriptProcess control hActivity ν T hT v p S) - f p.1 =
        ∑ j, ∫ z, DeterministicEnvironmentFiniteSupport.horizonIncrement
          control hActivity ν T hT v f j S (p,z) ∂MarkedNoise.countingMeasure j p.2 :=
  TimeDependentGlobalCounting.ae_testFunction_counting_identity control.function
    (finite_sublevels control) Jump.advance (rate control ν T hT v)
    (exists_uniform_rate_bounds control _ T hT hActivity
      (continuous_manuscriptExtension control ν (driftConstant control) T hT v).continuousOn)
    id 0 ν.measure f (manuscript_exhaustive control hActivity ν T hT v hCoupling)

/-- The weak expectation equation is a consequence of the actual counting
identity and compensation, with Fubini justified by finite predecessor support. -/
theorem expectation_eq_initial_add_integral (f : State D → ℝ) (hf : (Function.support f).Finite)
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ p, f (manuscriptProcess control hActivity ν T hT v p t) ∂law ν.measure (Jump D)) =
      (∫ x, f x ∂ν.measure) + ∫ s in (0 : ℝ)..t, expectedGenerator control hActivity ν T hT v f s := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  have hit := integrable_test_at control hActivity ν T hT v hCoupling f hf t
  have hi0 : Integrable (fun p : Sample (State D) (Jump D) => f p.1) (law ν.measure (Jump D)) :=
    (integrable_const (functionBound f hf)).mono'
      ((measurable_of_countable f).comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall (fun p => norm_le_functionBound f hf p.1))
  have hinit : (∫ p : Sample (State D) (Jump D), f p.1 ∂law ν.measure (Jump D)) = ∫ x, f x ∂ν.measure := by
    have he := integral_map_of_stronglyMeasurable (μ := law ν.measure (Jump D))
      measurable_fst (measurable_of_countable f).stronglyMeasurable
    rw [CommonInitialNoise.map_initial] at he
    exact he.symm
  have hcount (j : Jump D) := integrable_counting_integral control hActivity ν T hT v hCoupling f hf j t
  have hintensity (j : Jump D) :=
    (integrable_horizonIncrement control hActivity ν T hT v hCoupling f hf j t).integral_prod_left
  have he : (∫ p, f (manuscriptProcess control hActivity ν T hT v p t) ∂law ν.measure (Jump D)) -
      (∫ x, f x ∂ν.measure) = ∫ s in Ioc 0 t, expectedGenerator control hActivity ν T hT v f s := by
    calc
      _ = ∫ p, (f (manuscriptProcess control hActivity ν T hT v p t) - f p.1) ∂law ν.measure (Jump D) := by
        rw [integral_sub hit hi0, hinit]
      _ = ∫ p, ∑ j, ∫ z, DeterministicEnvironmentFiniteSupport.horizonIncrement
          control hActivity ν T hT v f j t (p,z) ∂MarkedNoise.countingMeasure j p.2 ∂law ν.measure (Jump D) :=
        integral_congr_ae ((ae_counting_identity control hActivity ν T hT v hCoupling f).mono
          (fun _ hp => hp ⟨t,ht⟩))
      _ = ∑ j, ∫ p, ∫ z, DeterministicEnvironmentFiniteSupport.horizonIncrement
          control hActivity ν T hT v f j t (p,z) ∂MarkedNoise.countingMeasure j p.2 ∂law ν.measure (Jump D) :=
        integral_finset_sum _ (fun j _ => hcount j)
      _ = ∑ j, ∫ p, ∫ z, DeterministicEnvironmentFiniteSupport.horizonIncrement
          control hActivity ν T hT v f j t (p,z) ∂positiveVolume.prod positiveVolume ∂law ν.measure (Jump D) := by
        apply Finset.sum_congr rfl
        intro j _
        exact compensation_horizonIncrement control hActivity ν T hT v hCoupling f hf j t
      _ = ∫ p, ∑ j, ∫ z, DeterministicEnvironmentFiniteSupport.horizonIncrement
          control hActivity ν T hT v f j t (p,z) ∂positiveVolume.prod positiveVolume ∂law ν.measure (Jump D) :=
        (integral_finset_sum _ (fun j _ => hintensity j)).symm
      _ = ∫ p, ∫ s in Ioc 0 t, generatorAt control hActivity ν T hT v f (p,s) ∂volume ∂law ν.measure (Jump D) :=
        integral_congr_ae (ae_sum_intensity_eq_timeGenerator control hActivity ν T hT v hCoupling f hf t)
      _ = _ := integral_integral_swap (integrable_generatorAt control hActivity ν T hT v hCoupling f hf t)
  rw [intervalIntegral.integral_of_le ht]
  linarith

/-- The current generator expectation is exactly the generator tested against
its genuine time marginal. -/
theorem integral_generator_lawCurve (f : State D → ℝ) (s : ℝ) :
    (∫ x, FiniteJumpForward.generator Jump.advance (rate control ν T hT v) f s x
      ∂lawCurve control hActivity ν T hT v s) = expectedGenerator control hActivity ν T hT v f s :=
  integral_lawCurve control hActivity ν T hT v hCoupling _ s

/-- The actual marginal curve is a weak forward solution for the clamped
coefficients, with genuine tested time integrability. -/
theorem isSolution_clamped : FiniteJumpForward.IsSolution Jump.advance
    (rate control ν T hT v) ν.measure (lawCurve control hActivity ν T hT v) T where
  probability := fun t _ => lawCurve_probability control hActivity ν T hT v hCoupling t
  integrable := by
    intro f hf
    simp_rw [integral_generator_lawCurve control hActivity ν T hT v hCoupling f]
    exact intervalIntegrable_expectedGenerator control hActivity ν T hT v hCoupling f hf T hT
  equation := by
    intro f hf t ht
    simp_rw [integral_generator_lawCurve control hActivity ν T hT v hCoupling f]
    rw [integral_lawCurve control hActivity ν T hT v hCoupling f t]
    exact expectation_eq_initial_add_integral control hActivity ν T hT v hCoupling f hf t ht.1


omit hCoupling in
/-- The clamped and original generators coincide throughout the construction interval. -/
theorem generator_eq_originalRate (f : State D → ℝ) (s : ℝ) (hs : s ∈ Icc 0 T) (x : State D) :
    FiniteJumpForward.generator Jump.advance (rate control ν T hT v) f s x =
      FiniteJumpForward.generator Jump.advance (originalRate control ν T hT v) f s x := by
  change generator control ν T hT v f s x = _
  rw [generator_eq_original control ν T hT v f s hs x]
  rfl

/-- The actual marginal law solves the weak equation with the original
prescribed coefficients on `[0,T]`, not merely their clamped extension. -/
theorem isSolution : FiniteJumpForward.IsSolution Jump.advance
    (originalRate control ν T hT v) ν.measure (lawCurve control hActivity ν T hT v) T := by
  have hc := isSolution_clamped control hActivity ν T hT v hCoupling
  refine ⟨hc.probability, ?_, ?_⟩
  · intro f hf
    apply (hc.integrable f hf).congr
    rw [uIoc_of_le hT]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => generator_eq_originalRate control ν T hT v f s ⟨hs.1.le,hs.2⟩ x)
  · intro f hf t ht
    rw [hc.equation f hf t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => generator_eq_originalRate control ν T hT v f s
      ⟨hs.1, hs.2.trans ht.2⟩ x)

/-- Genuine interval integrability for the original, law-tested generator. -/
theorem intervalIntegrable_originalGenerator (f : State D → ℝ) (hf : (Function.support f).Finite) :
    IntervalIntegrable (fun s => ∫ x,
      q.generator (manuscriptExtension control ν (driftConstant control) T hT v s) f x
      ∂lawCurve control hActivity ν T hT v s) volume 0 T :=
  (isSolution control hActivity ν T hT v hCoupling).integrable f hf

/-- The weak forward equation written directly for the actual time marginals
and the original environmental generator. -/
theorem law_forward_equation (f : State D → ℝ) (hf : (Function.support f).Finite)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (∫ x, f x ∂lawCurve control hActivity ν T hT v t) = (∫ x, f x ∂ν.measure) +
      ∫ s in (0 : ℝ)..t, ∫ x,
        q.generator (manuscriptExtension control ν (driftConstant control) T hT v s) f x
        ∂lawCurve control hActivity ν T hT v s :=
  (isSolution control hActivity ν T hT v hCoupling).equation f hf t ht

/-- The same original-rate equation as an expectation of the actual process. -/
theorem expectation_eq_original_generator (f : State D → ℝ) (hf : (Function.support f).Finite)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (∫ p, f (manuscriptProcess control hActivity ν T hT v p t) ∂law ν.measure (Jump D)) =
      (∫ x, f x ∂ν.measure) + ∫ s in (0 : ℝ)..t, ∫ p,
        q.generator (manuscriptExtension control ν (driftConstant control) T hT v s) f
          (manuscriptProcess control hActivity ν T hT v p s) ∂law ν.measure (Jump D) := by
  have h := law_forward_equation control hActivity ν T hT v hCoupling f hf t ht
  simp_rw [integral_lawCurve control hActivity ν T hT v hCoupling] at h
  exact h

section Nonlinear
omit v
variable (hInitial : Integrable control.function ν.measure)

/-- The fixed environment's measure equals the actual pushforward law on
the original interval. This is the proved self-consistency, not a premise. -/
theorem nonlinear_law_eq (s : ℝ) (hs : s ∈ Icc 0 T) :
    lawCurve control hActivity ν T hT
      (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hInitial) s =
      (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hInitial s).measure :=
  (NonlinearFixedPoint.environment_measure_eq_marginal control hActivity ν T hT hCoupling hInitial ⟨s,hs⟩).symm

/-- The actual nonlinear curve has a genuinely integrable tested drift. -/
theorem intervalIntegrable_nonlinearGenerator (f : State D → ℝ) (hf : (Function.support f).Finite) :
    IntervalIntegrable (fun s => ∫ x,
      q.generator (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hInitial s) f x
      ∂(NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hInitial s).measure) volume 0 T := by
  have h := intervalIntegrable_originalGenerator control hActivity ν T hT
    (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hInitial) hCoupling f hf
  apply h.congr
  rw [uIoc_of_le hT]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [nonlinear_law_eq control hActivity ν T hT hCoupling hInitial s ⟨hs.1.le,hs.2⟩]
  rfl

/-- The actual fixed law curve satisfies the nonlinear weak forward equation
for every finitely supported test, with its own current law in the generator. -/
theorem nonlinear_forward_equation (f : State D → ℝ) (hf : (Function.support f).Finite)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (∫ x, f x ∂(NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hInitial t).measure) =
      (∫ x, f x ∂ν.measure) + ∫ s in (0 : ℝ)..t, ∫ x,
        q.generator (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hInitial s) f x
        ∂(NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hInitial s).measure := by
  have h := law_forward_equation control hActivity ν T hT
    (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hInitial) hCoupling f hf t ht
  rw [nonlinear_law_eq control hActivity ν T hT hCoupling hInitial t ht] at h
  rw [h]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  dsimp only
  rw [nonlinear_law_eq control hActivity ν T hT hCoupling hInitial s ⟨hs.1,hs.2.trans ht.2⟩]
  rfl


/-- The canonical nonlinear law belongs to the genuine weak-solution class
for its own continuous environment, including tested time integrability. -/
theorem nonlinear_isSolution : FiniteJumpForward.IsSolution Jump.advance
    (fun j s x => q.rate j x (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hInitial s))
    ν.measure (fun s => (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hInitial s).measure) T where
  probability := fun s _ => (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hInitial s).probability
  integrable := fun f hf => intervalIntegrable_nonlinearGenerator control hActivity ν T hT hCoupling hInitial f hf
  equation := fun f hf t ht => nonlinear_forward_equation control hActivity ν T hT hCoupling hInitial f hf t ht

end Nonlinear

end CarryingCapacity.DeterministicEnvironmentForward
