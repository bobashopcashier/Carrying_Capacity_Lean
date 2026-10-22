import CarryingCapacity.ConfigurationMartingale
import CarryingCapacity.UsualMartingale

/-!
# The particle generator martingale in the usual filtration

Finite support makes both the test and its actual empirical generator globally
bounded. This supplies compact-time domination and continuity of the drift
primitive, so the raw generator martingale passes to the usual augmentation.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical Topology NNReal

namespace CarryingCapacity.ConfigurationUsualMartingale
open ConfigurationLocalization CommonInitialNoise ConfigurationMartingale
  FiniteSupportGeometry

variable {A : Type*} [MeasurableSpace A] {N D : ℕ}
  {κ : MomentScale} {q : Rates D (MomentLaw κ D)} (control : LyapunovControl κ q)
  (hN : 0 < N) (initial : A → Configuration N D)
  (F : Configuration N D → ℝ) (hF : (Function.support F).Finite)
  (hinit : Measurable initial)

def driftPrimitive (p : Sample A (Label N D)) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, generator κ q hN F
    (ConfigurationNonexplosion.process control hN initial p s)

theorem generatorBound_nonnegative : 0 ≤ generatorBound κ q hN F hF :=
  (norm_nonneg _).trans (norm_generator_le κ q hN F hF 0)

include hinit hF

theorem intervalIntegrable_generator (p : Sample A (Label N D)) (a b : ℝ) :
    IntervalIntegrable (fun s => generator κ q hN F
      (ConfigurationNonexplosion.process control hN initial p s)) volume a b := by
  have hm := (measurable_of_countable (generator κ q hN F)).comp
    ((ConfigurationNonexplosion.measurable_process control hN initial hinit).comp
      ((measurable_const (a := p)).prodMk measurable_id))
  exact (intervalIntegrable_const (c := generatorBound κ q hN F hF)).mono_fun'
    hm.aestronglyMeasurable (Filter.Eventually.of_forall
      (fun s => norm_generator_le κ q hN F hF _))

theorem continuous_driftPrimitive (p : Sample A (Label N D)) :
    Continuous (driftPrimitive control hN initial F p) :=
  intervalIntegral.continuous_primitive
    (intervalIntegrable_generator control hN initial F hF hinit p) 0

omit hinit [MeasurableSpace A] in
theorem norm_driftPrimitive_le (p : Sample A (Label N D)) (t : ℝ≥0) :
    ‖driftPrimitive control hN initial F p t‖ ≤ generatorBound κ q hN F hF * t := by
  simpa only [driftPrimitive, sub_zero, abs_of_nonneg t.coe_nonneg] using
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (t : ℝ))
      (fun s _ => norm_generator_le κ q hN F hF
        (ConfigurationNonexplosion.process control hN initial p s))

omit hinit hF [MeasurableSpace A] in
theorem generatorProcess_eq (p : Sample A (Label N D)) (t : ℝ≥0) :
    generatorProcess control hN initial F t p =
      F (ConfigurationNonexplosion.process control hN initial p t) - F (initial p.1) -
        driftPrimitive control hN initial F p t := by
  rw [generatorProcess, driftPrimitive, intervalIntegral.integral_of_le t.coe_nonneg,
    InitialFrozenExpectation.positiveVolume_restrict_Ioc_zero]

omit hinit [MeasurableSpace A] in
theorem norm_generatorProcess_le (p : Sample A (Label N D)) (t : ℝ≥0) :
    ‖generatorProcess control hN initial F t p‖ ≤
      2 * functionBound F hF + generatorBound κ q hN F hF * t := by
  rw [generatorProcess_eq]
  calc
    _ ≤ ‖F (ConfigurationNonexplosion.process control hN initial p t)‖ +
        ‖F (initial p.1)‖ + ‖driftPrimitive control hN initial F p t‖ :=
      (norm_sub_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
    _ ≤ functionBound F hF + functionBound F hF + generatorBound κ q hN F hF * t :=
      add_le_add (add_le_add (norm_le_functionBound F hF _) (norm_le_functionBound F hF _))
        (norm_driftPrimitive_le control hN initial F hF p t)
    _ = _ := by ring

variable (μ : Measure A) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem ae_rightContinuous : ∀ᵐ p ∂law μ (Label N D), ∀ s : ℝ≥0,
    ContinuousWithinAt (fun t : ℝ≥0 => generatorProcess control hN initial F t p) (Ici s) s := by
  filter_upwards [ArbitraryInitialNonexplosion.configuration_cadlag control hN initial μ]
    with p hp
  intro s
  have hstate : ContinuousWithinAt
      (fun t : ℝ≥0 => ConfigurationNonexplosion.process control hN initial p t) (Ici s) s :=
    (hp.1 s s.coe_nonneg).comp NNReal.continuous_coe.continuousWithinAt
      (fun t ht => ht)
  have hf : ContinuousWithinAt
      (fun t : ℝ≥0 => F (ConfigurationNonexplosion.process control hN initial p t)) (Ici s) s :=
    continuous_of_discreteTopology.continuousAt.comp_continuousWithinAt hstate
  have hd := ((continuous_driftPrimitive control hN initial F hF hinit p).comp
    NNReal.continuous_coe).continuousWithinAt (s := Ici s) (x := s)
  have he : (fun t : ℝ≥0 => generatorProcess control hN initial F t p) =
      (fun t : ℝ≥0 => F (ConfigurationNonexplosion.process control hN initial p t) -
        F (initial p.1) - driftPrimitive control hN initial F p t) :=
    funext (generatorProcess_eq control hN initial F p)
  rw [he]
  exact (hf.sub continuousWithinAt_const).sub hd

/-- The actual finite-support generator martingale in the completed
right-continuous initial/counting-noise filtration. -/
theorem generator_martingale_usual :
    Martingale (generatorProcess control hN initial F)
      (UsualMartingale.usualNonnegative (law μ (Label N D)) (filtration A (Label N D)))
      (UsualFiltration.completedLaw (law μ (Label N D))) := by
  apply UsualMartingale.martingale_usual (law μ (Label N D)) (filtration A (Label N D))
    (generator_martingale control hN initial F hF μ hinit)
    (ae_rightContinuous control hN initial F hF hinit μ)
  intro T
  refine ⟨fun _ => 2 * functionBound F hF + generatorBound κ q hN F hF * T,
    integrable_const _, Filter.Eventually.of_forall (fun p t ht => ?_)⟩
  exact (norm_generatorProcess_le control hN initial F hF p t).trans
    (add_le_add_left (mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ T from ht)
      (generatorBound_nonnegative hN F hF)) _)

end CarryingCapacity.ConfigurationUsualMartingale
