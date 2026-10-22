import CarryingCapacity.ConfigurationMartingale

/-!
# Weak forward equation for the actual particle law

For finitely supported configuration tests, both the test and its raw generator
are bounded. The proved generator martingale and genuine sample-time Fubini
therefore give the weak forward equation, without a postulated evolution law
or an initial moment assumption.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical NNReal

namespace CarryingCapacity.ConfigurationForwardEquation
open ConfigurationLocalization CommonInitialNoise FiniteSupportGeometry

variable {A : Type*} [MeasurableSpace A] {N D : ℕ}
  {κ : MomentScale} {q : Rates D (MomentLaw κ D)} (control : LyapunovControl κ q)
  (hN : 0 < N) (initial : A → Configuration N D) (F : Configuration N D → ℝ)
  (hF : (Function.support F).Finite)
  (μ : Measure A) [IsProbabilityMeasure μ] (hinit : Measurable initial)

/-- The actual configuration-test expectation. -/
def expectation (t : ℝ) : ℝ :=
  ∫ p, F (ConfigurationNonexplosion.process control hN initial p t) ∂law μ (Label N D)

/-- The expected raw configuration generator. -/
def expectedGenerator (t : ℝ) : ℝ :=
  ∫ p, generator κ q hN F (ConfigurationNonexplosion.process control hN initial p t)
    ∂law μ (Label N D)

include hinit hF

/-- Joint integrability on every finite time interval follows from the
actual finite backward support of the generator. -/
theorem integrable_generatorField (s t : ℝ) :
    Integrable (fun p : Sample A (Label N D) × ℝ =>
      generator κ q hN F (ConfigurationNonexplosion.process control hN initial p.1 p.2))
      ((law μ (Label N D)).prod (volume.restrict (Ioc s t))) := by
  letI : IsFiniteMeasure (volume.restrict (Ioc s t)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  exact ⟨((measurable_of_countable (generator κ q hN F)).comp
    (ConfigurationNonexplosion.measurable_process control hN initial hinit)).aestronglyMeasurable,
    hasFiniteIntegral_of_bounded (Eventually.of_forall (fun p =>
      norm_generator_le κ q hN F hF _))⟩

/-- Fubini for the unrestricted current-state generator. -/
theorem integral_timeGenerator_swap (s t : ℝ) :
    (∫ p, ∫ u in Ioc s t, generator κ q hN F
      (ConfigurationNonexplosion.process control hN initial p u) ∂volume ∂law μ (Label N D)) =
      ∫ u in Ioc s t, expectedGenerator control hN initial F μ u :=
  integral_integral_swap (integrable_generatorField control hN initial F hF μ hinit s t)

omit hF in
/-- The expected generator is a measurable function of time. -/
theorem stronglyMeasurable_expectedGenerator :
    StronglyMeasurable (expectedGenerator control hN initial F μ) :=
  ((measurable_of_countable (generator κ q hN F)).comp
    (ConfigurationNonexplosion.measurable_process control hN initial hinit)).stronglyMeasurable.integral_prod_left'

omit hinit in
/-- A deterministic uniform bound for the actual expected generator. -/
theorem norm_expectedGenerator_le (t : ℝ) :
    ‖expectedGenerator control hN initial F μ t‖ ≤ generatorBound κ q hN F hF := by
  have h := norm_integral_le_of_norm_le_const (μ := law μ (Label N D))
    (Eventually.of_forall (fun p : Sample A (Label N D) => norm_generator_le κ q hN F hF
      (ConfigurationNonexplosion.process control hN initial p t)))
  simpa only [expectedGenerator, measureReal_univ_eq_one, mul_one] using h

/-- The expected generator is integrable on every finite interval. -/
theorem intervalIntegrable_expectedGenerator (s t : ℝ) :
    IntervalIntegrable (expectedGenerator control hN initial F μ) volume s t := by
  have hi (a b : ℝ) : IntegrableOn (expectedGenerator control hN initial F μ) (Ioc a b) := by
    letI : IsFiniteMeasure (volume.restrict (Ioc a b)) :=
      isFiniteMeasure_restrict.mpr (by simp)
    exact ⟨(stronglyMeasurable_expectedGenerator control hN initial F μ hinit).aestronglyMeasurable,
      hasFiniteIntegral_of_bounded (Eventually.of_forall (fun u =>
        norm_expectedGenerator_le control hN initial F hF μ u))⟩
  exact ⟨hi s t, hi t s⟩

/-- The actual finite-particle law satisfies the weak forward equation for
every finitely supported configuration test and any initial probability law. -/
theorem expectation_eq_initial_add_integral (t : ℝ≥0) :
    expectation control hN initial F μ t = (∫ a, F (initial a) ∂μ) +
      ∫ s in Ioc 0 (t : ℝ), expectedGenerator control hN initial F μ s := by
  have ht := FiniteSupportGlobal.integrable_testFunction_at control hN initial F hF μ hinit t
  have h0 : Integrable (fun a => F (initial a)) μ :=
    (integrable_const (functionBound F hF)).mono'
      ((measurable_of_countable F).comp hinit).aestronglyMeasurable
      (Eventually.of_forall (fun a => norm_le_functionBound F hF _))
  have hi := InitialFrozenDynkin.integrable_initial_testFunction (J := Label N D) initial μ F h0
  have hd : Integrable (fun p => ∫ s in Ioc 0 (t : ℝ), generator κ q hN F
      (ConfigurationNonexplosion.process control hN initial p s) ∂MarkedIntensity.positiveVolume)
      (law μ (Label N D)) := by
    simp_rw [InitialFrozenExpectation.positiveVolume_restrict_Ioc_zero]
    exact (integrable_generatorField control hN initial F hF μ hinit 0 t).integral_prod_left
  have hz := ConfigurationMartingale.expectation_generatorProcess_eq_zero control hN initial F hF μ hinit t
  simp only [ConfigurationMartingale.generatorProcess] at hz
  have hsub := integral_sub (ht.sub hi) hd
  simp only [Pi.sub_apply] at hsub
  rw [hsub, integral_sub ht hi] at hz
  have he : (∫ p : Sample A (Label N D), F (initial p.1) ∂law μ (Label N D)) =
      ∫ a, F (initial a) ∂μ := by
    simpa only [measureReal_univ_eq_one, one_smul] using
      (integral_fun_fst (μ := μ) (ν := MarkedNoise.law (Label N D)) (fun a => F (initial a)))
  rw [he] at hz
  simp_rw [InitialFrozenExpectation.positiveVolume_restrict_Ioc_zero] at hz
  rw [integral_timeGenerator_swap control hN initial F hF μ hinit 0 t] at hz
  change (∫ p, F (ConfigurationNonexplosion.process control hN initial p t) ∂law μ (Label N D)) = _
  linarith

end CarryingCapacity.ConfigurationForwardEquation
