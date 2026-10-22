import CarryingCapacity.SynchronousGlobalCounting
import CarryingCapacity.TimeDependentGlobalPreStateTime
import CarryingCapacity.InitialPredictableCompensation

/-!
# Nonnegative compensation for actual synchronous positive increments

Both constructed paths use the same initial record and marked noise. Their
positive distance increments are predictable. Nonnegative predictable
compensation and exact height integration give an extended expected-activity
identity, without assuming a finite activity expectation or an expected
coupling inequality. Genuine exit exhaustion removes pre-jump notation from
the time integral.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace CarryingCapacity.SynchronousCompensation
open CommonInitialNoise MarkedIntensity PredictableSets PredictableTime
open PredictableStepApproximation SynchronousPositiveIncrement
open TimeDependentGlobalCounting SynchronousGlobalCounting
open LyapunovLocalization (active)

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

variable {A E J : Type*} [MeasurableSpace A] [DecidableEq E] [Fintype J]
  [TopologicalSpace E] [PolishSpace E] [Countable E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [BorelSpace E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rateX : J → ℝ → E → ℝ)
  (boundX : ∀ n : ℕ, ∃ C : ℝ,
    ∀ x ∈ active V hfinite n, ∀ j t, rateX j t x ≤ C)
  (rateY : J → ℝ → E → ℝ)
  (boundY : ∀ n : ℕ, ∃ C : ℝ,
    ∀ x ∈ active V hfinite n, ∀ j t, rateY j t x ≤ C)
  (initialX initialY : A → E) (e : E)
  (hRateX : ∀ j x, Measurable (fun t => rateX j t x))
  (hRateY : ∀ j x, Measurable (fun t => rateY j t x))
  (hinitX : Measurable initialX) (hinitY : Measurable initialY)

/-- The exact three-region height activity at the actual current states. -/
def currentActivity (ρ : E → E → ℝ) (j : J) (p : Sample A J × ℝ) : ℝ :=
  let x := TimeDependentGlobalProcess.process V hfinite jump rateX boundX initialX e p.1 p.2
  let y := TimeDependentGlobalProcess.process V hfinite jump rateY boundY initialY e p.1 p.2
  heightActivity ρ jump j (rateX j p.2 x) (rateY j p.2 y) x y

/-- The same height activity at the actual predictable pre-jump states. -/
def preActivity (ρ : E → E → ℝ) (j : J) (p : Sample A J × ℝ) : ℝ :=
  let x := preState V hfinite jump rateX boundX initialX e p.1 p.2
  let y := preState V hfinite jump rateY boundY initialY e p.1 p.2
  heightActivity ρ jump j (rateX j p.2 x) (rateY j p.2 y) x y

include hRateX hRateY hinitX hinitY

omit V hfinite boundX boundY rateX rateY initialX initialY e hRateX hRateY hinitX hinitY
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E] [Fintype J] [DecidableEq E]
  [MeasurableSpace A] in
/-- The height activity is measurable after substitution of genuine state
and rate fields on any measurable source space. -/
theorem measurable_heightActivity_comp {Ω : Type*} [MeasurableSpace Ω]
    (ρ : E → E → ℝ) (j : J) (a b : Ω → ℝ) (X Y : Ω → E)
    (ha : Measurable a) (hb : Measurable b) (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun ω => heightActivity ρ jump j (a ω) (b ω) (X ω) (Y ω)) := by
  have hxy := hX.prodMk hY
  have hbase := (measurable_of_countable (fun p : E × E => ρ p.1 p.2)).comp hxy
  have hshared := (measurable_of_countable (fun p : E × E => ρ (jump j p.1) (jump j p.2))).comp hxy
  have hleft := (measurable_of_countable (fun p : E × E => ρ (jump j p.1) p.2)).comp hxy
  have hright := (measurable_of_countable (fun p : E × E => ρ p.1 (jump j p.2))).comp hxy
  exact (((ha.min hb).mul ((hshared.sub hbase).max measurable_const)).add
    (((ha.sub hb).max measurable_const).mul ((hleft.sub hbase).max measurable_const))).add
      (((hb.sub ha).max measurable_const).mul ((hright.sub hbase).max measurable_const))

theorem measurable_currentActivity (ρ : E → E → ℝ) (j : J) :
    Measurable (currentActivity V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j) := by
  have hX := TimeDependentGlobalProcess.measurable_process
    V hfinite jump rateX boundX initialX e hRateX hinitX
  have hY := TimeDependentGlobalProcess.measurable_process
    V hfinite jump rateY boundY initialY e hRateY hinitY
  exact measurable_heightActivity_comp jump ρ j _ _ _ _
    ((measurable_coefficient (rateX j) (hRateX j)).comp (measurable_snd.prodMk hX))
    ((measurable_coefficient (rateY j) (hRateY j)).comp (measurable_snd.prodMk hY)) hX hY

/-- The actual synchronous positive-increment field is measurable in the
raw initial-record/noise predictable sigma algebra. -/
theorem measurable_positiveField (ρ : E → E → ℝ) (j : J) (T : ℝ) :
    Measurable[predictable (filtration A J)]
      (positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j T) := by
  letI : MeasurableSpace (Sample A J × (ℝ × ℝ)) := predictable (filtration A J)
  let X := fun p : Sample A J × (ℝ × ℝ) =>
    preState V hfinite jump rateX boundX initialX e p.1 p.2.1
  let Y := fun p : Sample A J × (ℝ × ℝ) =>
    preState V hfinite jump rateY boundY initialY e p.1 p.2.1
  have hX : Measurable X := measurable_preState V hfinite jump rateX boundX initialX e hRateX hinitX
  have hY : Measurable Y := measurable_preState V hfinite jump rateY boundY initialY e hRateY hinitY
  have ha := measurable_evaluation (filtration A J) (rateX j) (hRateX j) X hX
  have hb := measurable_evaluation (filtration A J) (rateY j) (hRateY j) Y hY
  have hU := measurable_positiveHeight (filtration A J)
  have hF := (measurable_positiveIncrement_comp ρ jump j _ _ _ X Y ha hb hU hX hY).indicator
      (measurableSet_predictable_rectangle (filtration A J) 0 T le_rfl
        univ MeasurableSet.univ univ MeasurableSet.univ)
  convert hF using 1
  funext p
  by_cases ht : p.2.1 ∈ Ioc 0 T
  · simp [positiveField, positiveIncrement, pairUpdate, X, Y,
      rectangle, Set.indicator_apply, ht, positiveTime, positiveHeight, ht.1]
  · simp [positiveField, rectangle, Set.indicator_apply, ht]

/-- Actual nonnegative predictable compensation, with possibly infinite
expectations on both sides and no exit-exhaustion or integrability premise. -/
theorem compensation_positiveField (μ : Measure A) [IsProbabilityMeasure μ]
    (ρ : E → E → ℝ) (j : J) (T : ℝ) :
    (∫⁻ p, ∫⁻ q, ENNReal.ofReal
      (positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j T (p,q))
      ∂MarkedNoise.countingMeasure j p.2 ∂law μ J) =
    ∫⁻ p, ∫⁻ q, ENNReal.ofReal
      (positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j T (p,q))
      ∂positiveVolume.prod positiveVolume ∂law μ J :=
  InitialPredictableCompensation.compensation_nonnegative μ j _
    ((measurable_positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e
      hRateX hRateY hinitX hinitY ρ j T).ennreal_ofReal)

/-- Pointwise height integration gives the true synchronous activity,
including the shared-jump contribution. -/
theorem intensityIntegral_eq_preActivity
    (hqX : ∀ j t x, 0 ≤ rateX j t x) (hqY : ∀ j t x, 0 ≤ rateY j t x)
    (ρ : E → E → ℝ) (j : J) (T : ℝ) (p : Sample A J) :
    (∫⁻ q, ENNReal.ofReal
      (positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j T (p,q))
      ∂positiveVolume.prod positiveVolume) =
    ∫⁻ t in Ioc 0 T, ENNReal.ofReal
      (preActivity V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j (p,t))
      ∂positiveVolume := by
  have hm := ((measurable_positiveField V hfinite jump rateX boundX rateY boundY
    initialX initialY e hRateX hRateY hinitX hinitY ρ j T).mono
      (predictable_le _) le_rfl).ennreal_ofReal
  have hm' : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal
      (positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j T (p,q))) :=
    hm.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod _ hm'.aemeasurable,
    ← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ Ioc 0 T
  · simp only [positiveField_apply, ht, if_true, Set.indicator_of_mem ht]
    exact lintegral_positiveIncrement ρ jump j _ _ _ _ (hqX j t _) (hqY j t _)
  · simp [positiveField_apply, ht]

omit hRateX hRateY hinitX hinitY [Countable E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [BorelSpace E] in
/-- The genuine exhausted paths allow both pre-states to be replaced
simultaneously in all time-activity integrals. -/
theorem ae_preActivity_eq_currentActivity (μ : Measure A)
    (hexhaustX : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < TimeDependentLocalization.exit V hfinite jump rateX boundX initialX n p)
    (hexhaustY : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < TimeDependentLocalization.exit V hfinite jump rateY boundY initialY n p) :
    ∀ᵐ p ∂law μ J, ∀ᵐ t ∂positiveVolume, ∀ (ρ : E → E → ℝ) (j : J),
      preActivity V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j (p,t) =
        currentActivity V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j (p,t) := by
  filter_upwards [TimeDependentGlobalPreStateTime.ae_preState_eq_process_time
    V hfinite jump rateX boundX initialX e μ hexhaustX,
    TimeDependentGlobalPreStateTime.ae_preState_eq_process_time
    V hfinite jump rateY boundY initialY e μ hexhaustY] with p hX hY
  filter_upwards [hX, hY] with t htX htY
  intro ρ j
  simp only [preActivity, currentActivity, htX, htY]

/-- Extended expected synchronous activity of the actual paths. No finite
expectation or stochastic coupling inequality is an input. -/
theorem expected_positiveField_eq_timeActivity (μ : Measure A) [IsProbabilityMeasure μ]
    (hqX : ∀ j t x, 0 ≤ rateX j t x) (hqY : ∀ j t x, 0 ≤ rateY j t x)
    (hexhaustX : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < TimeDependentLocalization.exit V hfinite jump rateX boundX initialX n p)
    (hexhaustY : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < TimeDependentLocalization.exit V hfinite jump rateY boundY initialY n p)
    (ρ : E → E → ℝ) (j : J) (T : ℝ) :
    (∫⁻ p, ∫⁻ q, ENNReal.ofReal
      (positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j T (p,q))
      ∂MarkedNoise.countingMeasure j p.2 ∂law μ J) =
    ∫⁻ t in Ioc 0 T, ∫⁻ p, ENNReal.ofReal
      (currentActivity V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j (p,t))
      ∂law μ J ∂positiveVolume := by
  rw [compensation_positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e
    hRateX hRateY hinitX hinitY μ ρ j T]
  simp_rw [intensityIntegral_eq_preActivity V hfinite jump rateX boundX rateY boundY
    initialX initialY e hRateX hRateY hinitX hinitY hqX hqY ρ j T]
  calc
    _ = ∫⁻ p, ∫⁻ t in Ioc 0 T, ENNReal.ofReal
        (currentActivity V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j (p,t))
        ∂positiveVolume ∂law μ J := by
      apply lintegral_congr_ae
      filter_upwards [ae_preActivity_eq_currentActivity V hfinite jump rateX boundX rateY boundY
        initialX initialY e μ hexhaustX hexhaustY] with p hp
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae hp] with t ht
      exact congrArg ENNReal.ofReal (ht ρ j)
    _ = _ := lintegral_lintegral_swap
      (measurable_currentActivity V hfinite jump rateX boundX rateY boundY initialX initialY e
        hRateX hRateY hinitX hinitY ρ j).ennreal_ofReal.aemeasurable

/-- The complete finite-label expected positive-jump sum is exactly the
time integral of the current synchronous height activities. -/
theorem expected_sum_positiveField_eq_timeActivity (μ : Measure A) [IsProbabilityMeasure μ]
    (hqX : ∀ j t x, 0 ≤ rateX j t x) (hqY : ∀ j t x, 0 ≤ rateY j t x)
    (hexhaustX : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < TimeDependentLocalization.exit V hfinite jump rateX boundX initialX n p)
    (hexhaustY : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < TimeDependentLocalization.exit V hfinite jump rateY boundY initialY n p)
    (ρ : E → E → ℝ) (T : ℝ) :
    (∫⁻ p, ∑ j : J, ∫⁻ q, ENNReal.ofReal
      (positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j T (p,q))
      ∂MarkedNoise.countingMeasure j p.2 ∂law μ J) =
    ∫⁻ t in Ioc 0 T, ∫⁻ p, ∑ j : J, ENNReal.ofReal
      (currentActivity V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j (p,t))
      ∂law μ J ∂positiveVolume := by
  classical
  have hm (j : J) := (measurable_currentActivity V hfinite jump rateX boundX rateY boundY
    initialX initialY e hRateX hRateY hinitX hinitY ρ j).ennreal_ofReal
  rw [lintegral_finset_sum Finset.univ (fun j _ =>
    InitialPredictableCompensation.measurable_countingIntegral j _
      (((measurable_positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e
        hRateX hRateY hinitX hinitY ρ j T).mono (predictable_le _) le_rfl).ennreal_ofReal))]
  simp_rw [expected_positiveField_eq_timeActivity V hfinite jump rateX boundX rateY boundY
    initialX initialY e hRateX hRateY hinitX hinitY μ hqX hqY hexhaustX hexhaustY ρ]
  rw [← lintegral_finset_sum Finset.univ (fun j _ => (hm j).lintegral_prod_left')]
  apply lintegral_congr
  intro t
  exact (lintegral_finset_sum Finset.univ (fun j _ =>
    (hm j).comp (measurable_id.prodMk measurable_const))).symm

/-- Actual pathwise synchronous domination and proved predictable compensation
give the extended expected-distance inequality. No expected inequality, finite
activity expectation or Bochner integrability is assumed. -/
theorem expected_distance_le_activity (μ : Measure A) [IsProbabilityMeasure μ]
    (hqX : ∀ j t x, 0 ≤ rateX j t x) (hqY : ∀ j t x, 0 ≤ rateY j t x)
    (hexhaustX : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < TimeDependentLocalization.exit V hfinite jump rateX boundX initialX n p)
    (hexhaustY : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < TimeDependentLocalization.exit V hfinite jump rateY boundY initialY n p)
    (ρ : E → E → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y) (T : ℝ≥0) :
    (∫⁻ p, ENNReal.ofReal (ρ
      (TimeDependentGlobalProcess.process V hfinite jump rateX boundX initialX e p T)
      (TimeDependentGlobalProcess.process V hfinite jump rateY boundY initialY e p T)) ∂law μ J) ≤
    (∫⁻ p, ENNReal.ofReal (ρ (initialX p.1) (initialY p.1)) ∂law μ J) +
      ∫⁻ t in Ioc 0 T, ∫⁻ p, ∑ j : J, ENNReal.ofReal
        (currentActivity V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j (p,t))
        ∂law μ J ∂positiveVolume := by
  have hpath := SynchronousGlobalCounting.ae_ofReal_distance_le_lintegral
    V hfinite jump rateX boundX rateY boundY initialX initialY e μ ρ hρ hexhaustX hexhaustY
  have hinit : Measurable (fun p : Sample A J =>
      ENNReal.ofReal (ρ (initialX p.1) (initialY p.1))) :=
    ((measurable_of_countable (fun z : E × E => ρ z.1 z.2)).comp
      ((hinitX.comp measurable_fst).prodMk (hinitY.comp measurable_fst))).ennreal_ofReal
  calc
    _ ≤ ∫⁻ p, ENNReal.ofReal (ρ (initialX p.1) (initialY p.1)) +
        ∑ j : J, ∫⁻ q, ENNReal.ofReal
          (positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j T (p,q))
          ∂MarkedNoise.countingMeasure j p.2 ∂law μ J :=
      lintegral_mono_ae (hpath.mono (fun _ hp => hp T))
    _ = _ := by
      rw [lintegral_add_left hinit,
        expected_sum_positiveField_eq_timeActivity V hfinite jump rateX boundX rateY boundY
          initialX initialY e hRateX hRateY hinitX hinitY μ hqX hqY hexhaustX hexhaustY ρ T]

end CarryingCapacity.SynchronousCompensation
