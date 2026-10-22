import CarryingCapacity.SynchronousRunningSupremum
import CarryingCapacity.PredictableExitMask

/-!
# Compensation through the genuine joint exit of synchronous global paths

The two actual constructed paths are observed as a pair. Their strict-past
rational survival is raw predictable and agrees with survival through the
actual exit, including its jump, on one full sample event. Consequently the
masked positive-jump counting integrals have their exact height/time activity
formula. Expectations may be infinite; no coupling estimate or finite expected
activity is assumed. The genuine localization exhaustions remain explicit in
this generic module and are discharged by model-specific constructions.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal

namespace CarryingCapacity.SynchronousStoppedCompensation
open CommonInitialNoise MarkedIntensity PredictableSets
open SynchronousGlobalCounting SynchronousCompensation
open CommonFrozenExit PredictableExitMask
open LyapunovLocalization (active)

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

/-- A single deterministic endpoint is null for time intensity. The strict
and inclusive exit masks therefore give exactly the same time integral. This
holds for every fixed sample's exit value, including zero and infinity. -/
theorem lintegral_inclusive_eq_strict (σ : ℝ≥0∞) (T : ℝ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioc 0 T, (if 0 < t ∧ ENNReal.ofReal t ≤ σ then f t else 0) ∂positiveVolume) =
      ∫⁻ t in Ioc 0 T, (if ENNReal.ofReal t < σ then f t else 0) ∂positiveVolume := by
  letI : NoAtoms positiveVolume := by unfold positiveVolume; infer_instance
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae ((Set.countable_singleton σ.toReal).ae_not_mem positiveVolume)] with t ht hne
  have hne' : ENNReal.ofReal t ≠ σ := by
    intro he
    apply hne
    change t = σ.toReal
    rw [← he, ENNReal.toReal_ofReal ht.1.le]
  have he : ENNReal.ofReal t ≤ σ ↔ ENNReal.ofReal t < σ :=
    ⟨fun h => lt_of_le_of_ne h hne', le_of_lt⟩
  simp only [ht.1, true_and, he]

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

/-- The actual jointly observed state on the original common noise space. -/
def pairPath (t : ℝ) (p : Sample A J) : E × E :=
  (TimeDependentGlobalProcess.process V hfinite jump rateX boundX initialX e p t,
   TimeDependentGlobalProcess.process V hfinite jump rateY boundY initialY e p t)

/-- The genuine exit infimum of the actual pair, possibly infinite. -/
def jointExit (G : Set (E × E)) (p : Sample A J) : ℝ≥0∞ :=
  exitTime G (fun t => pairPath V hfinite jump rateX boundX rateY boundY initialX initialY e t p)

/-- Positive increments through and including the genuine joint exit jump. -/
def stoppedField (G : Set (E × E)) (ρ : E → E → ℝ) (j : J) (T : ℝ) :
    Sample A J × (ℝ × ℝ) → ℝ≥0∞ :=
  exitMask (pairPath V hfinite jump rateX boundX rateY boundY initialX initialY e) G
    (fun p => ENNReal.ofReal
      (positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j T p))

/-- Current-state activity while the inclusive exit mask is on. -/
def stoppedActivity (G : Set (E × E)) (ρ : E → E → ℝ) (j : J)
    (p : Sample A J × ℝ) : ℝ≥0∞ :=
  if 0 < p.2 ∧ ENNReal.ofReal p.2 ≤
      jointExit V hfinite jump rateX boundX rateY boundY initialX initialY e G p.1
  then ENNReal.ofReal
    (currentActivity V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j p)
  else 0

variable (hRateX : ∀ j x, Measurable (fun t => rateX j t x))
  (hRateY : ∀ j x, Measurable (fun t => rateY j t x))
  (hinitX : Measurable initialX) (hinitY : Measurable initialY)
include hRateX hRateY hinitX hinitY

/-- The pair is adapted to the actual raw common history. -/
theorem measurable_pairPath_at (t : ℝ) :
    Measurable[filtration A J t]
      (pairPath V hfinite jump rateX boundX rateY boundY initialX initialY e t) :=
  (TimeDependentGlobalProcess.measurable_process_at V hfinite jump rateX boundX initialX e
    hRateX hinitX t).prodMk
  (TimeDependentGlobalProcess.measurable_process_at V hfinite jump rateY boundY initialY e
    hRateY hinitY t)

variable (μ : Measure A)
  (hexhaustX : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
    (T : ℝ≥0∞) < TimeDependentLocalization.exit V hfinite jump rateX boundX initialX n p)
  (hexhaustY : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
    (T : ℝ≥0∞) < TimeDependentLocalization.exit V hfinite jump rateY boundY initialY n p)

include hexhaustX hexhaustY

omit hRateX hRateY hinitX hinitY [Countable E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [BorelSpace E] in
/-- Right-local constancy holds for the pair on one common sample event. -/
theorem ae_pairPath_right_constant : ∀ᵐ p ∂law μ J, ∀ t : ℝ, 0 ≤ t →
    ∃ b, t < b ∧ ∀ s ∈ Ico t b,
      pairPath V hfinite jump rateX boundX rateY boundY initialX initialY e s p =
        pairPath V hfinite jump rateX boundX rateY boundY initialX initialY e t p := by
  filter_upwards [SynchronousRunningSupremum.ae_right_constant
    V hfinite jump rateX boundX initialX e μ hexhaustX,
    SynchronousRunningSupremum.ae_right_constant
    V hfinite jump rateY boundY initialY e μ hexhaustY] with p hX hY
  intro t ht
  obtain ⟨bX, hbX, hcX⟩ := hX t ht
  obtain ⟨bY, hbY, hcY⟩ := hY t ht
  refine ⟨min bX bY, lt_min hbX hbY, ?_⟩
  intro s hs
  exact Prod.ext (hcX s ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩)
    (hcY s ⟨hs.1, hs.2.trans_le (min_le_right _ _)⟩)

/-- The actual stopped counting integral has an AE measurable version. -/
theorem aemeasurable_stoppedCountingIntegral (G : Set (E × E))
    (ρ : E → E → ℝ) (j : J) (T : ℝ) :
    AEMeasurable (fun p => ∫⁻ z,
      stoppedField V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j T (p,z)
      ∂MarkedNoise.countingMeasure j p.2) (law μ J) :=
  PredictableExitMask.aemeasurable_exitCountingIntegral μ _
    (fun t _ => measurable_pairPath_at V hfinite jump rateX boundX rateY boundY initialX initialY e
      hRateX hRateY hinitX hinitY t) G (Set.to_countable G).measurableSet
    (ae_pairPath_right_constant V hfinite jump rateX boundX rateY boundY initialX initialY e
      μ hexhaustX hexhaustY) _
    (measurable_positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e
      hRateX hRateY hinitX hinitY ρ j T).ennreal_ofReal j

/-- Nonnegative compensation for the actual inclusive joint-exit field. -/
theorem compensation_stoppedField [IsProbabilityMeasure μ] (G : Set (E × E))
    (ρ : E → E → ℝ) (j : J) (T : ℝ) :
    (∫⁻ p, ∫⁻ z,
      stoppedField V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j T (p,z)
      ∂MarkedNoise.countingMeasure j p.2 ∂law μ J) =
    ∫⁻ p, ∫⁻ z,
      stoppedField V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j T (p,z)
      ∂positiveVolume.prod positiveVolume ∂law μ J :=
  PredictableExitMask.compensation_exitMask_nonnegative μ _
    (fun t _ => measurable_pairPath_at V hfinite jump rateX boundX rateY boundY initialX initialY e
      hRateX hRateY hinitX hinitY t) G (Set.to_countable G).measurableSet
    (ae_pairPath_right_constant V hfinite jump rateX boundX rateY boundY initialX initialY e
      μ hexhaustX hexhaustY) _
    (measurable_positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e
      hRateX hRateY hinitX hinitY ρ j T).ennreal_ofReal j

omit μ hexhaustX hexhaustY in
/-- For each fixed sample, ordinary height integration yields the masked
pre-jump activity, without any random-exit measurability assumption. -/
theorem intensityIntegral_eq_stoppedPreActivity
    (hqX : ∀ j t x, 0 ≤ rateX j t x) (hqY : ∀ j t x, 0 ≤ rateY j t x)
    (G : Set (E × E)) (ρ : E → E → ℝ) (j : J) (T : ℝ) (p : Sample A J) :
    (∫⁻ z, stoppedField V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j T (p,z)
      ∂positiveVolume.prod positiveVolume) =
    ∫⁻ t in Ioc 0 T,
      (if 0 < t ∧ ENNReal.ofReal t ≤
          jointExit V hfinite jump rateX boundX rateY boundY initialX initialY e G p
       then ENNReal.ofReal
         (preActivity V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j (p,t))
       else 0) ∂positiveVolume := by
  have hm := ((measurable_positiveField V hfinite jump rateX boundX rateY boundY
    initialX initialY e hRateX hRateY hinitX hinitY ρ j T).mono
      (predictable_le _) le_rfl).ennreal_ofReal
  have hz : MeasurableSet {z : ℝ × ℝ | 0 < z.1 ∧ ENNReal.ofReal z.1 ≤
      jointExit V hfinite jump rateX boundX rateY boundY initialX initialY e G p} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst.ennreal_ofReal measurable_const)
  have hm' : Measurable (fun z : ℝ × ℝ =>
      stoppedField V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j T (p,z)) := by
    exact (hm.comp (measurable_const.prodMk measurable_id)).ite hz measurable_const
  rw [lintegral_prod _ hm'.aemeasurable, ← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ Ioc 0 T
  · by_cases hs : 0 < t ∧ ENNReal.ofReal t ≤
        jointExit V hfinite jump rateX boundX rateY boundY initialX initialY e G p
    · simp only [stoppedField, exitMask, jointExit] at hs ⊢
      simp only [hs, if_pos, positiveField_apply, ht, if_true, Set.indicator_of_mem ht]
      exact SynchronousPositiveIncrement.lintegral_positiveIncrement ρ jump j _ _ _ _ (hqX j t _) (hqY j t _)
    · simp only [stoppedField, exitMask, jointExit] at hs ⊢
      simp [hs, ht]
  · simp only [stoppedField, exitMask, positiveField_apply, ht, if_false, ENNReal.ofReal_zero]
    simp [ht]

/-- Pre-jump states can be replaced by current states under the time integral,
even with the actual random inclusive-exit mask. -/
theorem expected_stoppedField_eq_sampleTimeActivity [IsProbabilityMeasure μ]
    (hqX : ∀ j t x, 0 ≤ rateX j t x) (hqY : ∀ j t x, 0 ≤ rateY j t x)
    (G : Set (E × E)) (ρ : E → E → ℝ) (j : J) (T : ℝ) :
    (∫⁻ p, ∫⁻ z,
      stoppedField V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j T (p,z)
      ∂MarkedNoise.countingMeasure j p.2 ∂law μ J) =
    ∫⁻ p, ∫⁻ t in Ioc 0 T,
      stoppedActivity V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j (p,t)
      ∂positiveVolume ∂law μ J := by
  rw [compensation_stoppedField V hfinite jump rateX boundX rateY boundY initialX initialY e
    hRateX hRateY hinitX hinitY μ hexhaustX hexhaustY G ρ j T]
  simp_rw [intensityIntegral_eq_stoppedPreActivity V hfinite jump rateX boundX rateY boundY
    initialX initialY e hRateX hRateY hinitX hinitY hqX hqY G ρ j T]
  apply lintegral_congr_ae
  filter_upwards [ae_preActivity_eq_currentActivity V hfinite jump rateX boundX rateY boundY
    initialX initialY e μ hexhaustX hexhaustY] with p hp
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hp] with t ht
  simp only [stoppedActivity, ht ρ j]

/-- Raw measurable strict-past version of the masked current activity. -/
def rationalActivity (G : Set (E × E)) (ρ : E → E → ℝ) (j : J)
    (p : Sample A J × ℝ) : ℝ≥0∞ :=
  if (p.1, (p.2, 0)) ∈ survivalSet
      (pairPath V hfinite jump rateX boundX rateY boundY initialX initialY e) G
  then ENNReal.ofReal
    (currentActivity V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j p)
  else 0

omit μ hexhaustX hexhaustY in
theorem measurable_rationalActivity (G : Set (E × E)) (ρ : E → E → ℝ) (j : J) :
    Measurable (rationalActivity V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j) := by
  have hs := (predictable_le (filtration A J)) _ (PredictableExitMask.measurableSet_survivalSet (filtration A J) _
    (fun t _ => measurable_pairPath_at V hfinite jump rateX boundX rateY boundY initialX initialY e
      hRateX hRateY hinitX hinitY t) G (Set.to_countable G).measurableSet)
  have hp : Measurable (fun p : Sample A J × ℝ => (p.1, (p.2, (0 : ℝ)))) :=
    measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  exact (measurable_currentActivity V hfinite jump rateX boundX rateY boundY initialX initialY e
    hRateX hRateY hinitX hinitY ρ j).ennreal_ofReal.ite (hs.preimage hp) measurable_const

omit hRateX hRateY hinitX hinitY [Countable E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [BorelSpace E] in
/-- The current-activity masks agree at every time on one full sample event. -/
theorem ae_rationalActivity_eq_stoppedActivity (G : Set (E × E)) (ρ : E → E → ℝ) (j : J) :
    ∀ᵐ p ∂law μ J, ∀ t : ℝ,
      rationalActivity V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j (p,t) =
        stoppedActivity V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j (p,t) := by
  filter_upwards [ae_pairPath_right_constant V hfinite jump rateX boundX rateY boundY initialX initialY e
    μ hexhaustX hexhaustY] with p hp
  intro t
  exact rationalMask_eq_exitMask _ G
    (fun r => ENNReal.ofReal
      (currentActivity V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j (r.1,r.2.1)))
    p hp (t,0)

/-- Joint AE measurability is derived from the single common regularity event,
for any time measure. -/
theorem aemeasurable_stoppedActivity (τ : Measure ℝ)
    (G : Set (E × E)) (ρ : E → E → ℝ) (j : J) :
    AEMeasurable (stoppedActivity V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j)
      ((law μ J).prod τ) := by
  apply (measurable_rationalActivity V hfinite jump rateX boundX rateY boundY initialX initialY e
    hRateX hRateY hinitX hinitY G ρ j).aemeasurable.congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
    (ae_rationalActivity_eq_stoppedActivity V hfinite jump rateX boundX rateY boundY initialX initialY e
      μ hexhaustX hexhaustY G ρ j)] with p hp
  exact hp p.2

/-- Every fixed-time masked activity is AE measurable under the original law. -/
theorem aemeasurable_stoppedActivity_at (G : Set (E × E)) (ρ : E → E → ℝ) (j : J) (t : ℝ) :
    AEMeasurable (fun p => stoppedActivity V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j (p,t))
      (law μ J) :=
  ((measurable_rationalActivity V hfinite jump rateX boundX rateY boundY initialX initialY e
    hRateX hRateY hinitX hinitY G ρ j).comp (measurable_id.prodMk measurable_const)).aemeasurable.congr
    ((ae_rationalActivity_eq_stoppedActivity V hfinite jump rateX boundX rateY boundY initialX initialY e
      μ hexhaustX hexhaustY G ρ j).mono (fun _ hp => hp t))

/-- Genuine inclusive-exit compensation in time-then-sample order, with
pre-jump states replaced by actual current states. -/
theorem expected_stoppedField_eq_timeActivity [IsProbabilityMeasure μ]
    (hqX : ∀ j t x, 0 ≤ rateX j t x) (hqY : ∀ j t x, 0 ≤ rateY j t x)
    (G : Set (E × E)) (ρ : E → E → ℝ) (j : J) (T : ℝ) :
    (∫⁻ p, ∫⁻ z,
      stoppedField V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j T (p,z)
      ∂MarkedNoise.countingMeasure j p.2 ∂law μ J) =
    ∫⁻ t in Ioc 0 T, ∫⁻ p,
      stoppedActivity V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j (p,t)
      ∂law μ J ∂positiveVolume := by
  rw [expected_stoppedField_eq_sampleTimeActivity V hfinite jump rateX boundX rateY boundY
    initialX initialY e hRateX hRateY hinitX hinitY μ hexhaustX hexhaustY hqX hqY G ρ j T]
  exact lintegral_lintegral_swap (aemeasurable_stoppedActivity V hfinite jump rateX boundX rateY boundY
    initialX initialY e hRateX hRateY hinitX hinitY μ hexhaustX hexhaustY
    (positiveVolume.restrict (Ioc 0 T)) G ρ j)

/-- The actual sum over driving labels equals the expected summed height
activity through the true joint exit, including its endpoint. -/
theorem expected_sum_stoppedField_eq_timeActivity [IsProbabilityMeasure μ]
    (hqX : ∀ j t x, 0 ≤ rateX j t x) (hqY : ∀ j t x, 0 ≤ rateY j t x)
    (G : Set (E × E)) (ρ : E → E → ℝ) (T : ℝ) :
    (∫⁻ p, ∑ j : J, ∫⁻ z,
      stoppedField V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j T (p,z)
      ∂MarkedNoise.countingMeasure j p.2 ∂law μ J) =
    ∫⁻ t in Ioc 0 T, ∫⁻ p, ∑ j : J,
      stoppedActivity V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j (p,t)
      ∂law μ J ∂positiveVolume := by
  rw [lintegral_finset_sum' Finset.univ (fun j _ =>
    aemeasurable_stoppedCountingIntegral V hfinite jump rateX boundX rateY boundY initialX initialY e
      hRateX hRateY hinitX hinitY μ hexhaustX hexhaustY G ρ j T)]
  simp_rw [expected_stoppedField_eq_timeActivity V hfinite jump rateX boundX rateY boundY
    initialX initialY e hRateX hRateY hinitX hinitY μ hexhaustX hexhaustY hqX hqY G ρ]
  rw [← lintegral_finset_sum' Finset.univ (fun j _ =>
    (aemeasurable_stoppedActivity V hfinite jump rateX boundX rateY boundY initialX initialY e
      hRateX hRateY hinitX hinitY μ hexhaustX hexhaustY
      (positiveVolume.restrict (Ioc 0 T)) G ρ j).lintegral_prod_left')]
  apply lintegral_congr
  intro t
  exact (lintegral_finset_sum' Finset.univ (fun j _ =>
    aemeasurable_stoppedActivity_at V hfinite jump rateX boundX rateY boundY initialX initialY e
      hRateX hRateY hinitX hinitY μ hexhaustX hexhaustY G ρ j t)).symm

/-- The paper's strict-exit convention is recovered under the time integral.
The counting side continues to include the exit jump. -/
theorem expected_stoppedField_eq_sampleTimeStrictActivity [IsProbabilityMeasure μ]
    (hqX : ∀ j t x, 0 ≤ rateX j t x) (hqY : ∀ j t x, 0 ≤ rateY j t x)
    (G : Set (E × E)) (ρ : E → E → ℝ) (j : J) (T : ℝ) :
    (∫⁻ p, ∫⁻ z,
      stoppedField V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j T (p,z)
      ∂MarkedNoise.countingMeasure j p.2 ∂law μ J) =
    ∫⁻ p, ∫⁻ t in Ioc 0 T,
      (if ENNReal.ofReal t < jointExit V hfinite jump rateX boundX rateY boundY initialX initialY e G p
       then ENNReal.ofReal
         (currentActivity V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j (p,t))
       else 0) ∂positiveVolume ∂law μ J := by
  rw [expected_stoppedField_eq_sampleTimeActivity V hfinite jump rateX boundX rateY boundY
    initialX initialY e hRateX hRateY hinitX hinitY μ hexhaustX hexhaustY hqX hqY G ρ j T]
  apply lintegral_congr
  intro p
  exact lintegral_inclusive_eq_strict
    (jointExit V hfinite jump rateX boundX rateY boundY initialX initialY e G p) T
    (fun t => ENNReal.ofReal
      (currentActivity V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j (p,t)))

end CarryingCapacity.SynchronousStoppedCompensation
