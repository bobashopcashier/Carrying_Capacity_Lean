import CarryingCapacity.SynchronousStoppedCompensation
import CarryingCapacity.StoppedPathMeasurability

/-!
# Running supremum through an actual joint exit

The cost is the supremum of the genuinely stopped pair on the whole real
time interval. It equals the original running supremum at the cut horizon.
Pathwise positive-increment domination is applied on one full sample event
at that random horizon. Inclusive-exit compensation then gives the expected
stopped running-cost inequality without assuming its finiteness.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal

namespace CarryingCapacity.SynchronousStoppedRunningSupremum
open CommonInitialNoise CommonFrozenExit SynchronousGlobalCounting
open SynchronousRunningSupremum SynchronousStoppedCompensation PredictableExitMask
open MarkedIntensity
open LyapunovLocalization (active)

/-- The actual nonnegative horizon after stopping at an extended time. -/
def cutHorizon (σ : ℝ≥0∞) (T : ℝ≥0) : ℝ≥0 :=
  if σ = ⊤ then T else ⟨min (T : ℝ) σ.toReal, le_min T.coe_nonneg ENNReal.toReal_nonneg⟩

theorem cutHorizon_le (σ : ℝ≥0∞) (T : ℝ≥0) : cutHorizon σ T ≤ T := by
  unfold cutHorizon
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem cutHorizon_le_exit (σ : ℝ≥0∞) (T : ℝ≥0) : (cutHorizon σ T : ℝ≥0∞) ≤ σ := by
  by_cases hσ : σ = ⊤
  · simp [hσ]
  · have h : (cutHorizon σ T : ℝ) ≤ σ.toReal := by
      simp only [cutHorizon, if_neg hσ]
      exact min_le_right _ _
    simpa only [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hσ] using
      ENNReal.ofReal_le_ofReal h

/-- Stopping has no effect up to and including the chosen time. -/
theorem stopped_eq_of_le {F : Type*} (σ : ℝ≥0∞) (f : ℝ → F) (t : ℝ)
    (ht : 0 ≤ t) (hle : ENNReal.ofReal t ≤ σ) : stopped σ f t = f t := by
  by_cases hσ : σ = ⊤
  · simp [CommonFrozenExit.stopped, hσ]
  · have htσ : t ≤ σ.toReal := by
      simpa only [ENNReal.toReal_ofReal ht] using ENNReal.toReal_mono hσ hle
    simp only [CommonFrozenExit.stopped, if_neg hσ, min_eq_left htσ]

/-- Taking the supremum of a stopped path retains its value at the exit. -/
theorem intervalSup_stopped (σ : ℝ≥0∞) (f : ℝ → ℝ≥0∞) (T : ℝ≥0) :
    intervalSup (stopped σ f) T = intervalSup f (cutHorizon σ T) := by
  by_cases hσ : σ = ⊤
  · subst σ
    simp [intervalSup, CommonFrozenExit.stopped, cutHorizon]
  · simp only [intervalSup, stopped, if_neg hσ]
    apply le_antisymm
    · apply iSup_le
      intro t
      have ht : min (t : ℝ) σ.toReal ∈ Icc (0 : ℝ) (cutHorizon σ T) := by
        refine ⟨le_min t.property.1 ENNReal.toReal_nonneg, ?_⟩
        simp only [cutHorizon, if_neg hσ]
        exact min_le_min_right _ t.property.2
      exact le_iSup_of_le ⟨_, ht⟩ le_rfl
    · apply iSup_le
      intro t
      have htT : (t : ℝ) ≤ T := t.property.2.trans (cutHorizon_le σ T)
      have htσ : (t : ℝ) ≤ σ.toReal := by
        have := t.property.2
        simp only [cutHorizon, if_neg hσ] at this
        exact this.trans (min_le_right _ _)
      have h : f (min (t : ℝ) σ.toReal) ≤
          ⨆ u : Icc (0 : ℝ) T, f (min (u : ℝ) σ.toReal) :=
        le_iSup_of_le (⟨t, t.property.1, htT⟩ : Icc (0 : ℝ) T) le_rfl
      simpa only [min_eq_left htσ] using h

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

/-- Supremum over every real time of the actual pair stopped at its joint exit. -/
def stoppedRunningCost (G : Set (E × E)) (ρ : E → E → ℝ) (T : ℝ) (p : Sample A J) : ℝ≥0∞ :=
  intervalSup (stopped
    (jointExit V hfinite jump rateX boundX rateY boundY initialX initialY e G p)
    (fun t => ENNReal.ofReal (ρ
      (TimeDependentGlobalProcess.process V hfinite jump rateX boundX initialX e p t)
      (TimeDependentGlobalProcess.process V hfinite jump rateY boundY initialY e p t)))) T

omit [MeasurableSpace A] [Fintype J] [PolishSpace E] [Countable E]
  [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
theorem stoppedRunningCost_eq_cut (G : Set (E × E)) (ρ : E → E → ℝ)
    (T : ℝ≥0) (p : Sample A J) :
    stoppedRunningCost V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ T p =
      runningCost V hfinite jump rateX boundX rateY boundY initialX initialY e ρ
        (cutHorizon (jointExit V hfinite jump rateX boundX rateY boundY initialX initialY e G p) T) p :=
  intervalSup_stopped _ _ T

omit [MeasurableSpace A] [Fintype J] [PolishSpace E] [Countable E]
  [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
/-- Every current cost before the exit is bounded by the actual stopped
running supremum, including both the exit and horizon endpoints. -/
theorem currentCost_le_stoppedRunningCost (G : Set (E × E)) (ρ : E → E → ℝ)
    (T t : ℝ) (p : Sample A J) (ht : t ∈ Icc 0 T)
    (hbefore : ENNReal.ofReal t ≤
      jointExit V hfinite jump rateX boundX rateY boundY initialX initialY e G p) :
    ENNReal.ofReal (ρ
      (TimeDependentGlobalProcess.process V hfinite jump rateX boundX initialX e p t)
      (TimeDependentGlobalProcess.process V hfinite jump rateY boundY initialY e p t)) ≤
      stoppedRunningCost V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ T p := by
  unfold stoppedRunningCost intervalSup
  apply le_iSup_of_le (⟨t, ht⟩ : Icc (0 : ℝ) T)
  exact (stopped_eq_of_le
    (jointExit V hfinite jump rateX boundX rateY boundY initialX initialY e G p)
    (fun u => ENNReal.ofReal (ρ
      (TimeDependentGlobalProcess.process V hfinite jump rateX boundX initialX e p u)
      (TimeDependentGlobalProcess.process V hfinite jump rateY boundY initialY e p u)))
    t ht.1 hbefore).symm.le

omit [MeasurableSpace A] [Fintype J] [PolishSpace E] [Countable E]
  [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
/-- The finite-horizon increment at the cut horizon is dominated by the
inclusive-exit field at the original horizon, at every time and mark. -/
theorem positiveField_cut_le_stoppedField (G : Set (E × E)) (ρ : E → E → ℝ)
    (j : J) (T : ℝ≥0) (p : Sample A J) (z : ℝ × ℝ) :
    ENNReal.ofReal (positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j
      (cutHorizon (jointExit V hfinite jump rateX boundX rateY boundY initialX initialY e G p) T) (p,z)) ≤
    stoppedField V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j T (p,z) := by
  let σ := jointExit V hfinite jump rateX boundX rateY boundY initialX initialY e G p
  by_cases hz : z.1 ∈ Ioc 0 (cutHorizon σ T : ℝ)
  · have hzT : z.1 ∈ Ioc 0 (T : ℝ) := ⟨hz.1, hz.2.trans (cutHorizon_le σ T)⟩
    have hzσ : ENNReal.ofReal z.1 ≤ σ :=
      (ENNReal.ofReal_le_ofReal hz.2).trans (by
        simpa only [ENNReal.ofReal_coe_nnreal] using cutHorizon_le_exit σ T)
    simp only [stoppedField, exitMask, jointExit, Prod.fst, Prod.snd]
    change ENNReal.ofReal (positiveField V hfinite jump rateX boundX rateY boundY
      initialX initialY e ρ j (cutHorizon σ T) (p,z)) ≤
      if 0 < z.1 ∧ ENNReal.ofReal z.1 ≤ σ then
        ENNReal.ofReal (positiveField V hfinite jump rateX boundX rateY boundY
          initialX initialY e ρ j T (p,z)) else 0
    rw [if_pos ⟨hz.1, hzσ⟩]
    simp only [positiveField, hz, hzT, if_pos]
    exact le_rfl
  · have he : positiveField V hfinite jump rateX boundX rateY boundY
        initialX initialY e ρ j (cutHorizon σ T) (p,z) = 0 := by
      simp [positiveField, hz]
    rw [he, ENNReal.ofReal_zero]
    exact zero_le _

variable (μ : Measure A)
  (hexhaustX : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
    (T : ℝ≥0∞) < TimeDependentLocalization.exit V hfinite jump rateX boundX initialX n p)
  (hexhaustY : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
    (T : ℝ≥0∞) < TimeDependentLocalization.exit V hfinite jump rateY boundY initialY n p)
include hexhaustX hexhaustY

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
/-- One common probability-one event permits evaluation at the genuine random
cut horizon; no separate exceptional set is selected at that time. -/
theorem ae_stoppedRunningCost_le_lintegral (G : Set (E × E))
    (ρ : E → E → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y) :
    ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0,
      stoppedRunningCost V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ T p ≤
        ENNReal.ofReal (ρ (initialX p.1) (initialY p.1)) +
          ∑ j : J, ∫⁻ z,
            stoppedField V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j T (p,z)
            ∂MarkedNoise.countingMeasure j p.2 := by
  filter_upwards [ae_runningCost_le_lintegral V hfinite jump rateX boundX rateY boundY
    initialX initialY e μ ρ hρ hexhaustX hexhaustY] with p hp
  intro T
  rw [stoppedRunningCost_eq_cut]
  apply (hp _).trans
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro j _
  exact lintegral_mono (fun z => positiveField_cut_le_stoppedField
    V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j T p z)

variable (hRateX : ∀ j x, Measurable (fun t => rateX j t x))
  (hRateY : ∀ j x, Measurable (fun t => rateY j t x))
  (hinitX : Measurable initialX) (hinitY : Measurable initialY)
include hRateX hRateY hinitX hinitY

/-- The genuine stopped running cost is AE measurable. Its uncountable
supremum and the true joint exit are handled through actual path regularity. -/
theorem aemeasurable_stoppedRunningCost (G : Set (E × E))
    (ρ : E → E → ℝ) (T : ℝ≥0) :
    AEMeasurable
      (stoppedRunningCost V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ T)
      (law μ J) := by
  have hpair : Measurable (fun p : Sample A J × ℝ =>
      pairPath V hfinite jump rateX boundX rateY boundY initialX initialY e p.2 p.1) :=
    (TimeDependentGlobalProcess.measurable_process V hfinite jump rateX boundX initialX e
      hRateX hinitX).prodMk
    (TimeDependentGlobalProcess.measurable_process V hfinite jump rateY boundY initialY e
      hRateY hinitY)
  have h := StoppedPathMeasurability.aemeasurable_exit_intervalSup
    (fun p t => pairPath V hfinite jump rateX boundX rateY boundY initialX initialY e t p)
    hpair G (Set.to_countable G).measurableSet (law μ J)
    (ae_pairPath_right_constant V hfinite jump rateX boundX rateY boundY initialX initialY e
      μ hexhaustX hexhaustY) (fun z => ENNReal.ofReal (ρ z.1 z.2)) T T.coe_nonneg
  convert h using 1
  funext p
  unfold stoppedRunningCost
  congr 1
  funext t
  simp only [jointExit, CommonFrozenExit.stopped, pairPath]
  split_ifs <;> rfl

/-- The actual stopped running-supremum inequality from compensated positive
increments. The expectations may be infinite at this stage. -/
theorem expected_stoppedRunningCost_le_activity [IsProbabilityMeasure μ]
    (hqX : ∀ j t x, 0 ≤ rateX j t x) (hqY : ∀ j t x, 0 ≤ rateY j t x)
    (G : Set (E × E)) (ρ : E → E → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y) (T : ℝ≥0) :
    (∫⁻ p, stoppedRunningCost V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ T p ∂law μ J) ≤
      (∫⁻ p, ENNReal.ofReal (ρ (initialX p.1) (initialY p.1)) ∂law μ J) +
        ∫⁻ t in Ioc 0 T, ∫⁻ p, ∑ j : J,
          stoppedActivity V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j (p,t)
          ∂law μ J ∂positiveVolume := by
  have hpath := ae_stoppedRunningCost_le_lintegral V hfinite jump rateX boundX rateY boundY
    initialX initialY e μ hexhaustX hexhaustY G ρ hρ
  have hinit : Measurable (fun p : Sample A J =>
      ENNReal.ofReal (ρ (initialX p.1) (initialY p.1))) :=
    ((measurable_of_countable (fun z : E × E => ρ z.1 z.2)).comp
      ((hinitX.comp measurable_fst).prodMk (hinitY.comp measurable_fst))).ennreal_ofReal
  calc
    _ ≤ ∫⁻ p, ENNReal.ofReal (ρ (initialX p.1) (initialY p.1)) +
        ∑ j : J, ∫⁻ z,
          stoppedField V hfinite jump rateX boundX rateY boundY initialX initialY e G ρ j T (p,z)
          ∂MarkedNoise.countingMeasure j p.2 ∂law μ J :=
      lintegral_mono_ae (hpath.mono (fun _ hp => hp T))
    _ = _ := by
      rw [lintegral_add_left hinit,
        expected_sum_stoppedField_eq_timeActivity V hfinite jump rateX boundX rateY boundY
          initialX initialY e hRateX hRateY hinitX hinitY μ hexhaustX hexhaustY hqX hqY G ρ T]

end CarryingCapacity.SynchronousStoppedRunningSupremum
