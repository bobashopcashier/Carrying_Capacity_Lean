import CarryingCapacity.SynchronousCompensation

/-!
# The actual running supremum of a synchronous coupling

A supremum over all times is identified almost surely with observations at
rational times and the terminal time. The identification uses the actual
paths' right-local constancy, derived from their finite frozen recursions and
genuine exit exhaustion. Thus arbitrary measurable costs on a countable state
space are allowed. Nonnegative predictable compensation then controls the
expectation of the actual running supremum, with no finiteness assumption.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal

namespace CarryingCapacity.SynchronousRunningSupremum
open CommonInitialNoise TimeDependentLocalization TimeDependentGlobalCounting
open SynchronousGlobalCounting SynchronousCompensation MarkedIntensity
open LyapunovLocalization (active)

/-- Supremum over every real time in the closed horizon. -/
def intervalSup (f : ℝ → ℝ≥0∞) (T : ℝ) : ℝ≥0∞ :=
  ⨆ t : Icc (0 : ℝ) T, f t

/-- A countable set of observations, including the possibly irrational endpoint. -/
def observedSup (f : ℝ → ℝ≥0∞) (T : ℝ) : ℝ≥0∞ :=
  f T ⊔ ⨆ q : ℚ, if (q : ℝ) ∈ Icc (0 : ℝ) T then f q else 0

/-- Right-local constancy identifies the uncountable supremum exactly with
rational observations and the terminal value. No continuity of a cost map is needed. -/
theorem intervalSup_eq_observedSup (f : ℝ → ℝ≥0∞) (T : ℝ) (hT : 0 ≤ T)
    (hf : ∀ t ∈ Ico (0 : ℝ) T, ∃ b, t < b ∧ ∀ u ∈ Ico t b, f u = f t) :
    intervalSup f T = observedSup f T := by
  apply le_antisymm
  · apply iSup_le
    intro t
    by_cases ht : (t : ℝ) = T
    · change f t ≤ f T ⊔ _
      rw [ht]
      exact le_sup_left
    · have htT : (t : ℝ) < T := lt_of_le_of_ne t.property.2 ht
      obtain ⟨b, hb, hlocal⟩ := hf t ⟨t.property.1, htT⟩
      obtain ⟨q, hq, hqb⟩ := exists_rat_btwn (lt_min hb htT)
      have hqI : (q : ℝ) ∈ Icc (0 : ℝ) T :=
        ⟨t.property.1.trans hq.le, (lt_min_iff.mp hqb).2.le⟩
      have hval := hlocal q ⟨hq.le, (lt_min_iff.mp hqb).1⟩
      change f t ≤ f T ⊔ _
      apply le_sup_of_le_right
      apply le_iSup_of_le q
      simpa only [if_pos hqI] using hval.symm.le
  · apply sup_le
    · exact le_iSup_of_le ⟨T, hT, le_rfl⟩ le_rfl
    · apply iSup_le
      intro q
      by_cases hq : (q : ℝ) ∈ Icc (0 : ℝ) T
      · simpa only [if_pos hq] using
          (le_iSup_of_le (⟨(q : ℝ), hq⟩ : Icc (0 : ℝ) T) (le_refl (f q)))
      · simp only [if_neg hq, zero_le]

variable {A E J : Type*} [DecidableEq E] [Fintype J]
  [TopologicalSpace E] [PolishSpace E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rateX : J → ℝ → E → ℝ)
  (boundX : ∀ n : ℕ, ∃ C : ℝ,
    ∀ x ∈ active V hfinite n, ∀ j t, rateX j t x ≤ C)
  (rateY : J → ℝ → E → ℝ)
  (boundY : ∀ n : ℕ, ∃ C : ℝ,
    ∀ x ∈ active V hfinite n, ∀ j t, rateY j t x ≤ C)
  (initialX initialY : A → E) (e : E)

/-- The extended running cost of the two actual global paths. -/
def runningCost (ρ : E → E → ℝ) (T : ℝ) (p : Sample A J) : ℝ≥0∞ :=
  intervalSup (fun t => ENNReal.ofReal (ρ
    (TimeDependentGlobalProcess.process V hfinite jump rateX boundX initialX e p t)
    (TimeDependentGlobalProcess.process V hfinite jump rateY boundY initialY e p t))) T

/-- A countable measurable version, later identified with the actual running cost. -/
def observedCost (ρ : E → E → ℝ) (T : ℝ) (p : Sample A J) : ℝ≥0∞ :=
  observedSup (fun t => ENNReal.ofReal (ρ
    (TimeDependentGlobalProcess.process V hfinite jump rateX boundX initialX e p t)
    (TimeDependentGlobalProcess.process V hfinite jump rateY boundY initialY e p t))) T

section OnePath
omit rateY boundY initialY
variable [MeasurableSpace A] (μ : Measure A)

/-- The global constructed path is locally constant from the right at every
nonnegative time, on one event. This is inherited from actual frozen paths. -/
theorem ae_right_constant
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rateX boundX initialX n p) :
    ∀ᵐ p ∂law μ J, ∀ t : ℝ, 0 ≤ t → ∃ b, t < b ∧ ∀ u ∈ Ico t b,
      TimeDependentGlobalProcess.process V hfinite jump rateX boundX initialX e p u =
      TimeDependentGlobalProcess.process V hfinite jump rateX boundX initialX e p t := by
  have hf := ae_all_iff.mpr (fun n : ℕ => ae_noise μ
    (TimeDependentFrozenProcess.ae_process_right_constant (active V hfinite n) jump rateX))
  filter_upwards [TimeDependentGlobalProcess.ae_agrees_on_horizon
    V hfinite jump rateX boundX initialX e μ hexhaust, hf] with p hp hlocal
  intro t ht
  let T : ℝ≥0 := ⟨t + 1, by linarith⟩
  obtain ⟨n, hn⟩ := hp T
  obtain ⟨b, hb, hconst⟩ := hlocal n (rateBound V hfinite rateX boundX n) (initialX p.1) t
  refine ⟨min b (t+1), lt_min hb (by linarith), ?_⟩
  intro u hu
  have hut : u ≤ T := (hu.2.trans_le (min_le_right _ _)).le
  have htT : t ≤ T := by dsimp [T]; linarith
  exact (hn n le_rfl u (ht.trans hu.1) hut).trans
    ((hconst u ⟨hu.1, hu.2.trans_le (min_le_left _ _)⟩).trans
      (hn n le_rfl t ht htT).symm)

end OnePath

variable [MeasurableSpace A] (μ : Measure A)

/-- The actual running cost and its countable observation version agree
simultaneously for all nonnegative horizons, for every cost function. -/
theorem ae_runningCost_eq_observedCost
    (hexhaustX : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rateX boundX initialX n p)
    (hexhaustY : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rateY boundY initialY n p) :
    ∀ᵐ p ∂law μ J, ∀ (ρ : E → E → ℝ) (T : ℝ≥0),
      runningCost V hfinite jump rateX boundX rateY boundY initialX initialY e ρ T p =
        observedCost V hfinite jump rateX boundX rateY boundY initialX initialY e ρ T p := by
  filter_upwards [ae_right_constant V hfinite jump rateX boundX initialX e μ hexhaustX,
    ae_right_constant V hfinite jump rateY boundY initialY e μ hexhaustY] with p hX hY
  intro ρ T
  apply intervalSup_eq_observedSup _ T T.coe_nonneg
  intro t ht
  obtain ⟨bX, hbX, hcX⟩ := hX t ht.1
  obtain ⟨bY, hbY, hcY⟩ := hY t ht.1
  refine ⟨min bX bY, lt_min hbX hbY, ?_⟩
  intro u hu
  rw [hcX u ⟨hu.1, hu.2.trans_le (min_le_left _ _)⟩,
    hcY u ⟨hu.1, hu.2.trans_le (min_le_right _ _)⟩]

section Measurability
variable [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E]
  (hRateX : ∀ j x, Measurable (fun t => rateX j t x))
  (hRateY : ∀ j x, Measurable (fun t => rateY j t x))
  (hinitX : Measurable initialX) (hinitY : Measurable initialY)
include hRateX hRateY hinitX hinitY
omit μ

/-- The rational-plus-terminal observation version is measurable on every sample. -/
theorem measurable_observedCost (ρ : E → E → ℝ) (T : ℝ) :
    Measurable (observedCost V hfinite jump rateX boundX rateY boundY initialX initialY e ρ T) := by
  have hm (t : ℝ) : Measurable (fun p : Sample A J => ENNReal.ofReal (ρ
      (TimeDependentGlobalProcess.process V hfinite jump rateX boundX initialX e p t)
      (TimeDependentGlobalProcess.process V hfinite jump rateY boundY initialY e p t))) := by
    have hX := (TimeDependentGlobalProcess.measurable_process V hfinite jump rateX boundX
      initialX e hRateX hinitX).comp (measurable_id.prodMk (measurable_const (a := t)))
    have hY := (TimeDependentGlobalProcess.measurable_process V hfinite jump rateY boundY
      initialY e hRateY hinitY).comp (measurable_id.prodMk (measurable_const (a := t)))
    exact ((measurable_of_countable (fun z : E × E => ρ z.1 z.2)).comp (hX.prodMk hY)).ennreal_ofReal
  apply (hm T).sup
  apply Measurable.iSup
  intro q
  by_cases hq : (q : ℝ) ∈ Icc (0 : ℝ) T
  · simpa only [if_pos hq] using hm q
  · simp only [if_neg hq]
    exact measurable_const

include μ in
/-- The actual supremum is AE measurable under the original product law,
without replacing its exceptional samples or assuming supremum measurability. -/
theorem aemeasurable_runningCost
    (hexhaustX : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rateX boundX initialX n p)
    (hexhaustY : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rateY boundY initialY n p)
    (ρ : E → E → ℝ) (T : ℝ≥0) :
    AEMeasurable (runningCost V hfinite jump rateX boundX rateY boundY initialX initialY e ρ T)
      (law μ J) :=
  (measurable_observedCost V hfinite jump rateX boundX rateY boundY initialX initialY e
    hRateX hRateY hinitX hinitY ρ T).aemeasurable.congr
      ((ae_runningCost_eq_observedCost V hfinite jump rateX boundX rateY boundY initialX initialY e
        μ hexhaustX hexhaustY).mono (fun _ hp => (hp ρ T).symm))

end Measurability

/-- The actual uncountable running supremum satisfies the positive-increment
bound, with no assumed finiteness or measurability of that supremum. -/
theorem ae_runningCost_le_lintegral (ρ : E → E → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y)
    (hexhaustX : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rateX boundX initialX n p)
    (hexhaustY : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rateY boundY initialY n p) :
    ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0,
      runningCost V hfinite jump rateX boundX rateY boundY initialX initialY e ρ T p ≤
        ENNReal.ofReal (ρ (initialX p.1) (initialY p.1)) +
          ∑ j : J, ∫⁻ q, ENNReal.ofReal
            (positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j T (p,q))
            ∂MarkedNoise.countingMeasure j p.2 := by
  filter_upwards [ae_ofReal_distance_le_lintegral_horizon V hfinite jump rateX boundX rateY boundY
    initialX initialY e μ ρ hρ hexhaustX hexhaustY] with p hp
  intro T
  apply iSup_le
  intro t
  exact hp T ⟨t, t.property.1⟩ t.property.2

section Expectation
variable [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E]
  (hRateX : ∀ j x, Measurable (fun t => rateX j t x))
  (hRateY : ∀ j x, Measurable (fun t => rateY j t x))
  (hinitX : Measurable initialX) (hinitY : Measurable initialY)

include hRateX hRateY hinitX hinitY

/-- The paper's expected running-distance bound for the actual synchronous
paths. Compensation is proved, and infinite expectations are allowed. -/
theorem expected_runningCost_le_activity [IsProbabilityMeasure μ]
    (hqX : ∀ j t x, 0 ≤ rateX j t x) (hqY : ∀ j t x, 0 ≤ rateY j t x)
    (hexhaustX : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rateX boundX initialX n p)
    (hexhaustY : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rateY boundY initialY n p)
    (ρ : E → E → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y) (T : ℝ≥0) :
    (∫⁻ p, runningCost V hfinite jump rateX boundX rateY boundY initialX initialY e ρ T p ∂law μ J) ≤
      (∫⁻ p, ENNReal.ofReal (ρ (initialX p.1) (initialY p.1)) ∂law μ J) +
        ∫⁻ t in Ioc 0 T, ∫⁻ p, ∑ j : J, ENNReal.ofReal
          (currentActivity V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j (p,t))
          ∂law μ J ∂positiveVolume := by
  have hpath := ae_runningCost_le_lintegral V hfinite jump rateX boundX rateY boundY
    initialX initialY e μ ρ hρ hexhaustX hexhaustY
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

end Expectation
end CarryingCapacity.SynchronousRunningSupremum
