import CarryingCapacity.TimeDependentNonexplosion
import CarryingCapacity.ExitTimeMeasurability
import CarryingCapacity.DiscreteCausalUniqueness

/-!
# Genuine global Lyapunov crossing bounds

A crossing anywhere on a closed time horizon forces a genuine canonical
localized exit. This is proved from actual agreement before that exit, rather
than from a terminal-time Markov inequality for the global process. The
localized Lyapunov estimate gives a reciprocal bound at every positive real
threshold. A deterministic union inclusion treats sums of two path values.

For discrete states, actual right continuity gives attainment of every finite
exit. The exact global first exit is AE measurable and its probability equals
the real-time crossing probability.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.GlobalLyapunovExit
open CommonInitialNoise LyapunovLocalization TimeDependentLocalization

/-- Some actual value on the closed horizon reaches the threshold. -/
def crossingEvent {Ω E : Type*} (V : E → ℝ) (X : Ω → ℝ → E) (R T : ℝ) : Set Ω :=
  {ω | ∃ t ∈ Icc 0 T, R ≤ V (X ω t)}

/-- A crossing of a sum forces a crossing of one summand at half the threshold. -/
theorem sum_crossing_subset_union {Ω E F : Type*} (V : E → ℝ) (W : F → ℝ)
    (X : Ω → ℝ → E) (Y : Ω → ℝ → F) (R T : ℝ) :
    {ω | ∃ t ∈ Icc 0 T, R ≤ V (X ω t) + W (Y ω t)} ⊆
      crossingEvent V X (R / 2) T ∪ crossingEvent W Y (R / 2) T := by
  rintro ω ⟨t, ht, hsum⟩
  by_cases hx : R / 2 ≤ V (X ω t)
  · exact Or.inl ⟨t, ht, hx⟩
  · exact Or.inr ⟨t, ht, by linarith⟩

/-- The union estimate needs no independence between the coupled paths. -/
theorem measure_sum_crossing_le {Ω E F : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (V : E → ℝ) (W : F → ℝ)
    (X : Ω → ℝ → E) (Y : Ω → ℝ → F) (R T : ℝ) :
    P {ω | ∃ t ∈ Icc 0 T, R ≤ V (X ω t) + W (Y ω t)} ≤
      P (crossingEvent V X (R / 2) T) + P (crossingEvent W Y (R / 2) T) :=
  (measure_mono (sum_crossing_subset_union V W X Y R T)).trans (measure_union_le _ _)

/-- The genuine first exit of a path from a strict Lyapunov sublevel. -/
def firstExit {Ω E : Type*} (V : E → ℝ) (X : Ω → ℝ → E) (R : ℝ) (ω : Ω) : ℝ≥0∞ :=
  CommonFrozenExit.exitTime {x | V x < R} (X ω)

section Global
variable {A E J : Type*} [MeasurableSpace A] [DecidableEq E] [Fintype J]
  [TopologicalSpace E] [PolishSpace E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (hbounded : ∀ n : ℕ, ∃ C : ℝ, ∀ x ∈ active V hfinite n, ∀ j t, rate j t x ≤ C)
  (initial : A → E) (e : E) (μ : Measure A)

/-- On one event, every real-time threshold crossing forces the corresponding
actual canonical exit. No exhaustion or expected-bound premise is needed. -/
theorem ae_crossing_implies_exit : ∀ᵐ p ∂law μ J, ∀ (n : ℕ) (R T : ℝ),
    (n : ℝ) + 1 ≤ R →
    p ∈ crossingEvent V (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e) R T →
    exit V hfinite jump rate hbounded initial n p ≤ ENNReal.ofReal T := by
  filter_upwards [TimeDependentGlobalProcess.ae_eq_path V hfinite jump rate hbounded initial e μ]
    with p hp
  intro n R T hR hcross
  obtain ⟨t, ht, hlevel⟩ := hcross
  by_contra hexit
  have hbefore : ENNReal.ofReal t < exit V hfinite jump rate hbounded initial n p :=
    (ENNReal.ofReal_le_ofReal ht.2).trans_lt (lt_of_not_ge hexit)
  have hm := path_mem_before_exit V hfinite jump rate hbounded initial n p ht.1 hbefore
  rw [mem_active] at hm
  rw [← hp n t ht.1 hbefore.le] at hm
  linarith

/-- The whole-horizon crossing event is controlled by a genuine localized
exit, not by the global state at the terminal time. -/
theorem measure_crossing_le_exit (n : ℕ) (R T : ℝ) (hR : (n : ℝ) + 1 ≤ R) :
    (law μ J) (crossingEvent V
      (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e) R T) ≤
    (law μ J) {p | exit V hfinite jump rate hbounded initial n p ≤ ENNReal.ofReal T} := by
  apply measure_mono_ae
  filter_upwards [ae_crossing_implies_exit V hfinite jump rate hbounded initial e μ] with p hp
  exact hp n R T hR

variable [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E]
  [IsProbabilityMeasure μ]
  (hRate : ∀ j x, Measurable (fun t => rate j t x)) (hinit : Measurable initial)
  (b : ℝ) (hb : 0 ≤ b) (hVnonneg : ∀ x, 0 ≤ V x)
  (hq : ∀ x j t, 0 ≤ t → 0 ≤ rate j t x)
  (hV : Integrable (fun a => V (initial a)) μ)
  (hdrift : ∀ x t, 0 ≤ t → (∑ j, rate j t x * (V (jump j x) - V x)) ≤ b * (1 + V x))
include hRate hinit hb hVnonneg hq hV hdrift

/-- Actual reciprocal global crossing bound at every positive real threshold.
The factor two accommodates the canonical integer levels. All stochastic
bounds are derived from the affine Lyapunov drift and initial integrability. -/
theorem measure_crossing_le (R T : ℝ) (hR : 0 < R) (hT : 0 ≤ T) :
    (law μ J) (crossingEvent V
      (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e) R T) ≤
      ENNReal.ofReal (2 * ((1 + ∫ a, V (initial a) ∂μ) * Real.exp (b * T)) / R) := by
  let K := TimeDependentNonexplosion.exponentialBound V initial μ b T
  have hm : 0 ≤ ∫ a, V (initial a) ∂μ := integral_nonneg (fun a => hVnonneg (initial a))
  have he : 1 ≤ Real.exp (b * T) := Real.one_le_exp_iff.mpr (mul_nonneg hb hT)
  have hgrowth : 1 ≤ (1 + ∫ a, V (initial a) ∂μ) * Real.exp (b * T) := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ _ := mul_le_mul (by linarith) he (by norm_num) (by linarith)
  have hK : 0 ≤ K := by dsimp [K, TimeDependentNonexplosion.exponentialBound]; linarith
  by_cases hlarge : 2 ≤ R
  · let n := Nat.floor (R / 2)
    have hnlow : R / 2 < (n : ℝ) + 1 := Nat.lt_floor_add_one (R / 2)
    have hnupper : (n : ℝ) + 1 ≤ R := by
      have hf : (n : ℝ) ≤ R / 2 := Nat.floor_le (by positivity)
      linarith
    have hnpos : 0 < (n : ℝ) + 1 := by positivity
    have hbound := (measure_crossing_le_exit V hfinite jump rate hbounded initial e μ n R T hnupper).trans
      (TimeDependentNonexplosion.exit_probability_le V hfinite jump rate hbounded initial e μ
        hRate hinit b hb hVnonneg hq hV hdrift n T hT)
    have hcast : ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n : ℝ) + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using (ENNReal.ofReal_natCast (n + 1)).symm
    rw [hcast, ← ENNReal.ofReal_div_of_pos hnpos] at hbound
    apply hbound.trans (ENNReal.ofReal_le_ofReal ?_)
    change K / ((n : ℝ) + 1) ≤ _
    have hfirst : K / ((n : ℝ) + 1) ≤ K / (R / 2) :=
      div_le_div_of_nonneg_left hK (by positivity) hnlow.le
    apply hfirst.trans
    dsimp [K, TimeDependentNonexplosion.exponentialBound]
    apply (div_le_div_iff₀ (by positivity : 0 < R / 2) hR).mpr
    nlinarith
  · have hp := measure_mono (μ := law μ J) (subset_univ
      (crossingEvent V (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e) R T))
    rw [measure_univ] at hp
    apply hp.trans
    apply ENNReal.one_le_ofReal.mpr
    apply (le_div_iff₀ hR).mpr
    linarith


variable [DiscreteTopology E]

/-- Actual right continuity on the discrete state space supplies the local
constancy needed for genuine exit attainment and rational measurability. -/
theorem ae_right_constant : ∀ᵐ p ∂law μ J, ∀ t : ℝ, 0 ≤ t →
    ∃ b, t < b ∧ ∀ s ∈ Ico t b,
      TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p s =
      TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p t := by
  filter_upwards [TimeDependentNonexplosion.ae_global_cadlag V hfinite jump rate hbounded initial e μ
    hRate hinit b hb hVnonneg hq hV hdrift] with p hp
  exact fun t ht => DiscreteCausalUniqueness.exists_right_constant _ t (hp.1 t ht)

/-- The genuine global exit has an attained crossing exactly when it is at
most the given horizon, simultaneously at all thresholds and horizons. -/
theorem ae_firstExit_le_iff_crossing : ∀ᵐ p ∂law μ J, ∀ R T : ℝ, 0 ≤ T →
    (firstExit V (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e) R p ≤
      ENNReal.ofReal T ↔
    p ∈ crossingEvent V (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e) R T) := by
  filter_upwards [ae_right_constant V hfinite jump rate hbounded initial e μ
    hRate hinit b hb hVnonneg hq hV hdrift] with p hp
  intro R T hT
  simpa only [firstExit, crossingEvent, mem_setOf_eq, not_lt] using
    ExitTimeMeasurability.exitTime_le_iff_exists {x | V x < R}
      (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p) hp T hT

/-- AE measurability of the exact all-real-time global exit, without replacing
its exceptional-sample definition by a rational infimum. -/
theorem aemeasurable_firstExit (R : ℝ) :
    AEMeasurable (firstExit V
      (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e) R) (law μ J) := by
  apply ExitTimeMeasurability.aemeasurable_exitTime
    (fun t p => TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p t)
    (fun t _ => (TimeDependentGlobalProcess.measurable_process_at V hfinite jump rate hbounded initial e
      hRate hinit t).mono ((filtration A J).le t) le_rfl)
    {x | V x < R} (measurableSet_lt (measurable_of_countable V) measurable_const)
  exact ae_right_constant V hfinite jump rate hbounded initial e μ
    hRate hinit b hb hVnonneg hq hV hdrift

/-- Reciprocal probability bound for the genuine global first exit. -/
theorem firstExit_probability_le (R T : ℝ) (hR : 0 < R) (hT : 0 ≤ T) :
    (law μ J) {p | firstExit V
      (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e) R p ≤ ENNReal.ofReal T} ≤
    ENNReal.ofReal (2 * ((1 + ∫ a, V (initial a) ∂μ) * Real.exp (b * T)) / R) := by
  have he : {p | firstExit V
      (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e) R p ≤ ENNReal.ofReal T}
      =ᵐ[law μ J] crossingEvent V
        (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e) R T := by
    filter_upwards [ae_firstExit_le_iff_crossing V hfinite jump rate hbounded initial e μ
      hRate hinit b hb hVnonneg hq hV hdrift] with p hp
    exact propext (hp R T hT)
  rw [measure_congr he]
  exact measure_crossing_le V hfinite jump rate hbounded initial e μ
    hRate hinit b hb hVnonneg hq hV hdrift R T hR hT

end Global

section Paired
variable {A E J : Type*} [MeasurableSpace A] [DecidableEq E] [Fintype J]
  [TopologicalSpace E] [PolishSpace E] [Countable E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [BorelSpace E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite) (jump : J → E → E)
  (rateX rateY : J → ℝ → E → ℝ)
  (hboundedX : ∀ n : ℕ, ∃ C : ℝ, ∀ x ∈ active V hfinite n, ∀ j t, rateX j t x ≤ C)
  (hboundedY : ∀ n : ℕ, ∃ C : ℝ, ∀ x ∈ active V hfinite n, ∀ j t, rateY j t x ≤ C)
  (initialX initialY : A → E) (e : E) (μ : Measure A) [IsProbabilityMeasure μ]
  (hRateX : ∀ j x, Measurable (fun t => rateX j t x))
  (hRateY : ∀ j x, Measurable (fun t => rateY j t x))
  (hinitX : Measurable initialX) (hinitY : Measurable initialY)
  (bX bY : ℝ) (hbX : 0 ≤ bX) (hbY : 0 ≤ bY) (hVnonneg : ∀ x, 0 ≤ V x)
  (hqX : ∀ x j t, 0 ≤ t → 0 ≤ rateX j t x)
  (hqY : ∀ x j t, 0 ≤ t → 0 ≤ rateY j t x)
  (hVX : Integrable (fun a => V (initialX a)) μ)
  (hVY : Integrable (fun a => V (initialY a)) μ)
  (hdriftX : ∀ x t, 0 ≤ t → (∑ j, rateX j t x * (V (jump j x) - V x)) ≤ bX * (1 + V x))
  (hdriftY : ∀ x t, 0 ≤ t → (∑ j, rateY j t x * (V (jump j x) - V x)) ≤ bY * (1 + V x))
include hRateX hRateY hinitX hinitY hbX hbY hVnonneg hqX hqY hVX hVY hdriftX hdriftY

/-- A genuine common-level crossing bound for two actual coupled global paths.
The initial records and driving noise may be shared arbitrarily. Each marginal
Lyapunov hypothesis is used to derive its own crossing estimate. -/
theorem measure_paired_crossing_le (R T : ℝ) (hR : 0 < R) (hT : 0 ≤ T) :
    (law μ J) {p | ∃ t ∈ Icc 0 T, R ≤
      V (TimeDependentGlobalProcess.process V hfinite jump rateX hboundedX initialX e p t) +
      V (TimeDependentGlobalProcess.process V hfinite jump rateY hboundedY initialY e p t)} ≤
    ENNReal.ofReal (4 * (((1 + ∫ a, V (initialX a) ∂μ) * Real.exp (bX * T)) +
      ((1 + ∫ a, V (initialY a) ∂μ) * Real.exp (bY * T))) / R) := by
  apply (measure_sum_crossing_le (law μ J) V V
    (TimeDependentGlobalProcess.process V hfinite jump rateX hboundedX initialX e)
    (TimeDependentGlobalProcess.process V hfinite jump rateY hboundedY initialY e) R T).trans
  have hx := measure_crossing_le V hfinite jump rateX hboundedX initialX e μ
    hRateX hinitX bX hbX hVnonneg hqX hVX hdriftX (R / 2) T (by positivity) hT
  have hy := measure_crossing_le V hfinite jump rateY hboundedY initialY e μ
    hRateY hinitY bY hbY hVnonneg hqY hVY hdriftY (R / 2) T (by positivity) hT
  apply (add_le_add hx hy).trans
  have hmX : 0 ≤ ∫ a, V (initialX a) ∂μ := integral_nonneg (fun _ => hVnonneg _)
  have hmY : 0 ≤ ∫ a, V (initialY a) ∂μ := integral_nonneg (fun _ => hVnonneg _)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply le_of_eq
  congr 1
  field_simp
  ring


/-- The genuine first exit of the combined actual Lyapunov values. -/
def pairedFirstExit (R : ℝ) (p : Sample A J) : ℝ≥0∞ :=
  firstExit (fun z : E × E => V z.1 + V z.2)
    (fun p t => (TimeDependentGlobalProcess.process V hfinite jump rateX hboundedX initialX e p t,
      TimeDependentGlobalProcess.process V hfinite jump rateY hboundedY initialY e p t)) R p

variable [DiscreteTopology E]

/-- Both actual coordinates are constant on a common right interval on one event. -/
theorem ae_paired_right_constant : ∀ᵐ p ∂law μ J, ∀ t : ℝ, 0 ≤ t →
    ∃ b, t < b ∧ ∀ s ∈ Ico t b,
      (TimeDependentGlobalProcess.process V hfinite jump rateX hboundedX initialX e p s,
        TimeDependentGlobalProcess.process V hfinite jump rateY hboundedY initialY e p s) =
      (TimeDependentGlobalProcess.process V hfinite jump rateX hboundedX initialX e p t,
        TimeDependentGlobalProcess.process V hfinite jump rateY hboundedY initialY e p t) := by
  filter_upwards [ae_right_constant V hfinite jump rateX hboundedX initialX e μ
    hRateX hinitX bX hbX hVnonneg hqX hVX hdriftX,
    ae_right_constant V hfinite jump rateY hboundedY initialY e μ
      hRateY hinitY bY hbY hVnonneg hqY hVY hdriftY] with p hx hy
  intro t ht
  obtain ⟨b, hb, hx⟩ := hx t ht
  obtain ⟨c, hc, hy⟩ := hy t ht
  refine ⟨min b c, lt_min hb hc, fun s hs => ?_⟩
  exact Prod.ext (hx s ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩)
    (hy s ⟨hs.1, hs.2.trans_le (min_le_right _ _)⟩)

/-- The common exit event equals an attained real-time crossing, including
both endpoints of every nonnegative horizon. -/
theorem ae_pairedFirstExit_le_iff_crossing : ∀ᵐ p ∂law μ J, ∀ R T : ℝ, 0 ≤ T →
    (pairedFirstExit V hfinite jump rateX rateY hboundedX hboundedY initialX initialY e R p ≤
      ENNReal.ofReal T ↔ ∃ t ∈ Icc 0 T, R ≤
        V (TimeDependentGlobalProcess.process V hfinite jump rateX hboundedX initialX e p t) +
        V (TimeDependentGlobalProcess.process V hfinite jump rateY hboundedY initialY e p t)) := by
  filter_upwards [ae_paired_right_constant V hfinite jump rateX rateY hboundedX hboundedY
    initialX initialY e μ hRateX hRateY hinitX hinitY bX bY hbX hbY hVnonneg hqX hqY hVX hVY hdriftX hdriftY]
    with p hp
  intro R T hT
  simpa only [pairedFirstExit, firstExit, mem_setOf_eq, not_lt] using
    ExitTimeMeasurability.exitTime_le_iff_exists {z : E × E | V z.1 + V z.2 < R}
      (fun t => (TimeDependentGlobalProcess.process V hfinite jump rateX hboundedX initialX e p t,
        TimeDependentGlobalProcess.process V hfinite jump rateY hboundedY initialY e p t)) hp T hT

/-- The exact combined global exit is AE measurable under the original common law. -/
theorem aemeasurable_pairedFirstExit (R : ℝ) :
    AEMeasurable (pairedFirstExit V hfinite jump rateX rateY hboundedX hboundedY initialX initialY e R)
      (law μ J) := by
  apply ExitTimeMeasurability.aemeasurable_exitTime
    (fun t p => (TimeDependentGlobalProcess.process V hfinite jump rateX hboundedX initialX e p t,
      TimeDependentGlobalProcess.process V hfinite jump rateY hboundedY initialY e p t))
    (fun t _ => ((TimeDependentGlobalProcess.measurable_process_at V hfinite jump rateX hboundedX initialX e
      hRateX hinitX t).mono ((filtration A J).le t) le_rfl).prodMk
      ((TimeDependentGlobalProcess.measurable_process_at V hfinite jump rateY hboundedY initialY e
        hRateY hinitY t).mono ((filtration A J).le t) le_rfl))
    {z : E × E | V z.1 + V z.2 < R}
    (measurableSet_lt (measurable_of_countable (fun z : E × E => V z.1 + V z.2)) measurable_const)
  exact ae_paired_right_constant V hfinite jump rateX rateY hboundedX hboundedY
    initialX initialY e μ hRateX hRateY hinitX hinitY bX bY hbX hbY hVnonneg hqX hqY hVX hVY hdriftX hdriftY

/-- The common genuine exit has an explicit reciprocal tail. In a particle
application the coefficients are uniform whenever the initial averaged
moments and single-particle drift coefficients are uniform. -/
theorem pairedFirstExit_probability_le (R T : ℝ) (hR : 0 < R) (hT : 0 ≤ T) :
    (law μ J) {p | pairedFirstExit V hfinite jump rateX rateY hboundedX hboundedY initialX initialY e R p ≤
      ENNReal.ofReal T} ≤
    ENNReal.ofReal (4 * (((1 + ∫ a, V (initialX a) ∂μ) * Real.exp (bX * T)) +
      ((1 + ∫ a, V (initialY a) ∂μ) * Real.exp (bY * T))) / R) := by
  have he : {p | pairedFirstExit V hfinite jump rateX rateY hboundedX hboundedY initialX initialY e R p ≤
      ENNReal.ofReal T} =ᵐ[law μ J] {p | ∃ t ∈ Icc 0 T, R ≤
      V (TimeDependentGlobalProcess.process V hfinite jump rateX hboundedX initialX e p t) +
      V (TimeDependentGlobalProcess.process V hfinite jump rateY hboundedY initialY e p t)} := by
    filter_upwards [ae_pairedFirstExit_le_iff_crossing V hfinite jump rateX rateY hboundedX hboundedY
      initialX initialY e μ hRateX hRateY hinitX hinitY bX bY hbX hbY hVnonneg hqX hqY hVX hVY hdriftX hdriftY]
      with p hp
    exact propext (hp R T hT)
  rw [measure_congr he]
  exact measure_paired_crossing_le V hfinite jump rateX rateY hboundedX hboundedY
    initialX initialY e μ hRateX hRateY hinitX hinitY bX bY hbX hbY hVnonneg hqX hqY hVX hVY hdriftX hdriftY
      R T hR hT

end Paired
end CarryingCapacity.GlobalLyapunovExit
