import CarryingCapacity.SynchronousFrozenCounting
import CarryingCapacity.TimeDependentGlobalCounting

/-!
# Positive distance domination for the actual shared-noise global paths

The two existing processes are compared on one common finite proposal list.
Genuine exit exhaustion selects active regions, and cutoff independence puts
both recursions under a common height bound. Their actual left states identify
the finite positive increments with the unrestricted predictable field.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal

namespace CarryingCapacity.SynchronousGlobalCounting
open CommonInitialNoise TimeDependentLocalization TimeDependentGlobalCounting
open LyapunovLocalization (active)
open SynchronousPositiveIncrement

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

/-- Unrestricted positive synchronous increments, on a deterministic horizon. -/
def positiveField (ρ : E → E → ℝ) (j : J) (T : ℝ)
    (p : Sample A J × (ℝ × ℝ)) : ℝ :=
  if p.2.1 ∈ Ioc 0 T then
    positiveIncrement ρ jump j
      (rateX j p.2.1 (preState V hfinite jump rateX boundX initialX e p.1 p.2.1))
      (rateY j p.2.1 (preState V hfinite jump rateY boundY initialY e p.1 p.2.1))
      (preState V hfinite jump rateX boundX initialX e p.1 p.2.1)
      (preState V hfinite jump rateY boundY initialY e p.1 p.2.1) p.2.2
  else 0

omit [Fintype J] [PolishSpace E] in
theorem positiveField_apply (ρ : E → E → ℝ) (j : J) (T : ℝ)
    (p : Sample A J) (q : ℝ × ℝ) :
    positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j T (p,q) =
      if q.1 ∈ Ioc 0 T then
        positiveIncrement ρ jump j
          (rateX j q.1 (preState V hfinite jump rateX boundX initialX e p q.1))
          (rateY j q.1 (preState V hfinite jump rateY boundY initialY e p q.1))
          (preState V hfinite jump rateX boundX initialX e p q.1)
          (preState V hfinite jump rateY boundY initialY e p q.1) q.2
      else 0 := rfl

omit [Fintype J] [PolishSpace E] in
theorem positiveField_nonneg (ρ : E → E → ℝ) (j : J) (T : ℝ)
    (p : Sample A J × (ℝ × ℝ)) :
    0 ≤ positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j T p := by
  unfold positiveField
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl


omit [Fintype J] [PolishSpace E] in
/-- Enlarging the horizon only adds nonnegative synchronous increments. -/
theorem positiveField_mono_horizon (ρ : E → E → ℝ) (j : J) {t T : ℝ}
    (htT : t ≤ T) (p : Sample A J × (ℝ × ℝ)) :
    positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j t p ≤
      positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j T p := by
  by_cases ht : p.2.1 ∈ Ioc 0 t
  · have hT : p.2.1 ∈ Ioc 0 T := ⟨ht.1, ht.2.trans htT⟩
    simp only [positiveField, ht, hT, ↓reduceIte, le_refl]
  · simpa only [positiveField, ht, ↓reduceIte] using
      positiveField_nonneg V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j T p

section OnePath
omit rateY boundY initialY
variable [MeasurableSpace A] (μ : Measure A)

/-- Before an actual localized exit, any larger valid cap gives the same
current and strict-past states as the existing global path. -/
theorem ae_agrees_with_larger_cap : ∀ᵐ p ∂law μ J, ∀ n : ℕ, ∀ C : ℝ,
    rateBound V hfinite rateX boundX n ≤ C → ∀ T : ℝ≥0,
    (T : ℝ≥0∞) < exit V hfinite jump rateX boundX initialX n p →
    (∀ t ∈ Icc (0 : ℝ) T,
      TimeDependentGlobalProcess.process V hfinite jump rateX boundX initialX e p t =
        TimeDependentFrozenProcess.process (active V hfinite n) jump rateX C (initialX p.1) p.2 t) ∧
    (∀ t ∈ Ioc (0 : ℝ) T,
      preState V hfinite jump rateX boundX initialX e p t =
        TimeDependentJumpIdentity.leftProcess (active V hfinite n) jump rateX C (initialX p.1) p.2 t ∧
      preState V hfinite jump rateX boundX initialX e p t ∈ active V hfinite n) := by
  have hl := ae_all_iff.mpr (fun n : ℕ => ae_noise μ
    (TimeDependentJumpIdentity.ae_process_eq_leftProcess_on_left
      (active V hfinite n) jump rateX))
  filter_upwards [TimeDependentGlobalProcess.ae_eq_path V hfinite jump rateX boundX initialX e μ,
    ae_preState_eq_level V hfinite jump rateX boundX initialX e μ,
    ae_noise μ (ChronologicalEvents.ae_boxedList_height_filter (J := J)), hl]
    with p hp hpre hfilter hleft
  intro n C hC T hT
  have hcap (t : ℝ) :
      TimeDependentFrozenProcess.process (active V hfinite n) jump rateX
        (rateBound V hfinite rateX boundX n) (initialX p.1) p.2 t =
      TimeDependentFrozenProcess.process (active V hfinite n) jump rateX C (initialX p.1) p.2 t := by
    unfold TimeDependentFrozenProcess.process TimeDependentFrozenProcess.runBox
    rw [← hfilter t (rateBound V hfinite rateX boundX n) C hC]
    exact TimeDependentFrozenProcess.run_filter_height (active V hfinite n) jump rateX
      (rateBound V hfinite rateX boundX n) (rate_le_bound V hfinite rateX boundX n) p.2 (initialX p.1) _
  have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      TimeDependentGlobalProcess.process V hfinite jump rateX boundX initialX e p t =
        TimeDependentFrozenProcess.process (active V hfinite n) jump rateX C (initialX p.1) p.2 t := by
    apply (hp n t ht.1 ?_).trans (hcap t)
    exact (show ENNReal.ofReal t ≤ (T : ℝ≥0∞) by
      simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal ht.2).trans hT.le
  refine ⟨he, ?_⟩
  intro t ht
  refine ⟨?_, (hpre n T hT t ht).2⟩
  obtain ⟨b, hb, hy⟩ := hleft n C (initialX p.1) t
  apply PredictableStepApproximation.pastLimit_eq_of_left_constant _ e p t ht.1 (max b 0) (max_lt hb ht.1)
  intro u hu
  exact (he u ⟨(le_max_right b 0).trans hu.1, hu.2.le.trans ht.2⟩).trans
    (hy u ⟨(le_max_left b 0).trans hu.1, hu.2⟩)

end OnePath


variable [MeasurableSpace A] (μ : Measure A)

/-- Actual shared-noise pathwise distance domination. The only localization
premises are exhaustion of the two genuine exit sequences. The increment
field has no freezing indicator or height cap. -/
theorem ae_ofReal_distance_le_lintegral (ρ : E → E → ℝ)
    (hρ : ∀ x y, 0 ≤ ρ x y)
    (hexhaustX : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rateX boundX initialX n p)
    (hexhaustY : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rateY boundY initialY n p) :
    ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0,
      ENNReal.ofReal (ρ
        (TimeDependentGlobalProcess.process V hfinite jump rateX boundX initialX e p T)
        (TimeDependentGlobalProcess.process V hfinite jump rateY boundY initialY e p T)) ≤
      ENNReal.ofReal (ρ (initialX p.1) (initialY p.1)) +
        ∑ j : J, ∫⁻ q, ENNReal.ofReal
          (positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j T (p,q))
          ∂MarkedNoise.countingMeasure j p.2 := by
  have hf := ae_all_iff.mpr (fun n : ℕ => ae_all_iff.mpr (fun m : ℕ =>
    ae_noise μ (SynchronousFrozenCounting.ae_ofReal_distance_le_lintegral
      (active V hfinite n) (active V hfinite m) jump rateX rateY ρ hρ)))
  filter_upwards [ae_agrees_with_larger_cap V hfinite jump rateX boundX initialX e μ,
    ae_agrees_with_larger_cap V hfinite jump rateY boundY initialY e μ,
    hf, ae_noise μ (MarkedNoise.ae_positive_points (J := J)), hexhaustX, hexhaustY]
    with p hX hY hd hpos hexX hexY
  intro T
  obtain ⟨n, hn⟩ := hexX T
  obtain ⟨m, hm⟩ := hexY T
  let C := max (rateBound V hfinite rateX boundX n) (rateBound V hfinite rateY boundY m)
  have hXcap := hX n C (le_max_left _ _) T hn
  have hYcap := hY m C (le_max_right _ _) T hm
  have hleftX : ∀ t ∈ Ioc (0 : ℝ) T,
      TimeDependentJumpIdentity.leftProcess (active V hfinite n) jump rateX C (initialX p.1) p.2 t
        ∈ active V hfinite n := by
    intro t ht
    rw [← (hXcap.2 t ht).1]
    exact (hXcap.2 t ht).2
  have hleftY : ∀ t ∈ Ioc (0 : ℝ) T,
      TimeDependentJumpIdentity.leftProcess (active V hfinite m) jump rateY C (initialY p.1) p.2 t
        ∈ active V hfinite m := by
    intro t ht
    rw [← (hYcap.2 t ht).1]
    exact (hYcap.2 t ht).2
  have h := hd n m C (initialX p.1) (initialY p.1) T hleftX hleftY
  rw [← hXcap.1 T ⟨T.coe_nonneg, le_rfl⟩, ← hYcap.1 T ⟨T.coe_nonneg, le_rfl⟩] at h
  apply h.trans
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro j _
  have hqpos : ∀ᵐ q ∂MarkedNoise.countingMeasure j p.2, 0 < q.1 := by
    simpa only [MarkedNoise.countingMeasure, Measure.ae_sum_iff, ae_dirac_eq,
      eventually_pure] using (fun k => (hpos j k).1)
  apply lintegral_mono_ae
  filter_upwards [hqpos] with q hq
  by_cases hb : q ∈ Iic (T : ℝ) ×ˢ Iic C
  · have ht : q.1 ∈ Ioc (0 : ℝ) T := ⟨hq, hb.1⟩
    simp only [SynchronousFrozenCounting.boxField, Set.indicator_of_mem hb,
      positiveField_apply, if_pos ht, SynchronousFrozenCounting.field]
    rw [← (hXcap.2 q.1 ht).1, ← (hYcap.2 q.1 ht).1]
  · simp only [SynchronousFrozenCounting.boxField, Set.indicator_of_not_mem hb,
      ENNReal.ofReal_zero, zero_le]


/-- One positive-increment integral controls the distance at every time up
to its horizon, on one common probability-one event. -/
theorem ae_ofReal_distance_le_lintegral_horizon (ρ : E → E → ℝ)
    (hρ : ∀ x y, 0 ≤ ρ x y)
    (hexhaustX : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rateX boundX initialX n p)
    (hexhaustY : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rateY boundY initialY n p) :
    ∀ᵐ p ∂law μ J, ∀ T t : ℝ≥0, t ≤ T →
      ENNReal.ofReal (ρ
        (TimeDependentGlobalProcess.process V hfinite jump rateX boundX initialX e p t)
        (TimeDependentGlobalProcess.process V hfinite jump rateY boundY initialY e p t)) ≤
      ENNReal.ofReal (ρ (initialX p.1) (initialY p.1)) +
        ∑ j : J, ∫⁻ q, ENNReal.ofReal
          (positiveField V hfinite jump rateX boundX rateY boundY initialX initialY e ρ j T (p,q))
          ∂MarkedNoise.countingMeasure j p.2 := by
  filter_upwards [ae_ofReal_distance_le_lintegral V hfinite jump rateX boundX rateY boundY
    initialX initialY e μ ρ hρ hexhaustX hexhaustY] with p hp
  intro T t htT
  apply (hp t).trans
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro j _
  apply lintegral_mono
  intro q
  exact ENNReal.ofReal_le_ofReal (positiveField_mono_horizon V hfinite jump rateX boundX
    rateY boundY initialX initialY e ρ j (NNReal.coe_le_coe.mpr htT) (p,q))

end CarryingCapacity.SynchronousGlobalCounting
