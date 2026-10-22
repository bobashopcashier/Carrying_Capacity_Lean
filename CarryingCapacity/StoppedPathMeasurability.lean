import CarryingCapacity.ExitTimeMeasurability
import CarryingCapacity.SynchronousRunningSupremum

/-!
# Actual stopped paths and their running suprema

A measurable version of an AE measurable extended stopping time gives a
jointly measurable version of the stopped path. Equality holds on one sample
event at every time, hence transfers to any product time measure. Stopping
preserves right-local constancy, including the exit jump. The actual running
supremum is therefore the rational-plus-terminal supremum almost surely.
No stopping-time property or finiteness of the supremum is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical ENNReal

namespace CarryingCapacity.StoppedPathMeasurability
open CommonFrozenExit SynchronousRunningSupremum

variable {Ω E : Type*}

/-- Stopping an actually right-locally-constant path preserves that property,
without any special assumption about the selected extended time. -/
theorem stopped_right_constant (f : ℝ → E) (σ : ℝ≥0∞)
    (hright : ∀ t : ℝ, 0 ≤ t → ∃ b, t < b ∧ ∀ u ∈ Ico t b, f u = f t) :
    ∀ t : ℝ, 0 ≤ t → ∃ b, t < b ∧ ∀ u ∈ Ico t b,
      stopped σ f u = stopped σ f t := by
  intro t ht
  by_cases hσ : σ = ⊤
  · simpa only [stopped, hσ, if_true] using hright t ht
  · by_cases ha : σ.toReal ≤ t
    · refine ⟨t+1, by linarith, fun u hu => ?_⟩
      simp only [stopped, if_neg hσ, min_eq_right ha, min_eq_right (ha.trans hu.1)]
    · have hta : t < σ.toReal := lt_of_not_ge ha
      obtain ⟨b, hb, hlocal⟩ := hright t ht
      refine ⟨min b σ.toReal, lt_min hb hta, fun u hu => ?_⟩
      have hua : u < σ.toReal := hu.2.trans_le (min_le_right _ _)
      simp only [stopped, if_neg hσ, min_eq_left hta.le, min_eq_left hua.le]
      exact hlocal u ⟨hu.1, hu.2.trans_le (min_le_left _ _)⟩

section Measurability
variable [MeasurableSpace Ω] [MeasurableSpace E]
  (X : Ω → ℝ → E) (hX : Measurable (fun p : Ω × ℝ => X p.1 p.2))
  (σ : Ω → ℝ≥0∞)

include hX in
/-- Joint measurability with an everywhere measurable extended time. -/
theorem measurable_stopped (hσ : Measurable σ) :
    Measurable (fun p : Ω × ℝ => stopped (σ p.1) (X p.1) p.2) := by
  have ht : Measurable (fun p : Ω × ℝ =>
      if σ p.1 = ⊤ then p.2 else min p.2 (σ p.1).toReal) :=
    measurable_snd.ite ((hσ.comp measurable_fst) (measurableSet_singleton ⊤))
      (measurable_snd.min ((hσ.comp measurable_fst).ennreal_toReal))
  have h := hX.comp (measurable_fst.prodMk ht)
  convert h using 1
  funext p
  simp only [stopped, Function.comp_apply]
  split_ifs <;> rfl

variable (μ : Measure Ω) (hσ : AEMeasurable σ μ)

include hX hσ in
/-- Joint AE measurability of the exact stopped path, for any time measure.
The sample null set is pulled back by the product first-coordinate projection. -/
theorem aemeasurable_stopped (ν : Measure ℝ) :
    AEMeasurable (fun p : Ω × ℝ => stopped (σ p.1) (X p.1) p.2) (μ.prod ν) := by
  have hm := measurable_stopped X hX (hσ.mk σ) hσ.measurable_mk
  apply hm.aemeasurable.congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hσ.ae_eq_mk] with p hp
  rw [hp]

include hX hσ in
/-- Exact fixed-time evaluations are AE measurable under the original law. -/
theorem aemeasurable_stopped_at (t : ℝ) :
    AEMeasurable (fun ω => stopped (σ ω) (X ω) t) μ := by
  have hm := (measurable_stopped X hX (hσ.mk σ) hσ.measurable_mk).comp
    (measurable_id.prodMk (measurable_const (a := t)))
  apply hm.aemeasurable.congr
  filter_upwards [hσ.ae_eq_mk] with ω hω
  rw [hω]
  rfl

variable (hright : ∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t →
  ∃ b, t < b ∧ ∀ u ∈ Ico t b, X ω u = X ω t)
include hright

omit [MeasurableSpace E] in
/-- Actual stopped paths retain right-local constancy on one sample event. -/
theorem ae_stopped_right_constant : ∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t →
    ∃ b, t < b ∧ ∀ u ∈ Ico t b,
      stopped (σ ω) (X ω) u = stopped (σ ω) (X ω) t := by
  filter_upwards [hright] with ω hω
  exact stopped_right_constant (X ω) (σ ω) hω

omit [MeasurableSpace E] in
/-- Countable observations recover the true supremum, simultaneously for all
costs and all nonnegative horizons. The cost need not be continuous. -/
theorem ae_intervalSup_eq_observedSup : ∀ᵐ ω ∂μ, ∀ (cost : E → ℝ≥0∞) (T : ℝ), 0 ≤ T →
    intervalSup (fun t => cost (stopped (σ ω) (X ω) t)) T =
      observedSup (fun t => cost (stopped (σ ω) (X ω) t)) T := by
  filter_upwards [ae_stopped_right_constant X σ μ hright] with ω hω
  intro cost T hT
  apply intervalSup_eq_observedSup _ T hT
  intro t ht
  obtain ⟨b, hb, he⟩ := hω t ht.1
  exact ⟨b, hb, fun u hu => congrArg cost (he u hu)⟩

variable [Countable E] [MeasurableSingletonClass E]
include hX hσ in
/-- The actual uncountable stopped running supremum is AE measurable, with
no measurability or integrability premise on that supremum. -/
theorem aemeasurable_intervalSup_stopped (cost : E → ℝ≥0∞) (T : ℝ) (hT : 0 ≤ T) :
    AEMeasurable (fun ω => intervalSup (fun t => cost (stopped (σ ω) (X ω) t)) T) μ := by
  have hm (t : ℝ) : AEMeasurable (fun ω => cost (stopped (σ ω) (X ω) t)) μ :=
    (measurable_of_countable cost).comp_aemeasurable (aemeasurable_stopped_at X hX σ μ hσ t)
  have ho : AEMeasurable (fun ω => observedSup
      (fun t => cost (stopped (σ ω) (X ω) t)) T) μ := by
    apply (hm T).sup
    apply AEMeasurable.iSup
    intro q
    by_cases hq : (q : ℝ) ∈ Icc (0 : ℝ) T
    · simpa only [if_pos hq] using hm q
    · simp only [if_neg hq]
      exact aemeasurable_const
  apply ho.congr
  filter_upwards [ae_intervalSup_eq_observedSup X σ μ hright] with ω hω
  exact (hω cost T hT).symm

end Measurability

section ActualExit
variable [MeasurableSpace Ω] [MeasurableSpace E]
  (X : Ω → ℝ → E) (hX : Measurable (fun p : Ω × ℝ => X p.1 p.2))
  (G : Set E) (hG : MeasurableSet G) (μ : Measure Ω)
  (hright : ∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t →
    ∃ b, t < b ∧ ∀ u ∈ Ico t b, X ω u = X ω t)
include hX hG hright

/-- The genuine exit is AE measurable from the actual path hypotheses. -/
theorem aemeasurable_exitTime : AEMeasurable (fun ω => exitTime G (X ω)) μ :=
  ExitTimeMeasurability.aemeasurable_exitTime (fun t ω => X ω t)
    (fun t _ => hX.comp (measurable_id.prodMk (measurable_const (a := t)))) G hG μ hright

/-- Joint AE measurability stopped at the genuine exit, without supplying
exit measurability as an extra assumption. Any time measure is allowed. -/
theorem aemeasurable_exit_stopped (ν : Measure ℝ) :
    AEMeasurable (fun p : Ω × ℝ => stopped (exitTime G (X p.1)) (X p.1) p.2) (μ.prod ν) :=
  aemeasurable_stopped X hX _ μ (aemeasurable_exitTime X hX G hG μ hright) ν

/-- Fixed-time measurability at the genuine exit. -/
theorem aemeasurable_exit_stopped_at (t : ℝ) :
    AEMeasurable (fun ω => stopped (exitTime G (X ω)) (X ω) t) μ :=
  aemeasurable_stopped_at X hX _ μ (aemeasurable_exitTime X hX G hG μ hright) t

variable [Countable E] [MeasurableSingletonClass E]

/-- Actual stopped costs on a countable state space have measurable running
suprema, including the exit jump and the terminal horizon value. -/
theorem aemeasurable_exit_intervalSup (cost : E → ℝ≥0∞) (T : ℝ) (hT : 0 ≤ T) :
    AEMeasurable (fun ω => intervalSup
      (fun t => cost (stopped (exitTime G (X ω)) (X ω) t)) T) μ :=
  aemeasurable_intervalSup_stopped X hX _ μ (aemeasurable_exitTime X hX G hG μ hright)
    hright cost T hT

end ActualExit
end CarryingCapacity.StoppedPathMeasurability
