import CarryingCapacity.MarkedCountMoments
import CarryingCapacity.CommonFrozenStopping

/-!
# Actual marked prefix counts are adapted on every sample

Counting the observed points reproduces the original prefix measure exactly:
every censored sentinel has time T+1 and lies outside the prefix at T. No
local-finiteness event is needed for this extended-valued identity. Taking its
real value therefore proves adaptedness of the original real count, including
its original exceptional-sample values.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace CarryingCapacity.MarkedCountAdapted
open MarkedNoise MarkedCountMoments CommonNoiseFiltration

variable {J : Type*}

/-- Prefix mass reconstructed solely from the observed labelled point family. -/
def observedMass (j : J) (B : Set ℝ) (T : ℝ) (v : EventView J) : ℝ≥0∞ :=
  ∑' p : ℕ × ℕ, Measure.dirac (v (j, p)) (Iic T ×ˢ B)

theorem measurable_observedMass (j : J) (B : Set ℝ) (hB : MeasurableSet B) (T : ℝ) :
    Measurable (observedMass j B T) := by
  apply Measurable.ennreal_tsum
  intro p
  exact (Measure.measurable_coe (measurableSet_Iic.prod hB)).comp
    (Measure.measurable_dirac.comp (measurable_pi_apply (j, p)))

/-- Actual and observed Dirac atoms have identical mass in the current prefix. -/
theorem dirac_view_prefix (j : J) (B : Set ℝ) (hB : MeasurableSet B) (T : ℝ)
    (ω : MarkedNoise.Sample J) (p : ℕ × ℕ) :
    Measure.dirac (MarkedNoise.point j ω p) (Iic T ×ˢ B) =
      Measure.dirac (view T ω (j, p)) (Iic T ×ˢ B) := by
  by_cases h : (MarkedNoise.point j ω p).1 ≤ T
  · simp only [view, censor, points, h, if_true]
  · have hsent : ¬T + 1 ≤ T := by linarith
    simp only [view, censor, points, h, if_false,
      Measure.dirac_apply' _ (measurableSet_Iic.prod hB), Set.indicator_apply,
      Set.mem_prod, Set.mem_Iic, h, hsent, false_and, if_false]
    rw [Set.indicator_of_not_mem (fun hp => h hp.1),
      Set.indicator_of_not_mem (fun hp => hsent hp.1)]

/-- The full prefix measure factors exactly through the natural noise view. -/
theorem countingMass_eq_observedMass (j : J) (B : Set ℝ) (hB : MeasurableSet B) (T : ℝ)
    (ω : MarkedNoise.Sample J) :
    countingMeasure j ω (Iic T ×ˢ B) = observedMass j B T (view T ω) := by
  rw [countingMeasure, Measure.sum_apply _ (measurableSet_Iic.prod hB)]
  exact tsum_congr (fun p => dirac_view_prefix j B hB T ω p)

theorem measurable_countingMass_at (j : J) (B : Set ℝ) (hB : MeasurableSet B) (T : ℝ) :
    Measurable[filtration J T]
      (fun ω : MarkedNoise.Sample J => countingMeasure j ω (Iic T ×ˢ B)) := by
  have he : (fun ω : MarkedNoise.Sample J => countingMeasure j ω (Iic T ×ˢ B)) =
      observedMass j B T ∘ view T := funext (countingMass_eq_observedMass j B hB T)
  rw [he]
  exact (measurable_observedMass j B hB T).comp (measurable_view_at T)

/-- Real prefix counts are measurable in the actual noise history without a null-set modification. -/
theorem measurable_realCount_at (j : J) (B : Set ℝ) (hB : MeasurableSet B) (T : ℝ) :
    Measurable[filtration J T] (realCount j B T) :=
  (measurable_countingMass_at j B hB T).ennreal_toReal

theorem adapted_realCount (j : J) (B : Set ℝ) (hB : MeasurableSet B) :
    Adapted (filtration J) (fun T => realCount j B T) :=
  fun T => (measurable_realCount_at j B hB T).stronglyMeasurable

theorem adapted_nonnegative_realCount (j : J) (B : Set ℝ) (hB : MeasurableSet B) :
    Adapted (nonnegativeFiltration J) (fun T => realCount j B (T : ℝ)) :=
  fun T => (measurable_realCount_at j B hB T).stronglyMeasurable

theorem measurable_realCount_completedAt (j : J) (B : Set ℝ)
    (hB : MeasurableSet B) (T : ℝ) :
    Measurable[CommonFrozenStopping.completedAt J T] (realCount j B T) :=
  (measurable_realCount_at j B hB T).mono
    (CommonFrozenStopping.raw_le_completedAt J T) le_rfl

theorem adapted_completed_realCount (j : J) (B : Set ℝ) (hB : MeasurableSet B) :
    Adapted (CommonFrozenStopping.completedFiltration J) (fun T => realCount j B T) :=
  fun T => (measurable_realCount_completedAt j B hB T).stronglyMeasurable

end CarryingCapacity.MarkedCountAdapted
