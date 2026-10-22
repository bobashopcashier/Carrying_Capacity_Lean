import CarryingCapacity.MarkedStripCounts
import CarryingCapacity.MarkedIntensity

/-!
# Finite strip sums for bounded height categories

A height category contained below a natural cutoff receives no points from
higher strips, because the actual uniform marks are nonnegative almost surely.
The full common-noise rectangle count is therefore a finite sum of the genuine
strip counts. The same finite sum of translated mark probabilities is exactly
positive Lebesgue measure of the category.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace CarryingCapacity.MarkedBoundedCounts
open FrozenProcess MarkedNoise MarkedStripCounts MarkedIntensity

/-- A natural-valued finite sum on the original common-noise sample space. -/
def boundedCount {J : Type*} (j : J) (m : ℕ) (B : Set ℝ) (T : ℝ)
    (ω : MarkedNoise.Sample J) : ℕ :=
  ∑ n ∈ Finset.range m,
    clockCount ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B) T (ω (j, n))

theorem measurable_boundedCount {J : Type*} (j : J) (m : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B) (T : ℝ) :
    Measurable (boundedCount j m B T) := by
  apply Finset.measurable_sum
  intro n _
  exact (measurable_clockCount _ (hB.preimage (measurable_const.add measurable_id)) T).comp
    (measurable_pi_apply (j, n))

/-- No nonnegative mark in strip n can fall strictly below m when m ≤ n. -/
theorem clockCount_eq_zero_of_le {m n : ℕ} (hmn : m ≤ n)
    (B : Set ℝ) (hB : B ⊆ Iio (m : ℝ)) (T : ℝ) (ω : StripSample)
    (hmark : ∀ k, 0 ≤ ω.2 k) :
    clockCount ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B) T ω = 0 := by
  classical
  unfold clockCount prefixCount
  apply Finset.sum_eq_zero
  intro k _
  have hn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hnot : (n : ℝ) + ω.2 k ∉ B := by
    intro h
    have hh := hB h
    have hk := hmark k
    change (n : ℝ) + ω.2 k < (m : ℝ) at hh
    linarith
  simp only [Set.mem_preimage, if_neg hnot]

theorem ae_nonnegative_marks {J : Type*} (j : J) :
    ∀ᵐ ω ∂law J, ∀ n k : ℕ, 0 ≤ (ω (j, n)).2 k := by
  rw [ae_all_iff]
  intro n
  have h := strip_ae_good
  rw [← strip_map J (j, n)] at h
  filter_upwards [ae_of_ae_map (measurable_pi_apply (j, n)).aemeasurable h] with ω hω
  exact fun k => (hω.2 k).1

/-- One probability-one event identifies all bounded categories and horizons. -/
theorem ae_countingMeasure_eq_boundedCount {J : Type*} (j : J) :
    ∀ᵐ ω ∂law J, ∀ m : ℕ, ∀ B : Set ℝ, MeasurableSet B → B ⊆ Iio (m : ℝ) →
      ∀ T : ℝ, 0 ≤ T →
        countingMeasure j ω (Iic T ×ˢ B) = (boundedCount j m B T ω : ℝ≥0∞) := by
  filter_upwards [ae_countingMeasure_rectangle j, ae_nonnegative_marks j] with ω hcount hmark
  intro m B hB hbound T hT
  rw [hcount T hT B hB]
  rw [tsum_eq_sum (s := Finset.range m) (fun n hn => by
    have hmn : m ≤ n := Nat.le_of_not_gt (by simpa using hn)
    rw [clockCount_eq_zero_of_le hmn B hbound T (ω (j, n)) (hmark n)]
    exact Nat.cast_zero)]
  simp only [boundedCount, Nat.cast_sum]

/-- Higher strips also have zero category probability, without an exceptional event. -/
theorem uniformUnit_preimage_eq_zero_of_le {m n : ℕ} (hmn : m ≤ n)
    (B : Set ℝ) (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ)) :
    uniformUnit ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B) = 0 := by
  have hmap := Measure.map_apply (μ := uniformUnit) (f := fun x : ℝ => (n : ℝ) + x)
    (measurable_const.add measurable_id) hB
  rw [← hmap, translated_uniformUnit, Measure.restrict_apply hB]
  have he : B ∩ Ico (n : ℝ) ((n : ℝ) + 1) = ∅ := by
    apply Set.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    have hn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hb := hbound hx.1
    exact (not_lt_of_ge (hn.trans hx.2.1)) hb
  rw [he, measure_empty]

/-- The finite sum of strip category probabilities equals positive Lebesgue mass. -/
theorem sum_uniformUnit_preimage (m : ℕ) (B : Set ℝ) (hB : MeasurableSet B)
    (hbound : B ⊆ Iio (m : ℝ)) :
    (∑ n ∈ Finset.range m, uniformUnit ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B)) =
      positiveVolume B := by
  rw [positiveVolume, Measure.restrict_apply hB, ← tsum_uniformUnit_preimage B hB]
  symm
  exact tsum_eq_sum (fun n hn => uniformUnit_preimage_eq_zero_of_le
    (Nat.le_of_not_gt (by simpa using hn)) B hB hbound)

theorem positiveVolume_ne_top_of_bounded (m : ℕ) (B : Set ℝ)
    (hbound : B ⊆ Iio (m : ℝ)) : positiveVolume B ≠ ∞ := by
  have hle : positiveVolume B ≤ positiveVolume (Iic (m : ℝ)) :=
    measure_mono (fun x hx => show x ≤ (m : ℝ) from le_of_lt (hbound hx))
  rw [positiveVolume_Iic] at hle
  exact ne_of_lt (hle.trans_lt ENNReal.ofReal_lt_top)

/-- Real-valued parameters for the finite Poisson sum are exactly additive. -/
theorem sum_uniformUnit_real_preimage (m : ℕ) (B : Set ℝ) (hB : MeasurableSet B)
    (hbound : B ⊆ Iio (m : ℝ)) :
    (∑ n ∈ Finset.range m, uniformUnit.real ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B)) =
      positiveVolume.real B := by
  have h := congrArg ENNReal.toReal (sum_uniformUnit_preimage m B hB hbound)
  rw [ENNReal.toReal_sum (fun n _ => measure_ne_top _ _)] at h
  exact h

/-- A bounded time-window count, formed from actual strip window counts. -/
def boundedWindowCount {J : Type*} (j : J) (m : ℕ) (B : Set ℝ) (S T : ℝ)
    (ω : MarkedNoise.Sample J) : ℕ :=
  ∑ n ∈ Finset.range m,
    windowCount ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B) S T (ω (j, n))

theorem measurable_boundedWindowCount {J : Type*} (j : J) (m : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B) (S T : ℝ) :
    Measurable (boundedWindowCount j m B S T) := by
  apply Finset.measurable_sum
  intro n _
  exact (measurable_windowCount _ (hB.preimage (measurable_const.add measurable_id)) S T).comp
    (measurable_pi_apply (j, n))

theorem windowCount_eq_zero_of_le {m n : ℕ} (hmn : m ≤ n)
    (B : Set ℝ) (hB : B ⊆ Iio (m : ℝ)) (S T : ℝ) (ω : StripSample)
    (hmark : ∀ k, 0 ≤ ω.2 k) :
    windowCount ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B) S T ω = 0 := by
  rw [windowCount, clockCount_eq_zero_of_le hmn B hB T ω hmark,
    clockCount_eq_zero_of_le hmn B hB S ω hmark, Nat.sub_self]

theorem ae_coordinate_window_rectangle {J : Type*} (j : J) (n : ℕ) :
    ∀ᵐ ω ∂law J, ∀ S T : ℝ, 0 ≤ S → S ≤ T → ∀ B : Set ℝ, MeasurableSet B →
      stripMeasure n (ω (j, n)) (Ioc S T ×ˢ B) =
        (windowCount ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B) S T (ω (j, n)) : ℝ≥0∞) := by
  have h := ae_stripMeasure_window_rectangle
  rw [← strip_map J (j, n)] at h
  filter_upwards [ae_of_ae_map (measurable_pi_apply (j, n)).aemeasurable h] with ω hω
  exact hω n

/-- All bounded window rectangles are identified on one probability-one event. -/
theorem ae_countingMeasure_eq_boundedWindowCount {J : Type*} (j : J) :
    ∀ᵐ ω ∂law J, ∀ m : ℕ, ∀ B : Set ℝ, MeasurableSet B → B ⊆ Iio (m : ℝ) →
      ∀ S T : ℝ, 0 ≤ S → S ≤ T →
        countingMeasure j ω (Ioc S T ×ˢ B) =
          (boundedWindowCount j m B S T ω : ℝ≥0∞) := by
  have h := ae_all_iff.mpr (fun n : ℕ => ae_coordinate_window_rectangle j n)
  filter_upwards [h, ae_nonnegative_marks j] with ω hcount hmark
  intro m B hB hbound S T hS hST
  rw [countingMeasure_eq_sum_strips, Measure.sum_apply _ (measurableSet_Ioc.prod hB)]
  have he (n : ℕ) := hcount n S T hS hST B hB
  simp_rw [he]
  rw [tsum_eq_sum (s := Finset.range m) (fun n hn => by
    have hmn : m ≤ n := Nat.le_of_not_gt (by simpa using hn)
    rw [windowCount_eq_zero_of_le hmn B hbound S T (ω (j, n)) (hmark n)]
    exact Nat.cast_zero)]
  simp only [boundedWindowCount, Nat.cast_sum]

end CarryingCapacity.MarkedBoundedCounts
