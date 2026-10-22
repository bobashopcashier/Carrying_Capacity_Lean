import CarryingCapacity.MarkedBoundedCounts

/-!
# Real counts, integrability, and means of genuine marked rectangles

The real variables are obtained from evaluations of the actual random counting
measure. Finite height bounds give almost-sure finiteness and genuine
integrability, so conversion from extended nonnegative reals does not hide
infinite counts. Campbell's identity supplies the first moments.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace CarryingCapacity.MarkedCountMoments
open MarkedNoise MarkedIntensity MarkedBoundedCounts

variable {J : Type*}

local instance : SFinite positiveVolume := by
  unfold positiveVolume
  infer_instance

def realCount (j : J) (B : Set ℝ) (T : ℝ) (ω : MarkedNoise.Sample J) : ℝ :=
  (countingMeasure j ω (Iic T ×ˢ B)).toReal

def realWindowCount (j : J) (B : Set ℝ) (S T : ℝ) (ω : MarkedNoise.Sample J) : ℝ :=
  (countingMeasure j ω (Ioc S T ×ˢ B)).toReal

theorem realCount_nonneg (j : J) (B : Set ℝ) (T : ℝ) (ω : MarkedNoise.Sample J) :
    0 ≤ realCount j B T ω := ENNReal.toReal_nonneg

theorem realWindowCount_nonneg (j : J) (B : Set ℝ) (S T : ℝ) (ω : MarkedNoise.Sample J) :
    0 ≤ realWindowCount j B S T ω := ENNReal.toReal_nonneg

theorem measurable_countingMass (j : J) (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) :
    Measurable (fun ω : MarkedNoise.Sample J => countingMeasure j ω A) :=
  (Measure.measurable_coe hA).comp (measurable_countingMeasure j)

theorem measurable_realCount (j : J) (B : Set ℝ) (hB : MeasurableSet B) (T : ℝ) :
    Measurable (realCount j B T) :=
  (measurable_countingMass j _ (measurableSet_Iic.prod hB)).ennreal_toReal

theorem measurable_realWindowCount (j : J) (B : Set ℝ) (hB : MeasurableSet B) (S T : ℝ) :
    Measurable (realWindowCount j B S T) :=
  (measurable_countingMass j _ (measurableSet_Ioc.prod hB)).ennreal_toReal

theorem positiveVolume_Ioc (S T : ℝ) (hS : 0 ≤ S) :
    positiveVolume (Ioc S T) = ENNReal.ofReal (T - S) := by
  rw [positiveVolume, Measure.restrict_apply measurableSet_Ioc]
  have he : Ioc S T ∩ Ici 0 = Ioc S T := by
    apply Set.inter_eq_left.mpr
    intro x hx
    exact hS.trans hx.1.le
  rw [he, Real.volume_Ioc]

theorem lintegral_counting_prefix (j : J) (B : Set ℝ) (hB : MeasurableSet B) (T : ℝ) :
    (∫⁻ ω, countingMeasure j ω (Iic T ×ˢ B) ∂law J) =
      ENNReal.ofReal T * positiveVolume B := by
  rw [lintegral_counting_set j _ (measurableSet_Iic.prod hB),
    Measure.prod_prod, positiveVolume_Iic]

theorem lintegral_counting_window (j : J) (B : Set ℝ) (hB : MeasurableSet B)
    (S T : ℝ) (hS : 0 ≤ S) :
    (∫⁻ ω, countingMeasure j ω (Ioc S T ×ˢ B) ∂law J) =
      ENNReal.ofReal (T - S) * positiveVolume B := by
  rw [lintegral_counting_set j _ (measurableSet_Ioc.prod hB),
    Measure.prod_prod, positiveVolume_Ioc S T hS]

theorem ae_counting_prefix_lt_top (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ)) (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ ω ∂law J, countingMeasure j ω (Iic T ×ˢ B) < ∞ := by
  filter_upwards [ae_countingMeasure_eq_boundedCount j] with ω hω
  rw [hω m B hB hbound T hT]
  exact ENNReal.natCast_lt_top _

theorem ae_counting_window_lt_top (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (S T : ℝ) (hS : 0 ≤ S) (hST : S ≤ T) :
    ∀ᵐ ω ∂law J, countingMeasure j ω (Ioc S T ×ˢ B) < ∞ := by
  filter_upwards [ae_countingMeasure_eq_boundedWindowCount j] with ω hω
  rw [hω m B hB hbound S T hS hST]
  exact ENNReal.natCast_lt_top _

theorem integrable_realCount (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ)) (T : ℝ) :
    Integrable (realCount j B T) (law J) := by
  apply integrable_toReal_of_lintegral_ne_top
    (measurable_countingMass j _ (measurableSet_Iic.prod hB)).aemeasurable
  rw [lintegral_counting_prefix j B hB T]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (positiveVolume_ne_top_of_bounded m B hbound)

theorem integral_realCount (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ)) (T : ℝ) (hT : 0 ≤ T) :
    (∫ ω, realCount j B T ω ∂law J) = T * positiveVolume.real B := by
  simp only [realCount]
  rw [integral_toReal
    (measurable_countingMass j _ (measurableSet_Iic.prod hB)).aemeasurable
    (ae_counting_prefix_lt_top j m B hB hbound T hT),
    lintegral_counting_prefix j B hB T, ENNReal.toReal_mul, ENNReal.toReal_ofReal hT]
  rfl

theorem integrable_realWindowCount (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ)) (S T : ℝ) (hS : 0 ≤ S) :
    Integrable (realWindowCount j B S T) (law J) := by
  apply integrable_toReal_of_lintegral_ne_top
    (measurable_countingMass j _ (measurableSet_Ioc.prod hB)).aemeasurable
  rw [lintegral_counting_window j B hB S T hS]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (positiveVolume_ne_top_of_bounded m B hbound)

theorem integral_realWindowCount (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (S T : ℝ) (hS : 0 ≤ S) (hST : S ≤ T) :
    (∫ ω, realWindowCount j B S T ω ∂law J) = (T - S) * positiveVolume.real B := by
  simp only [realWindowCount]
  rw [integral_toReal
    (measurable_countingMass j _ (measurableSet_Ioc.prod hB)).aemeasurable
    (ae_counting_window_lt_top j m B hB hbound S T hS hST),
    lintegral_counting_window j B hB S T hS,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hST)]
  rfl

/-- Prefix differences agree with actual window masses wherever the larger prefix is finite. -/
theorem realCount_sub_eq_realWindowCount_of_finite (j : J) (B : Set ℝ)
    (hB : MeasurableSet B) (S T : ℝ) (hST : S ≤ T) (ω : MarkedNoise.Sample J)
    (hfin : countingMeasure j ω (Iic T ×ˢ B) ≠ ∞) :
    realCount j B T ω - realCount j B S ω = realWindowCount j B S T ω := by
  have he : Ioc S T ×ˢ B = (Iic T ×ˢ B) \ (Iic S ×ˢ B) := by
    ext p
    simp only [Set.mem_prod, Set.mem_Ioc, Set.mem_diff, Set.mem_Iic]
    constructor
    · rintro ⟨⟨h1, h2⟩, hB⟩
      exact ⟨⟨h2, hB⟩, fun h => (not_le_of_gt h1) h.1⟩
    · rintro ⟨⟨h2, hB⟩, h⟩
      exact ⟨⟨lt_of_not_ge (fun h1 => h ⟨h1, hB⟩), h2⟩, hB⟩
  have hsub : Iic S ×ˢ B ⊆ Iic T ×ˢ B := fun _ h => ⟨h.1.trans hST, h.2⟩
  have hle := measure_mono (μ := countingMeasure j ω) hsub
  have hfinS : countingMeasure j ω (Iic S ×ˢ B) ≠ ∞ := ne_top_of_le_ne_top hfin hle
  rw [realWindowCount, he, measure_diff hsub (measurableSet_Iic.prod hB).nullMeasurableSet hfinS,
    ENNReal.toReal_sub_of_le hle hfin]
  rfl

theorem ae_realCount_sub_eq_realWindowCount (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (S T : ℝ) (hS : 0 ≤ S) (hST : S ≤ T) :
    (fun ω => realCount j B T ω - realCount j B S ω) =ᵐ[law J]
      realWindowCount j B S T := by
  filter_upwards [ae_counting_prefix_lt_top j m B hB hbound T (hS.trans hST)] with ω hω
  exact realCount_sub_eq_realWindowCount_of_finite j B hB S T hST ω hω.ne

end CarryingCapacity.MarkedCountMoments
