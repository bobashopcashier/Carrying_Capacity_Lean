import CarryingCapacity.CommonMarkedPastIndependence
import CarryingCapacity.CommonInitialStopping

/-!
# Future marked counts with arbitrary independent initialization

The actual initial-record/noise product law preserves independence between
future bounded marked counts and the entire initial record together with the
observed past noise. The exact existing product filtration is identified with
this observation, and independence survives its ambient-null augmentation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CarryingCapacity.InitialMarkedPastIndependence

section Product

variable {A Ω P F : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
  [MeasurableSpace P] [MeasurableSpace F]

/-- Adjoining the whole independent first coordinate to an observation
preserves its independence from the future of the second coordinate. -/
theorem indepFun_initial_prod_observation
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (X : Ω → P) (hX : Measurable X) (Y : Ω → F) (hY : Measurable Y)
    (hnoise : IndepFun X Y ν) :
    IndepFun (fun p : A × Ω => (p.1, X p.2)) (fun p => Y p.2) (μ.prod ν) := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S T hS hT
  have hobs : Measurable (fun p : A × Ω => (p.1, X p.2)) :=
    measurable_fst.prodMk (hX.comp measurable_snd)
  have hfuture : Measurable (fun p : A × Ω => Y p.2) := hY.comp measurable_snd
  have hfuture_mass : μ.prod ν ((fun p : A × Ω => Y p.2) ⁻¹' T) = ν (Y ⁻¹' T) := by
    have heq : (fun p : A × Ω => Y p.2) ⁻¹' T = univ ×ˢ (Y ⁻¹' T) := by
      ext p
      simp
    rw [heq, Measure.prod_prod, measure_univ, one_mul]
  rw [hfuture_mass, Measure.prod_apply ((hS.preimage hobs).inter (hT.preimage hfuture)),
    Measure.prod_apply (hS.preimage hobs)]
  calc
    _ = ∫⁻ a, ν (X ⁻¹' (Prod.mk a ⁻¹' S)) * ν (Y ⁻¹' T) ∂μ := by
      apply lintegral_congr
      intro a
      exact hnoise.measure_inter_preimage_eq_mul _ _
        (hS.preimage measurable_prodMk_left) hT
    _ = _ := lintegral_mul_const' _ _ (measure_ne_top ν _)

end Product

variable {A J : Type*} [MeasurableSpace A]

/-- The actual product history records the entire initial record and arrived marks. -/
def view (s : ℝ) (p : CommonInitialNoise.Sample A J) :
    A × CommonNoiseFiltration.EventView J :=
  (p.1, CommonNoiseFiltration.view s p.2)

theorem measurable_view (s : ℝ) : Measurable (view (A := A) (J := J) s) :=
  measurable_fst.prodMk ((CommonNoiseFiltration.measurable_view s).comp measurable_snd)

/-- This is exactly the existing product filtration, without extra information. -/
theorem comap_view_eq_filtration (s : ℝ) :
    MeasurableSpace.comap (view (A := A) (J := J) s) inferInstance =
      CommonInitialNoise.filtration A J s := by
  change MeasurableSpace.comap (view s)
      ((inferInstance : MeasurableSpace A).prod
        (inferInstance : MeasurableSpace (CommonNoiseFiltration.EventView J))) =
    (inferInstance : MeasurableSpace A).prod
      (MeasurableSpace.comap (CommonNoiseFiltration.view s) inferInstance)
  simp only [MeasurableSpace.prod, MeasurableSpace.comap_sup,
    MeasurableSpace.comap_comp, Function.comp_def, view]

theorem measurable_view_at (s : ℝ) :
    Measurable[CommonInitialNoise.filtration A J s] (view s) := by
  rw [← comap_view_eq_filtration]
  exact comap_measurable _

/-- Actual bounded future strip counts are measurable on the product sample space. -/
theorem measurable_boundedWindowCount (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (s t : ℝ) :
    Measurable (fun p : CommonInitialNoise.Sample A J =>
      MarkedBoundedCounts.boundedWindowCount j m B s (s + t) p.2) :=
  (MarkedBoundedCounts.measurable_boundedWindowCount j m B hB s (s + t)).comp measurable_snd

/-- Measurability uses evaluation of the genuine random measure on a Borel rectangle. -/
theorem measurable_countingMeasure_windowrectangle (j : J) (B : Set ℝ)
    (hB : MeasurableSet B) (s t : ℝ) :
    Measurable (fun p : CommonInitialNoise.Sample A J =>
      MarkedNoise.countingMeasure j p.2 (Ioc s (s + t) ×ˢ B)) :=
  ((Measure.measurable_coe (measurableSet_Ioc.prod hB)).comp
    (MarkedNoise.measurable_countingMeasure j)).comp measurable_snd

theorem independent_view_boundedWindowCount
    (μ : Measure A) [IsProbabilityMeasure μ] (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IndepFun (view (A := A) (J := J) s)
      (fun p => MarkedBoundedCounts.boundedWindowCount j m B s (s + t) p.2)
      (CommonInitialNoise.law μ J) :=
  indepFun_initial_prod_observation μ (MarkedNoise.law J)
    (CommonNoiseFiltration.view s) (CommonNoiseFiltration.measurable_view s)
    (MarkedBoundedCounts.boundedWindowCount j m B s (s + t))
    (MarkedBoundedCounts.measurable_boundedWindowCount j m B hB s (s + t))
    (CommonMarkedPastIndependence.independent_view_boundedWindowCount j m B hB s t hs ht)

theorem independent_view_countingMeasure_windowrectangle
    (μ : Measure A) [IsProbabilityMeasure μ] (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IndepFun (view (A := A) (J := J) s)
      (fun p => MarkedNoise.countingMeasure j p.2 (Ioc s (s + t) ×ˢ B))
      (CommonInitialNoise.law μ J) :=
  indepFun_initial_prod_observation μ (MarkedNoise.law J)
    (CommonNoiseFiltration.view s) (CommonNoiseFiltration.measurable_view s)
    (fun ω => MarkedNoise.countingMeasure j ω (Ioc s (s + t) ×ˢ B))
    ((Measure.measurable_coe (measurableSet_Ioc.prod hB)).comp
      (MarkedNoise.measurable_countingMeasure j))
    (CommonMarkedPastIndependence.independent_view_countingMeasure_windowrectangle
      j m B hB hbound s t hs ht)

/-- The exact raw initial-plus-marked-history filtration is independent of future counts. -/
theorem independent_filtration_boundedWindowCount
    (μ : Measure A) [IsProbabilityMeasure μ] (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Indep (CommonInitialNoise.filtration A J s)
      (MeasurableSpace.comap (fun p : CommonInitialNoise.Sample A J =>
        MarkedBoundedCounts.boundedWindowCount j m B s (s + t) p.2) inferInstance)
      (CommonInitialNoise.law μ J) := by
  rw [← comap_view_eq_filtration]
  exact independent_view_boundedWindowCount μ j m B hB s t hs ht

theorem independent_filtration_countingMeasure_windowrectangle
    (μ : Measure A) [IsProbabilityMeasure μ] (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Indep (CommonInitialNoise.filtration A J s)
      (MeasurableSpace.comap (fun p : CommonInitialNoise.Sample A J =>
        MarkedNoise.countingMeasure j p.2 (Ioc s (s + t) ×ˢ B)) inferInstance)
      (CommonInitialNoise.law μ J) := by
  rw [← comap_view_eq_filtration]
  exact independent_view_countingMeasure_windowrectangle μ j m B hB hbound s t hs ht

/-- Null augmentation preserves independence for the same actual bounded count. -/
theorem independent_completedAt_boundedWindowCount
    (μ : Measure A) [IsProbabilityMeasure μ] (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Indep (CommonInitialStopping.completedAt μ J s)
      (MeasurableSpace.comap (fun p : CommonInitialNoise.Sample A J =>
        MarkedBoundedCounts.boundedWindowCount j m B s (s + t) p.2) inferInstance)
      (CommonInitialStopping.completedLaw μ J) := by
  apply NullAugmentedIndependence.indep_completion_iff.mpr
  exact NullAugmentedIndependence.indep_augment_left
    (independent_filtration_boundedWindowCount μ j m B hB s t hs ht)

/-- The genuine future rectangle mass is independent of the completed product history. -/
theorem independent_completedAt_countingMeasure_windowrectangle
    (μ : Measure A) [IsProbabilityMeasure μ] (j : J) (m : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hbound : B ⊆ Iio (m : ℝ))
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Indep (CommonInitialStopping.completedAt μ J s)
      (MeasurableSpace.comap (fun p : CommonInitialNoise.Sample A J =>
        MarkedNoise.countingMeasure j p.2 (Ioc s (s + t) ×ˢ B)) inferInstance)
      (CommonInitialStopping.completedLaw μ J) := by
  apply NullAugmentedIndependence.indep_completion_iff.mpr
  exact NullAugmentedIndependence.indep_augment_left
    (independent_filtration_countingMeasure_windowrectangle μ j m B hB hbound s t hs ht)

end CarryingCapacity.InitialMarkedPastIndependence
