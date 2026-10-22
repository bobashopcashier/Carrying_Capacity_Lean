import CarryingCapacity.PredictableSets
import CarryingCapacity.MarkedElementaryCompensation

/-!
# Predictable compensation for the actual common marked counting measure

The Campbell measure retains the original sample and each actual marked point.
It is a countable sum of genuine image measures. Elementary predictable
rectangle identities come from the proved past independence and deterministic
intensity. Finite-box measure uniqueness then extends those identities to the
generated predictable sigma algebra.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter MeasurableSpace
open scoped ENNReal BigOperators

namespace CarryingCapacity.PredictableCompensation
open MarkedNoise MarkedIntensity PredictableSets

variable {J : Type*}

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

abbrev SamplePoint (J : Type*) := MarkedNoise.Sample J × (ℝ × ℝ)

/-- The actual sample-marked-point Campbell measure. -/
def campbell (j : J) : Measure (SamplePoint J) :=
  Measure.sum (fun p : ℕ × ℕ =>
    (law J).map (fun ω => (ω, point j ω p)))

/-- The deterministic product measure on samples, time and height. -/
def productIntensity (J : Type*) : Measure (SamplePoint J) :=
  (law J).prod (positiveVolume.prod positiveVolume)

theorem lintegral_campbell (j : J) (f : SamplePoint J → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂campbell j) =
      ∫⁻ ω, ∫⁻ p, f (ω, p) ∂countingMeasure j ω ∂law J := by
  rw [campbell, lintegral_sum_measure]
  have he : (∑' p : ℕ × ℕ, ∫⁻ x, f x ∂(law J).map (fun ω => (ω, point j ω p))) =
      ∑' p : ℕ × ℕ, ∫⁻ ω, f (ω, point j ω p) ∂law J := by
    apply tsum_congr
    intro p
    exact lintegral_map hf (measurable_id.prodMk (measurable_point j p))
  rw [he]
  have hm (p : ℕ × ℕ) : Measurable (fun ω => f (ω, point j ω p)) :=
    hf.comp (measurable_id.prodMk (measurable_point j p))
  rw [← lintegral_tsum (μ := law J) (fun p => (hm p).aemeasurable)]
  apply lintegral_congr
  intro ω
  rw [countingMeasure, lintegral_sum_measure]
  simp only [lintegral_dirac]

theorem campbell_apply (j : J) (S : Set (SamplePoint J)) (hS : MeasurableSet S) :
    campbell j S = ∫⁻ ω, ∫⁻ p, S.indicator 1 (ω, p) ∂countingMeasure j ω ∂law J := by
  rw [← lintegral_indicator_one hS]
  exact lintegral_campbell j _ (measurable_const.indicator hS)

theorem campbell_rectangle (j : J) (A : Set (MarkedNoise.Sample J))
    (hA : MeasurableSet A) (s t : ℝ) (B : Set ℝ) (hB : MeasurableSet B) :
    campbell j (rectangle A s t B) =
      ∫⁻ ω, A.indicator (fun ω => countingMeasure j ω (Ioc s t ×ˢ B)) ω ∂law J := by
  rw [campbell_apply j (rectangle A s t B) (hA.prod (measurableSet_Ioc.prod hB))]
  apply lintegral_congr
  intro ω
  by_cases hω : ω ∈ A
  · have he : (fun p => (rectangle A s t B).indicator (1 : SamplePoint J → ℝ≥0∞) (ω,p)) =
        (Ioc s t ×ˢ B).indicator 1 := by
      funext p
      by_cases hp : p ∈ Ioc s t ×ˢ B
      · rw [Set.indicator_of_mem (show (ω,p) ∈ rectangle A s t B from ⟨hω,hp⟩),
          Set.indicator_of_mem hp]
        rfl
      · rw [Set.indicator_of_not_mem (show (ω,p) ∉ rectangle A s t B from fun h => hp h.2),
          Set.indicator_of_not_mem hp]
    rw [he, lintegral_indicator_one (measurableSet_Ioc.prod hB)]
    simp [hω]
  · have he : (fun p => (rectangle A s t B).indicator (1 : SamplePoint J → ℝ≥0∞) (ω,p)) = 0 := by
      funext p
      simp [rectangle, hω]
    rw [he, Set.indicator_of_not_mem hω]
    exact lintegral_zero

/-- The two actual measures agree on each generating predictable rectangle. -/
theorem campbell_eq_product_on_rectangles (j : J) (S : Set (SamplePoint J))
    (hS : S ∈ rectangles (CommonNoiseFiltration.filtration J)) :
    campbell j S = productIntensity J S := by
  rcases hS with ⟨s, t, A, B, m, hs, hA, hB, hb, rfl⟩
  by_cases hst : s ≤ t
  · rw [campbell_rectangle j A ((CommonNoiseFiltration.filtration J).le s _ hA) s t B hB,
      MarkedElementaryCompensation.lintegral_indicator_countingMeasure
        j m B hB hb s t hs hst A hA]
    exact (Measure.prod_prod A (Ioc s t ×ˢ B)).symm
  · have he : rectangle A s t B = ∅ := by
      simp [rectangle, Ioc_eq_empty_of_le (le_of_not_ge hst)]
    rw [he]
    simp

/-- A finite deterministic box, with an open upper height cutoff. -/
def box (J : Type*) (T : ℝ) (m : ℕ) : Set (SamplePoint J) :=
  rectangle univ 0 T (Iio (m : ℝ))

theorem box_mem_rectangles (J : Type*) (T : ℝ) (m : ℕ) :
    box J T m ∈ rectangles (CommonNoiseFiltration.filtration J) :=
  ⟨0, T, univ, Iio (m : ℝ), m, le_rfl, MeasurableSet.univ,
    measurableSet_Iio, Subset.rfl, rfl⟩

theorem measurableSet_box (J : Type*) (T : ℝ) (m : ℕ) : MeasurableSet (box J T m) :=
  MeasurableSet.univ.prod (measurableSet_Ioc.prod measurableSet_Iio)

theorem productIntensity_box_ne_top (J : Type*) (T : ℝ) (m : ℕ) :
    productIntensity J (box J T m) ≠ ∞ := by
  have hle : productIntensity J (box J T m) ≤
      ENNReal.ofReal T * ENNReal.ofReal (m : ℝ) := by
    calc
      _ ≤ productIntensity J (univ ×ˢ (Iic T ×ˢ Iic (m : ℝ))) :=
        measure_mono (Set.prod_mono Subset.rfl
          (Set.prod_mono Ioc_subset_Iic_self Iio_subset_Iic_self))
      _ = _ := by
        rw [productIntensity, Measure.prod_prod, measure_univ, one_mul,
          Measure.prod_prod, positiveVolume_Iic, positiveVolume_Iic]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hle

theorem campbell_box_ne_top (j : J) (T : ℝ) (m : ℕ) : campbell j (box J T m) ≠ ∞ := by
  rw [campbell_eq_product_on_rectangles j _ (box_mem_rectangles J T m)]
  exact productIntensity_box_ne_top J T m

/-- Both finite-box restrictions agree on the entire predictable sigma algebra. -/
theorem trim_restrict_box_eq (j : J) (T : ℝ) (m : ℕ) :
    ((campbell j).restrict (box J T m)).trim
        (predictable_le (CommonNoiseFiltration.filtration J)) =
      ((productIntensity J).restrict (box J T m)).trim
        (predictable_le (CommonNoiseFiltration.filtration J)) := by
  letI : IsFiniteMeasure ((campbell j).restrict (box J T m)) :=
    isFiniteMeasure_restrict.mpr (campbell_box_ne_top j T m)
  apply trim_eq_of_rectangles
  · intro S hS
    have hm := predictable_le (CommonNoiseFiltration.filtration J) S
      (measurableSet_generateFrom hS)
    rw [Measure.restrict_apply hm, Measure.restrict_apply hm]
    rcases (S ∩ box J T m).eq_empty_or_nonempty with he | he
    · simp [he]
    · exact campbell_eq_product_on_rectangles j _
        (isPiSystem_rectangles _ _ hS _ (box_mem_rectangles J T m) he)
  · simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact campbell_eq_product_on_rectangles j _ (box_mem_rectangles J T m)

/-- Forgetting the sample coordinate recovers the already proved intensity. -/
theorem campbell_univ_prod (j : J) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) :
    campbell j (univ ×ˢ S) = (positiveVolume.prod positiveVolume) S := by
  rw [campbell_apply j _ (MeasurableSet.univ.prod hS)]
  calc
    _ = ∫⁻ ω, countingMeasure j ω S ∂law J := by
      apply lintegral_congr
      intro ω
      have he : (fun p => (univ ×ˢ S).indicator (1 : SamplePoint J → ℝ≥0∞) (ω,p)) =
          S.indicator 1 := by
        funext p
        by_cases hp : p ∈ S
        · rw [Set.indicator_of_mem (show (ω,p) ∈ univ ×ˢ S from ⟨mem_univ _,hp⟩),
            Set.indicator_of_mem hp]
          rfl
        · rw [Set.indicator_of_not_mem (show (ω,p) ∉ univ ×ˢ S from fun h => hp h.2),
            Set.indicator_of_not_mem hp]
      rw [he, lintegral_indicator_one hS]
    _ = _ := lintegral_counting_set j S hS

def positiveRegion (J : Type*) : Set (SamplePoint J) :=
  {p | 0 < p.2.1}

theorem positiveRegion_compl (J : Type*) :
    (positiveRegion J)ᶜ = univ ×ˢ (Iic (0 : ℝ) ×ˢ univ) := by
  ext p
  simp [positiveRegion]

theorem campbell_positiveRegion_compl (j : J) : campbell j (positiveRegion J)ᶜ = 0 := by
  rw [positiveRegion_compl, campbell_univ_prod j _ (measurableSet_Iic.prod MeasurableSet.univ),
    Measure.prod_prod, positiveVolume_Iic]
  simp

theorem productIntensity_positiveRegion_compl (J : Type*) :
    productIntensity J (positiveRegion J)ᶜ = 0 := by
  rw [positiveRegion_compl, productIntensity, Measure.prod_prod,
    Measure.prod_prod, positiveVolume_Iic]
  simp

theorem iUnion_box (J : Type*) : (⋃ n : ℕ, box J (n : ℝ) n) = positiveRegion J := by
  ext p
  simp only [mem_iUnion, box, rectangle, mem_prod, mem_univ, true_and,
    mem_Ioc, mem_Iio, positiveRegion, mem_setOf_eq]
  constructor
  · rintro ⟨n, ⟨hpos, _⟩, _⟩
    exact hpos
  · intro hp
    obtain ⟨n, hn⟩ := exists_nat_gt (max p.2.1 p.2.2)
    exact ⟨n, ⟨hp, ((le_max_left _ _).trans_lt hn).le⟩,
      (le_max_right _ _).trans_lt hn⟩

theorem measurableSet_box_predictable (J : Type*) (T : ℝ) (m : ℕ) :
    MeasurableSet[predictable (CommonNoiseFiltration.filtration J)] (box J T m) :=
  measurableSet_generateFrom (box_mem_rectangles J T m)

theorem measurableSet_positiveRegion_predictable (J : Type*) :
    MeasurableSet[predictable (CommonNoiseFiltration.filtration J)] (positiveRegion J) := by
  rw [← iUnion_box]
  exact MeasurableSet.iUnion (fun n => measurableSet_box_predictable J n n)

/-- The genuine Campbell and deterministic product measures have equal
restrictions to the entire positive-time predictable sigma algebra. -/
theorem trim_campbell_eq_product (j : J) :
    (campbell j).trim (predictable_le (CommonNoiseFiltration.filtration J)) =
      (productIntensity J).trim (predictable_le (CommonNoiseFiltration.filtration J)) := by
  let hF := predictable_le (CommonNoiseFiltration.filtration J)
  have hlocal : ∀ n : ℕ, ((campbell j).trim hF).restrict (box J n n) =
      ((productIntensity J).trim hF).restrict (box J n n) := by
    intro n
    rw [restrict_trim hF _ (measurableSet_box_predictable J n n),
      restrict_trim hF _ (measurableSet_box_predictable J n n)]
    exact trim_restrict_box_eq j n n
  have he := Measure.restrict_iUnion_congr.mpr hlocal
  rw [iUnion_box] at he
  have hmemC : ∀ᵐ p ∂(campbell j).trim hF, p ∈ positiveRegion J := by
    change (campbell j).trim hF (positiveRegion J)ᶜ = 0
    rw [trim_measurableSet_eq hF (measurableSet_positiveRegion_predictable J).compl]
    exact campbell_positiveRegion_compl j
  have hmemP : ∀ᵐ p ∂(productIntensity J).trim hF, p ∈ positiveRegion J := by
    change (productIntensity J).trim hF (positiveRegion J)ᶜ = 0
    rw [trim_measurableSet_eq hF (measurableSet_positiveRegion_predictable J).compl]
    exact productIntensity_positiveRegion_compl J
  rw [Measure.restrict_eq_self_of_ae_mem hmemC,
    Measure.restrict_eq_self_of_ae_mem hmemP] at he
  exact he

/-- Nonnegative predictable compensation for the actual constructed marked
counting measure, with no boundedness or integrability assumption on f. -/
theorem compensation_nonnegative (j : J) (f : SamplePoint J → ℝ≥0∞)
    (hf : Measurable[predictable (CommonNoiseFiltration.filtration J)] f) :
    (∫⁻ ω, ∫⁻ p, f (ω,p) ∂countingMeasure j ω ∂law J) =
      ∫⁻ ω, ∫⁻ p, f (ω,p) ∂positiveVolume.prod positiveVolume ∂law J := by
  have hm : Measurable f := hf.mono (predictable_le _) le_rfl
  calc
    _ = ∫⁻ x, f x ∂campbell j := (lintegral_campbell j f hm).symm
    _ = ∫⁻ x, f x ∂(campbell j).trim (predictable_le _) := (lintegral_trim _ hf).symm
    _ = ∫⁻ x, f x ∂(productIntensity J).trim (predictable_le _) := by
      rw [trim_campbell_eq_product]
    _ = ∫⁻ x, f x ∂productIntensity J := lintegral_trim _ hf
    _ = _ := lintegral_prod f hm.aemeasurable

end CarryingCapacity.PredictableCompensation
