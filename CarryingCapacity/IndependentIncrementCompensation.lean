import CarryingCapacity.MarkedCountingKernel
import CarryingCapacity.PredictableStoppingMask

/-!
# Predictable compensation from independent future counts and intensity

This theorem is on an arbitrary filtered probability space. Its inputs are
the unweighted intensity of a genuine random-measure kernel and independence
of each bounded future rectangle count from the whole past. The weighted
rectangle identity and then full predictable compensation are proved. No
compensator identity or expected coupling inequality is supplied as a premise.

The s-finite-kernel hypothesis is needed for genuine Campbell/Fubini measure
construction. In applications to Poisson random measures it is supplied by
their locally finite counting-measure realization.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter MeasurableSpace
open scoped Classical ENNReal BigOperators

namespace CarryingCapacity.IndependentIncrementCompensation
open PredictableSets MarkedIntensity

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  (F : Filtration ℝ mΩ) (P : Measure Ω) [IsProbabilityMeasure P]
  (K : Kernel Ω (ℝ × ℝ)) [IsSFiniteKernel K]

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

/-- Unweighted intensity, a first-moment property of the random measure. -/
def HasIntensity : Prop := ∀ S : Set (ℝ × ℝ), MeasurableSet S →
  (∫⁻ ω, K ω S ∂P) = (positiveVolume.prod positiveVolume) S

/-- Each future bounded-rectangle count is independent of the entire past
sigma algebra, not merely of individual past coordinates. -/
def FutureCountsIndependent : Prop := ∀ (s t : ℝ) (m : ℕ) (B : Set ℝ),
  0 ≤ s → s ≤ t → MeasurableSet B → B ⊆ Iio (m : ℝ) →
  Indep (F s) (MeasurableSpace.comap
    (fun ω => K ω (Ioc s t ×ˢ B)) inferInstance) P

variable (hmean : HasIntensity P K) (hind : FutureCountsIndependent F P K)

omit [IsProbabilityMeasure P] [IsSFiniteKernel K] in
include hmean hind in
/-- Independent future counts factor against every nonnegative past
coefficient. This elementary compensation identity is derived, not assumed. -/
theorem lintegral_past_mul_count (s t : ℝ) (m : ℕ) (B : Set ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) (hB : MeasurableSet B) (hb : B ⊆ Iio (m : ℝ))
    (H : Ω → ℝ≥0∞) (hH : Measurable[F s] H) :
    (∫⁻ ω, H ω * K ω (Ioc s t ×ˢ B) ∂P) =
      (∫⁻ ω, H ω ∂P) * (positiveVolume.prod positiveVolume) (Ioc s t ×ˢ B) := by
  have hi : IndepFun H (fun ω => K ω (Ioc s t ×ˢ B)) P :=
    indep_of_indep_of_le_left (hind s t m B hs hst hB hb) hH.comap_le
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hH.mono (F.le s) le_rfl).aemeasurable
    (K.measurable_coe (measurableSet_Ioc.prod hB)).aemeasurable hi,
    hmean _ (measurableSet_Ioc.prod hB)]

include hmean hind in
theorem campbell_eq_product_on_rectangles (S : Set (Ω × (ℝ × ℝ)))
    (hS : S ∈ rectangles F) :
    (P ⊗ₘ K) S = P.prod (positiveVolume.prod positiveVolume) S := by
  rcases hS with ⟨s, t, A, B, m, hs, hA, hB, hb, rfl⟩
  by_cases hst : s ≤ t
  · have hAm : MeasurableSet A := F.le s A hA
    rw [rectangle, Measure.compProd_apply_prod hAm (measurableSet_Ioc.prod hB),
      Measure.prod_prod]
    rw [← lintegral_indicator hAm]
    have he : A.indicator (fun ω => K ω (Ioc s t ×ˢ B)) =
        fun ω => A.indicator (fun _ => (1 : ℝ≥0∞)) ω * K ω (Ioc s t ×ˢ B) := by
      funext ω
      by_cases hω : ω ∈ A <;> simp [hω]
    rw [he, lintegral_past_mul_count F P K hmean hind s t m B hs hst hB hb
      _ (measurable_const.indicator hA)]
    congr 1
    simpa only [Pi.one_apply] using lintegral_indicator_one hAm
  · have he : rectangle A s t B = ∅ := by
      simp [rectangle, Ioc_eq_empty_of_le (le_of_not_ge hst)]
    simp [he]

/-- Finite boxes exhaust the positive-time region. -/
def box (T : ℝ) (m : ℕ) : Set (Ω × (ℝ × ℝ)) := rectangle univ 0 T (Iio (m : ℝ))

theorem box_mem_rectangles (T : ℝ) (m : ℕ) : box (Ω := Ω) T m ∈ rectangles F :=
  ⟨0, T, univ, Iio (m : ℝ), m, le_rfl, MeasurableSet.univ,
    measurableSet_Iio, Subset.rfl, rfl⟩

theorem measurableSet_box_predictable (T : ℝ) (m : ℕ) :
    MeasurableSet[predictable F] (box (Ω := Ω) T m) :=
  measurableSet_generateFrom (box_mem_rectangles F T m)

theorem product_box_ne_top (T : ℝ) (m : ℕ) :
    P.prod (positiveVolume.prod positiveVolume) (box (Ω := Ω) T m) ≠ ⊤ := by
  have hle : P.prod (positiveVolume.prod positiveVolume) (box (Ω := Ω) T m) ≤
      ENNReal.ofReal T * ENNReal.ofReal (m : ℝ) := by
    calc
      _ ≤ P.prod (positiveVolume.prod positiveVolume)
          (univ ×ˢ (Iic T ×ˢ Iic (m : ℝ))) :=
        measure_mono (Set.prod_mono Subset.rfl
          (Set.prod_mono Ioc_subset_Iic_self Iio_subset_Iic_self))
      _ = _ := by
        rw [Measure.prod_prod, measure_univ, one_mul, Measure.prod_prod,
          positiveVolume_Iic, positiveVolume_Iic]
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hle

include hmean hind in
theorem trim_restrict_box_eq (T : ℝ) (m : ℕ) :
    ((P ⊗ₘ K).restrict (box (Ω := Ω) T m)).trim (predictable_le F) =
      ((P.prod (positiveVolume.prod positiveVolume)).restrict (box (Ω := Ω) T m)).trim
        (predictable_le F) := by
  have hfinite : (P ⊗ₘ K) (box (Ω := Ω) T m) ≠ ⊤ := by
    rw [campbell_eq_product_on_rectangles F P K hmean hind _ (box_mem_rectangles F T m)]
    exact product_box_ne_top P T m
  letI : IsFiniteMeasure ((P ⊗ₘ K).restrict (box (Ω := Ω) T m)) :=
    isFiniteMeasure_restrict.mpr hfinite
  apply trim_eq_of_rectangles
  · intro S hS
    have hm := predictable_le F S (measurableSet_generateFrom hS)
    rw [Measure.restrict_apply hm, Measure.restrict_apply hm]
    rcases (S ∩ box (Ω := Ω) T m).eq_empty_or_nonempty with he | he
    · simp [he]
    · exact campbell_eq_product_on_rectangles F P K hmean hind _
        (isPiSystem_rectangles F _ hS _ (box_mem_rectangles F T m) he)
  · simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact campbell_eq_product_on_rectangles F P K hmean hind _ (box_mem_rectangles F T m)

omit mΩ in
theorem iUnion_box : (⋃ n : ℕ, box (Ω := Ω) (n : ℝ) n) =
    {p : Ω × (ℝ × ℝ) | 0 < p.2.1} := by
  ext p
  simp only [mem_iUnion, box, rectangle, mem_prod, mem_univ, true_and,
    mem_Ioc, mem_Iio, mem_setOf_eq]
  constructor
  · rintro ⟨n, ⟨hpos, _⟩, _⟩
    exact hpos
  · intro hp
    obtain ⟨n, hn⟩ := exists_nat_gt (max p.2.1 p.2.2)
    exact ⟨n, ⟨hp, ((le_max_left _ _).trans_lt hn).le⟩,
      (le_max_right _ _).trans_lt hn⟩

include hmean hind in
/-- The Campbell measure and product intensity have the same predictable
restriction, proved from primitive independent counts and mean intensity. -/
theorem trim_campbell_eq_product :
    (P ⊗ₘ K).trim (predictable_le F) =
      (P.prod (positiveVolume.prod positiveVolume)).trim (predictable_le F) := by
  let R : Set (Ω × (ℝ × ℝ)) := {p | 0 < p.2.1}
  have hRm : MeasurableSet[predictable F] R := by
    rw [show R = ⋃ n : ℕ, box (Ω := Ω) n n from iUnion_box.symm]
    exact MeasurableSet.iUnion (fun n => measurableSet_box_predictable F n n)
  have hcomp : Rᶜ = univ ×ˢ (Iic (0 : ℝ) ×ˢ univ) := by ext p; simp [R]
  have hzeroK : (P ⊗ₘ K) Rᶜ = 0 := by
    rw [hcomp, Measure.compProd_apply_prod MeasurableSet.univ
      (measurableSet_Iic.prod MeasurableSet.univ), Measure.restrict_univ,
      hmean _ (measurableSet_Iic.prod MeasurableSet.univ), Measure.prod_prod,
      positiveVolume_Iic]
    simp
  have hzeroP : P.prod (positiveVolume.prod positiveVolume) Rᶜ = 0 := by
    rw [hcomp, Measure.prod_prod, Measure.prod_prod, positiveVolume_Iic]
    simp
  have hlocal : ∀ n : ℕ, ((P ⊗ₘ K).trim (predictable_le F)).restrict (box (Ω := Ω) n n) =
      ((P.prod (positiveVolume.prod positiveVolume)).trim (predictable_le F)).restrict
        (box (Ω := Ω) n n) := by
    intro n
    rw [restrict_trim _ _ (measurableSet_box_predictable F n n),
      restrict_trim _ _ (measurableSet_box_predictable F n n)]
    exact trim_restrict_box_eq F P K hmean hind n n
  have he := Measure.restrict_iUnion_congr.mpr hlocal
  rw [iUnion_box] at he
  have hmemK : ∀ᵐ p ∂(P ⊗ₘ K).trim (predictable_le F), p ∈ R := by
    change (P ⊗ₘ K).trim (predictable_le F) Rᶜ = 0
    rw [trim_measurableSet_eq _ hRm.compl, hzeroK]
  have hmemP : ∀ᵐ p ∂(P.prod (positiveVolume.prod positiveVolume)).trim (predictable_le F), p ∈ R := by
    change (P.prod (positiveVolume.prod positiveVolume)).trim (predictable_le F) Rᶜ = 0
    rw [trim_measurableSet_eq _ hRm.compl, hzeroP]
  rw [Measure.restrict_eq_self_of_ae_mem hmemK,
    Measure.restrict_eq_self_of_ae_mem hmemP] at he
  exact he

include hmean hind in
/-- Nonnegative predictable compensation on an arbitrary filtered
probability space. Both sides are genuine extended integrals; finiteness is
not assumed. -/
theorem compensation_nonnegative (f : Ω × (ℝ × ℝ) → ℝ≥0∞)
    (hf : Measurable[predictable F] f) :
    (∫⁻ ω, ∫⁻ q, f (ω,q) ∂K ω ∂P) =
      ∫⁻ ω, ∫⁻ q, f (ω,q) ∂positiveVolume.prod positiveVolume ∂P := by
  have hm : Measurable f := hf.mono (predictable_le _) le_rfl
  calc
    _ = ∫⁻ p, f p ∂P ⊗ₘ K := (Measure.lintegral_compProd hm).symm
    _ = ∫⁻ p, f p ∂(P ⊗ₘ K).trim (predictable_le F) := (lintegral_trim _ hf).symm
    _ = ∫⁻ p, f p ∂(P.prod (positiveVolume.prod positiveVolume)).trim (predictable_le F) := by
      rw [trim_campbell_eq_product F P K hmean hind]
    _ = ∫⁻ p, f p ∂P.prod (positiveVolume.prod positiveVolume) := lintegral_trim _ hf
    _ = _ := lintegral_prod f hm.aemeasurable

include hmean hind in
/-- Compensation through any common stopping time, retaining its jump. -/
theorem compensation_stopped_nonnegative (τ : Ω → ℝ≥0∞)
    (hτ : ∀ s : ℝ, 0 ≤ s → MeasurableSet[F s] {ω | τ ω ≤ ENNReal.ofReal s})
    (f : Ω × (ℝ × ℝ) → ℝ≥0∞) (hf : Measurable[predictable F] f) :
    (∫⁻ ω, ∫⁻ q, PredictableStoppingMask.mask τ f (ω,q) ∂K ω ∂P) =
      ∫⁻ ω, ∫⁻ q, PredictableStoppingMask.mask τ f (ω,q)
        ∂positiveVolume.prod positiveVolume ∂P :=
  compensation_nonnegative F P K hmean hind _
    (PredictableStoppingMask.measurable_mask F τ hτ f hf)

end CarryingCapacity.IndependentIncrementCompensation
