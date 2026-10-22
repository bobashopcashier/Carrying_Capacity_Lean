import CarryingCapacity.MarkedNoise
import CarryingCapacity.PoissonMoments

/-!
# Intensity of the actual shared marked noise

The expectation of the random counting measure is computed from its actual
independent clock and mark coordinates. These deterministic-integrand intensity
identities do not assert a predictable compensator or a full marked Poisson law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

namespace CarryingCapacity.MarkedIntensity
open CountableJumpProcess FrozenProcess PoissonMoments

/-- Expected mass of a random Dirac measure is the actual image probability. -/
theorem lintegral_dirac_eval {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (f : Ω → X) (hf : Measurable f) (s : Set X) (hs : MeasurableSet s) :
    (∫⁻ ω, Measure.dirac (f ω) s ∂P) = P (f ⁻¹' s) := by
  simp only [Measure.dirac_apply' _ hs]
  have he : (fun ω => s.indicator (1 : X → ℝ≥0∞) (f ω)) =
      (f ⁻¹' s).indicator 1 := by
    funext ω
    exact (Set.indicator_comp_right f).symm
  rw [he, lintegral_indicator_one (hf hs)]

theorem arrivalCountingMeasure_Iic {ω : ClockSpace}
    (hfin : ∀ T : ℝ, {n : ℕ | arrival ω n ≤ T}.Finite) (T : ℝ) :
    arrivalCountingMeasure ω (Iic T) = (proposalCount ω T : ℝ≥0∞) := by
  have hf : {n : ℕ | arrival ω (n + 1) ≤ T}.Finite :=
    Set.Finite.preimage (f := fun n : ℕ => n + 1)
      (fun _ _ _ _ h => Nat.succ_injective h) (hfin T)
  rw [arrivalCountingMeasure_eq_map, Measure.map_apply measurable_from_nat measurableSet_Iic]
  change Measure.count {n : ℕ | arrival ω (n + 1) ≤ T} = _
  rw [Measure.count_apply_finite _ hf, proposalCount, Set.ncard_eq_toFinset_card _ hf]

/-- The expected unmarked number of proposals on a bounded past interval. -/
theorem lintegral_arrivalCountingMeasure_Iic (r : ℝ) (hr : 0 < r) (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, arrivalCountingMeasure ω (Iic T) ∂waitingTimeLaw r hr) = ENNReal.ofReal (r * T) := by
  rw [← lintegral_proposalCount r hr T hT]
  apply lintegral_congr_ae
  filter_upwards [ae_locally_finite r hr] with ω hω
  exact arrivalCountingMeasure_Iic hω.2 T

/-- The sum of arrival-event probabilities is derived from the count moment. -/
theorem tsum_arrival_probabilities (r : ℝ) (hr : 0 < r) (T : ℝ) (hT : 0 ≤ T) :
    (∑' k : ℕ, waitingTimeLaw r hr {ω | arrival ω (k + 1) ≤ T}) =
      ENNReal.ofReal (r * T) := by
  rw [← lintegral_arrivalCountingMeasure_Iic r hr T hT]
  simp only [arrivalCountingMeasure, Measure.sum_apply _ measurableSet_Iic]
  have hm (k : ℕ) : Measurable (fun ω => Measure.dirac (arrival ω (k + 1)) (Iic T)) :=
    (Measure.measurable_coe measurableSet_Iic).comp
      (Measure.measurable_dirac.comp (measurable_arrival (k + 1)))
  rw [lintegral_tsum (fun k => (hm k).aemeasurable)]
  apply tsum_congr
  intro k
  exact (lintegral_dirac_eval _ _ (measurable_arrival (k + 1)) _ measurableSet_Iic).symm

/-- Translation of the actual uniform mark law fills one unit height strip. -/
theorem translated_uniformUnit (n : ℕ) :
    Measure.map (fun u : ℝ => (n : ℝ) + u) uniformUnit =
      volume.restrict (Ico (n : ℝ) ((n : ℝ) + 1)) := by
  have hu : uniformUnit = volume.restrict (Ico (0 : ℝ) 1) :=
    (Measure.restrict_congr_set Ico_ae_eq_Icc).symm
  have hp : (fun u : ℝ => (n : ℝ) + u) ⁻¹' Ico (n : ℝ) ((n : ℝ) + 1) = Ico 0 1 := by
    ext u
    simp only [mem_preimage, mem_Ico]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hm := (measurePreserving_add_left (volume : Measure ℝ) (n : ℝ)).restrict_preimage
    (measurableSet_Ico : MeasurableSet (Ico (n : ℝ) ((n : ℝ) + 1)))
  rw [hp] at hm
  rw [hu]
  exact hm.map_eq

theorem pairwise_unitStrips : Pairwise (fun i j : ℕ =>
    Disjoint (Ico (i : ℝ) ((i : ℝ) + 1)) (Ico (j : ℝ) ((j : ℝ) + 1))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro u hi hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have h : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hlt
    linarith [hi.2, hj.1]
  · have h : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hgt
    linarith [hj.2, hi.1]

theorem iUnion_unitStrips : (⋃ n : ℕ, Ico (n : ℝ) ((n : ℝ) + 1)) = Ici (0 : ℝ) := by
  ext u
  constructor
  · intro h
    obtain ⟨n, hn⟩ := mem_iUnion.mp h
    exact (Nat.cast_nonneg n).trans hn.1
  · intro hu
    exact mem_iUnion.mpr ⟨⌊u⌋₊, Nat.floor_le hu, Nat.lt_floor_add_one u⟩

/-- The sum of all translated mark laws is Lebesgue measure on the positive half-line. -/
theorem sum_translated_uniformUnit :
    Measure.sum (fun n : ℕ => Measure.map (fun u : ℝ => (n : ℝ) + u) uniformUnit) =
      volume.restrict (Ici (0 : ℝ)) := by
  simp_rw [translated_uniformUnit]
  rw [← Measure.restrict_iUnion pairwise_unitStrips (fun _ => measurableSet_Ico),
    iUnion_unitStrips]

theorem tsum_uniformUnit_preimage (B : Set ℝ) (hB : MeasurableSet B) :
    (∑' n : ℕ, uniformUnit ((fun u : ℝ => (n : ℝ) + u) ⁻¹' B)) =
      volume (B ∩ Ici 0) := by
  have h := congrArg (fun μ : Measure ℝ => μ B) sum_translated_uniformUnit
  have he (n : ℕ) : (Measure.map (fun u : ℝ => (n : ℝ) + u) uniformUnit) B =
      uniformUnit ((fun u : ℝ => (n : ℝ) + u) ⁻¹' B) :=
    Measure.map_apply (measurable_const.add measurable_id) hB
  simp only [Measure.sum_apply _ hB, he, Measure.restrict_apply hB] at h
  exact h

/-- Lebesgue intensity on the nonnegative coordinate axis. The endpoint has zero mass. -/
def positiveVolume : Measure ℝ := volume.restrict (Ici 0)

theorem positiveVolume_Iic (a : ℝ) : positiveVolume (Iic a) = ENNReal.ofReal a := by
  rw [positiveVolume, Measure.restrict_apply measurableSet_Iic]
  have he : Iic a ∩ Ici (0 : ℝ) = Icc 0 a := by ext x; simp [and_comm]
  rw [he, Real.volume_Icc, sub_zero]

/-- Half-lines form a finite-mass spanning family for positive Lebesgue measure. -/
def positiveVolume_spanning : positiveVolume.FiniteSpanningSetsIn (range (Iic : ℝ → Set ℝ)) where
  set n := Iic (n : ℝ)
  set_mem n := ⟨n, rfl⟩
  finite n := by rw [positiveVolume_Iic]; exact ENNReal.ofReal_lt_top
  spanning := by
    ext x
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
    exact exists_nat_ge x

variable {J : Type*} [Countable J]

omit [Countable J] in
/-- A point in one strip has the product of its clock-event probability and
the corresponding translated uniform mark probability. -/
theorem lintegral_point_rectangle (j : J) (n k : ℕ) (T : ℝ)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, Measure.dirac (MarkedNoise.point j ω (n,k)) (Iic T ×ˢ B) ∂MarkedNoise.law J) =
      waitingTimeLaw 1 (by norm_num) {ω | arrival ω (k + 1) ≤ T} *
        uniformUnit ((fun u : ℝ => (n : ℝ) + u) ⁻¹' B) := by
  let f : MarkedNoise.StripSample → ℝ × ℝ :=
    fun p => (arrival p.1 (k + 1), (n : ℝ) + p.2 k)
  have hf : Measurable f := ((measurable_arrival (k + 1)).comp measurable_fst).prodMk
    (measurable_const.add ((measurable_pi_apply k).comp measurable_snd))
  have hg : Measurable (fun p => Measure.dirac (f p) (Iic T ×ˢ B)) :=
    (Measure.measurable_coe (measurableSet_Iic.prod hB)).comp
      (Measure.measurable_dirac.comp hf)
  change (∫⁻ ω, Measure.dirac (f (ω (j,n))) (Iic T ×ˢ B) ∂MarkedNoise.law J) = _
  rw [← lintegral_map hg (measurable_pi_apply (j,n)), MarkedNoise.strip_map,
    lintegral_dirac_eval _ f hf _ (measurableSet_Iic.prod hB)]
  have he : f ⁻¹' (Iic T ×ˢ B) =
      {ω : ClockSpace | arrival ω (k + 1) ≤ T} ×ˢ
        {u : ℕ → ℝ | (n : ℝ) + u k ∈ B} := by
    ext p
    rfl
  rw [he, MarkedNoise.stripLaw, Measure.prod_prod]
  congr 1
  have hshift : MeasurableSet ((fun u : ℝ => (n : ℝ) + u) ⁻¹' B) :=
    (measurable_const.add measurable_id) hB
  rw [← MarkedNoise.unitMarks_coordinate_map k, Measure.map_apply (measurable_pi_apply k) hshift]
  rfl

omit [Countable J] in
/-- Expected mass of the actual marked measure on a time-height rectangle,
prior to identifying the sum of translated mark laws with Lebesgue measure. -/
theorem lintegral_counting_rectangle_series (j : J) (T : ℝ) (hT : 0 ≤ T)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, MarkedNoise.countingMeasure j ω (Iic T ×ˢ B) ∂MarkedNoise.law J) =
      ENNReal.ofReal T * ∑' n : ℕ, uniformUnit ((fun u : ℝ => (n : ℝ) + u) ⁻¹' B) := by
  simp only [MarkedNoise.countingMeasure, Measure.sum_apply _ (measurableSet_Iic.prod hB)]
  have hm (p : ℕ × ℕ) : Measurable (fun ω =>
      Measure.dirac (MarkedNoise.point j ω p) (Iic T ×ˢ B)) :=
    (Measure.measurable_coe (measurableSet_Iic.prod hB)).comp
      (Measure.measurable_dirac.comp (MarkedNoise.measurable_point j p))
  rw [lintegral_tsum (fun p => (hm p).aemeasurable)]
  rw [ENNReal.tsum_prod']
  simp_rw [lintegral_point_rectangle j _ _ T B hB]
  simp_rw [ENNReal.tsum_mul_right, tsum_arrival_probabilities 1 (by norm_num) T hT, one_mul]
  exact ENNReal.tsum_mul_left

omit [Countable J] in
/-- The actual shared marked measure has the required Lebesgue rectangle intensity. -/
theorem lintegral_counting_rectangle (j : J) (T : ℝ) (hT : 0 ≤ T)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, MarkedNoise.countingMeasure j ω (Iic T ×ˢ B) ∂MarkedNoise.law J) =
      ENNReal.ofReal T * volume (B ∩ Ici 0) := by
  rw [lintegral_counting_rectangle_series j T hT B hB, tsum_uniformUnit_preimage B hB]

omit [Countable J] in
/-- Expected mass of the bounded time-height box is exactly its area. -/
theorem lintegral_counting_box (j : J) (T C : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, MarkedNoise.countingMeasure j ω (Iic T ×ˢ Iic C) ∂MarkedNoise.law J) =
      ENNReal.ofReal T * ENNReal.ofReal C := by
  rw [lintegral_counting_rectangle j T hT (Iic C) measurableSet_Iic]
  have he : Iic C ∩ Ici (0 : ℝ) = Icc 0 C := by ext x; simp [and_comm]
  rw [he, Real.volume_Icc, sub_zero]

omit [Countable J] in
/-- The box intensity formula also covers negative time cutoffs, when the mass is zero. -/
theorem lintegral_counting_box_all (j : J) (T C : ℝ) :
    (∫⁻ ω, MarkedNoise.countingMeasure j ω (Iic T ×ˢ Iic C) ∂MarkedNoise.law J) =
      ENNReal.ofReal T * ENNReal.ofReal C := by
  by_cases hT : 0 ≤ T
  · exact lintegral_counting_box j T C hT
  · have hT0 : T ≤ 0 := le_of_lt (lt_of_not_ge hT)
    rw [ENNReal.ofReal_eq_zero.mpr hT0, zero_mul]
    apply le_antisymm _ bot_le
    calc
      _ ≤ ∫⁻ ω, MarkedNoise.countingMeasure j ω (Iic 0 ×ˢ Iic C) ∂MarkedNoise.law J :=
        lintegral_mono (fun ω => measure_mono
          (Set.prod_mono (Iic_subset_Iic.mpr hT0) Subset.rfl))
      _ = 0 := by rw [lintegral_counting_box j 0 C le_rfl]; simp

/-- The expected random measure, defined by actual measure integration. -/
def intensity (j : J) : Measure (ℝ × ℝ) :=
  (MarkedNoise.law J).bind (MarkedNoise.countingMeasure j)

omit [Countable J] in
/-- The entire intensity measure is the product Lebesgue measure on the quadrant,
not merely a list of rectangle expectations. -/
theorem intensity_eq (j : J) : intensity j = positiveVolume.prod positiveVolume := by
  symm
  apply Measure.prod_eq_generateFrom
    (borel_eq_generateFrom_Iic ℝ).symm (borel_eq_generateFrom_Iic ℝ).symm
    isPiSystem_Iic isPiSystem_Iic positiveVolume_spanning positiveVolume_spanning
  rintro _ ⟨T, rfl⟩ _ ⟨C, rfl⟩
  rw [intensity, Measure.bind_apply (measurableSet_Iic.prod measurableSet_Iic)
    (MarkedNoise.measurable_countingMeasure j).aemeasurable,
    lintegral_counting_box_all, positiveVolume_Iic, positiveVolume_Iic]

omit [Countable J] in
/-- Campbell's identity for every nonnegative measurable deterministic integrand
against the actual shared marked counting measure. No integrability assumption is needed. -/
theorem campbell_nonnegative (j : J) (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ∫⁻ p, f p ∂MarkedNoise.countingMeasure j ω ∂MarkedNoise.law J) =
      ∫⁻ p, f p ∂positiveVolume.prod positiveVolume := by
  rw [← Measure.lintegral_bind (MarkedNoise.measurable_countingMeasure j).aemeasurable
    hf.aemeasurable]
  rw [show (MarkedNoise.law J).bind (MarkedNoise.countingMeasure j) =
    positiveVolume.prod positiveVolume from intensity_eq j]

omit [Countable J] in
/-- In particular the expectation of the count on any measurable set is its
Lebesgue area in the nonnegative quadrant. -/
theorem lintegral_counting_set (j : J) (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) :
    (∫⁻ ω, MarkedNoise.countingMeasure j ω s ∂MarkedNoise.law J) =
      (positiveVolume.prod positiveVolume) s := by
  rw [← Measure.bind_apply hs (MarkedNoise.measurable_countingMeasure j).aemeasurable]
  exact congrArg (fun μ : Measure (ℝ × ℝ) => μ s) (intensity_eq j)

end CarryingCapacity.MarkedIntensity
