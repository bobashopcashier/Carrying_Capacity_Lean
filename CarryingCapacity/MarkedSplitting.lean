import CarryingCapacity.MarkedThinning
import CarryingCapacity.CountVectorTransform

/-!
# Splitting the actual marked strip into disjoint categories

The multivariate transform is computed from the actual iid marks and actual
Poisson clock. Disjointness enters only in the single-mark factor identity.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace CarryingCapacity.MarkedSplitting
open CountableJumpProcess FrozenProcess MarkedNoise MarkedProducts MarkedThinning
  MarkedStripCounts

variable {ι : Type*} [Fintype ι]

def categoryFactor (B : ι → Set ℝ) (z : ι → ℂ) (x : ℝ) : ℂ :=
  ∏ i, markFactor (B i) (z i) x

theorem measurable_categoryFactor (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (z : ι → ℂ) : Measurable (categoryFactor B z) :=
  Finset.measurable_prod _ (fun i _ => measurable_markFactor (B i) (hB i) (z i))

theorem norm_categoryFactor_le_one (B : ι → Set ℝ) (z : ι → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ 1) (x : ℝ) : ‖categoryFactor B z x‖ ≤ 1 := by
  exact (Finset.norm_prod_le _ _).trans (Finset.prod_le_one
    (fun _ _ => norm_nonneg _) (fun i _ => norm_markFactor_le_one (B i) (z i) (hz i) x))

theorem categoryFactor_eq_sum (B : ι → Set ℝ)
    (hdis : Pairwise (fun i j => Disjoint (B i) (B j))) (z : ι → ℂ) (x : ℝ) :
    categoryFactor B z x = 1 + ∑ i, (B i).indicator (fun _ => z i - 1) x := by
  classical
  by_cases hex : ∃ i, x ∈ B i
  · obtain ⟨i, hi⟩ := hex
    have hj (j : ι) (hji : j ≠ i) : x ∉ B j := by
      intro hx
      exact Set.disjoint_left.mp (hdis hji) hx hi
    rw [categoryFactor, Finset.prod_eq_single i]
    · rw [Finset.sum_eq_single i]
      · simp [markFactor, hi]
      · intro j _ hji
        simp [hj j hji]
      · simp
    · intro j _ hji
      simp [markFactor, hj j hji]
    · simp
  · have hx : ∀ i, x ∉ B i := by simpa using hex
    simp [categoryFactor, markFactor, hx]

theorem integral_categoryFactor (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (hdis : Pairwise (fun i j => Disjoint (B i) (B j))) (z : ι → ℂ) :
    (∫ x, categoryFactor B z x ∂uniformUnit) =
      1 + ∑ i, (uniformUnit.real (B i) : ℂ) * (z i - 1) := by
  simp_rw [categoryFactor_eq_sum B hdis z]
  rw [integral_add (integrable_const _) (integrable_finset_sum _
    (fun i _ => (integrable_const _).indicator (hB i))),
    integral_finset_sum _ (fun i _ => (integrable_const _).indicator (hB i))]
  simp [integral_indicator_const, hB, Complex.real_smul]

theorem clockProduct_categoryFactor (B : ι → Set ℝ) (z : ι → ℂ)
    (T : ℝ) (ω : StripSample) :
    clockProduct (categoryFactor B z) T ω = ∏ i, z i ^ clockCount (B i) T ω := by
  classical
  unfold clockProduct prefixProduct categoryFactor
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  exact prefixProduct_indicator_eq_pow (B i) (z i) _ _

/-- Joint complex transform for disjoint measurable categories at a common horizon. -/
theorem integral_categoryCounts_pow (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (hdis : Pairwise (fun i j => Disjoint (B i) (B j)))
    (T : ℝ) (hT : 0 ≤ T) (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    (∫ ω, ∏ i, z i ^ clockCount (B i) T ω ∂stripLaw) =
      Complex.exp (∑ i, ((T * uniformUnit.real (B i) : ℝ) : ℂ) * (z i - 1)) := by
  simp_rw [← clockProduct_categoryFactor]
  rw [integral_clockProduct _ (measurable_categoryFactor B hB z)
    (norm_categoryFactor_le_one B z hz),
    PoissonTransform.integral_proposalCount_pow 1 (by norm_num) T hT,
    integral_categoryFactor B hB hdis z]
  congr 1
  simp only [one_mul, add_sub_cancel_left, Finset.mul_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Disjoint measurable mark categories have the actual joint product Poisson law. -/
theorem categoryCounts_map {k : ℕ} (B : Fin k → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hdis : Pairwise (fun i j => Disjoint (B i) (B j)))
    (T : ℝ) (hT : 0 ≤ T) :
    Measure.map (fun ω : StripSample => fun i => clockCount (B i) T ω) stripLaw =
      Measure.pi (fun i => poissonMeasure
        ⟨T * uniformUnit.real (B i), mul_nonneg hT measureReal_nonneg⟩) := by
  apply CountVectorTransform.measure_eq_of_pow_integrals
  intro z hz
  rw [integral_map_of_stronglyMeasurable
    (measurable_pi_lambda _ (fun i => measurable_clockCount (B i) (hB i) T))
    (measurable_of_countable _).stronglyMeasurable,
    integral_categoryCounts_pow B hB hdis T hT z hz,
    PoissonTransform.integral_poisson_product]
  rfl

theorem independent_categoryCounts {k : ℕ} (B : Fin k → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hdis : Pairwise (fun i j => Disjoint (B i) (B j)))
    (T : ℝ) (hT : 0 ≤ T) :
    iIndepFun (fun i => clockCount (B i) T) stripLaw := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i =>
    (measurable_clockCount (B i) (hB i) T).aemeasurable)).mpr
  rw [categoryCounts_map B hB hdis T hT]
  congr 1
  funext i
  exact (clockCount_map (B i) (hB i) T hT).symm

/-- The same joint law for the masses of the actual translated strip measure. -/
theorem stripMeasure_categoryCounts_map {k : ℕ} (n : ℕ) (B : Fin k → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hdis : Pairwise (fun i j => Disjoint (B i) (B j)))
    (T : ℝ) (hT : 0 ≤ T) :
    Measure.map (fun ω : StripSample => fun i =>
      ⌊(stripMeasure n ω (Iic T ×ˢ B i)).toReal⌋₊) stripLaw =
      Measure.pi (fun i => poissonMeasure
        ⟨T * uniformUnit.real ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B i),
          mul_nonneg hT measureReal_nonneg⟩) := by
  let A : Fin k → Set ℝ := fun i => (fun x : ℝ => (n : ℝ) + x) ⁻¹' B i
  have hA (i : Fin k) : MeasurableSet (A i) :=
    (hB i).preimage (measurable_const.add measurable_id)
  have hd : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    exact (hdis hij).preimage _
  calc
    _ = Measure.map (fun ω : StripSample => fun i => clockCount (A i) T ω) stripLaw := by
      apply Measure.map_congr
      filter_upwards [ae_stripMeasure_rectangle] with ω hω
      funext i
      rw [hω n T hT (B i) (hB i)]
      simp [A]
    _ = _ := categoryCounts_map A hA hd T hT

end CarryingCapacity.MarkedSplitting
