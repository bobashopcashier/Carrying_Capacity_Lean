import CarryingCapacity.MarkedTimeProducts
import CarryingCapacity.MarkedTimeCounts
import CarryingCapacity.MarkedSplitting

/-!
# Joint marked Poisson laws on finite time grids

Different time windows use disjoint blocks of the actual iid marks. Categories
may vary from window to window and need only be disjoint within each window.
The joint transform is derived from the actual clock and marks, then identifies
the full product Poisson law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace CarryingCapacity.MarkedGridLaw
open CountableJumpProcess FrozenProcess MarkedNoise MarkedTimeProducts
  MarkedTimeCounts MarkedSplitting

variable {q : ℕ} {ι : Type*} [Fintype ι]

theorem timeProduct_categoryFactor (B : Fin q → ι → Set ℝ)
    (z : Fin q → ι → ℂ) (u : Fin (q+1) → ℝ) (hu : Monotone u)
    (ω : StripSample) (hfin : ∀ T : ℝ, {n : ℕ | arrival ω.1 n ≤ T}.Finite) :
    timeProduct (fun a => categoryFactor (B a) (z a)) u ω =
      ∏ a, ∏ i, z a i ^ gridCounts B u ω a i := by
  classical
  rw [gridCounts_eq_blockCounts B u hu ω hfin]
  unfold timeProduct blockProduct categoryFactor
  apply Finset.prod_congr rfl
  intro a _
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  exact indexProduct_indicator_eq_pow (B a i) (z a i) _ _ _

/-- The full finite-grid marked transform, with arbitrary disjoint categories per window. -/
theorem integral_gridVector_pow (B : Fin q → ι → Set ℝ)
    (hB : ∀ a i, MeasurableSet (B a i))
    (hdis : ∀ a, Pairwise (fun i l => Disjoint (B a i) (B a l)))
    (u : Fin (q+1) → ℝ) (hu : Monotone u) (hu0 : 0 ≤ u 0)
    (z : (Fin q × ι) → ℂ) (hz : ∀ p, ‖z p‖ ≤ 1) :
    (∫ ω, ∏ p, z p ^ gridVector B u ω p ∂stripLaw) =
      Complex.exp (∑ p : Fin q × ι,
        (((u p.1.succ - u p.1.castSucc) * uniformUnit.real (B p.1 p.2) : ℝ) : ℂ) *
          (z p - 1)) := by
  have he : (∫ ω, ∏ p, z p ^ gridVector B u ω p ∂stripLaw) =
      ∫ ω, timeProduct (fun a => categoryFactor (B a) (fun i => z (a,i))) u ω
        ∂stripLaw := by
    apply integral_congr_ae
    filter_upwards [strip_ae_good] with ω hω
    rw [timeProduct_categoryFactor B _ u hu ω hω.1.2]
    simp [gridVector, Fintype.prod_prod_type]
  rw [he, integral_timeProduct _
    (fun a => measurable_categoryFactor (B a) (hB a) _)
    (fun a => norm_categoryFactor_le_one (B a) _ (fun i => hz (a,i))) u hu hu0]
  simp_rw [integral_categoryFactor _ (hB _) (hdis _)]
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp only [add_sub_cancel_left, Finset.mul_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual marked strip has mutually independent Poisson counts on every
finite time grid, with disjoint measurable height categories in each window. -/
theorem gridVector_map (B : Fin q → ι → Set ℝ)
    (hB : ∀ a i, MeasurableSet (B a i))
    (hdis : ∀ a, Pairwise (fun i l => Disjoint (B a i) (B a l)))
    (u : Fin (q+1) → ℝ) (hu : Monotone u) (hu0 : 0 ≤ u 0) :
    Measure.map (gridVector B u) stripLaw =
      Measure.pi (fun p : Fin q × ι => poissonMeasure
        ⟨(u p.1.succ - u p.1.castSucc) * uniformUnit.real (B p.1 p.2),
          mul_nonneg (sub_nonneg.mpr (hu (Fin.castSucc_le_succ p.1)))
            measureReal_nonneg⟩) := by
  apply CountVectorTransform.measure_eq_of_pow_integrals_fintype
  intro z hz
  rw [integral_map_of_stronglyMeasurable (measurable_gridVector B hB u)
    (measurable_of_countable _).stronglyMeasurable,
    integral_gridVector_pow B hB hdis u hu hu0 z hz,
    PoissonTransform.integral_poisson_product]
  rfl

end CarryingCapacity.MarkedGridLaw
