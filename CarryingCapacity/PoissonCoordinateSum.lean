import CarryingCapacity.PoissonTransform
import CarryingCapacity.CountVectorTransform

/-!
# Summing one index of a product Poisson vector

A finite array of independent Poisson coordinates remains a product Poisson
vector after summing the first index. The rates add within each remaining
coordinate. This is a statement about the actual pushed-forward measures,
proved from the previously derived product transforms.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace CarryingCapacity.PoissonCoordinateSum
variable {α ι : Type*} [Fintype α] [Fintype ι]

/-- Aggregate a finite count array over its first coordinate. -/
def coordinateSum (v : (α × ι) → ℕ) (i : ι) : ℕ := ∑ a, v (a, i)

/-- The actual sum map is measurable. -/
theorem measurable_coordinateSum : Measurable (coordinateSum (α := α) (ι := ι)) :=
  measurable_of_countable _

/-- A product of powers of the aggregated counts factors over the array. -/
theorem pow_coordinateSum (z : ι → ℂ) (v : (α × ι) → ℕ) :
    (∏ i, z i ^ coordinateSum v i) = ∏ p : α × ι, z p.2 ^ v p := by
  simp only [coordinateSum, ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  exact (Fintype.prod_prod_type (fun p : α × ι => z p.2 ^ v p)).symm

/-- The exact transform after deterministic coordinate aggregation. -/
theorem integral_coordinateSum (r : (α × ι) → ℝ≥0) (z : ι → ℂ) :
    (∫ v : (α × ι) → ℕ, ∏ i, z i ^ coordinateSum v i
      ∂Measure.pi (fun p => poissonMeasure (r p))) =
    Complex.exp (∑ i, (((∑ a, r (a,i) : ℝ≥0) : ℝ) : ℂ) * (z i - 1)) := by
  simp_rw [pow_coordinateSum]
  rw [PoissonTransform.integral_poisson_product]
  congr 1
  simp only [NNReal.coe_sum, Complex.ofReal_sum, Finset.sum_mul]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- A finite product-Poisson array sums to independent Poisson coordinates,
including empty index types and zero rates. -/
theorem coordinateSum_map (r : (α × ι) → ℝ≥0) :
    Measure.map (coordinateSum (α := α) (ι := ι))
      (Measure.pi (fun p => poissonMeasure (r p))) =
      Measure.pi (fun i => poissonMeasure (∑ a, r (a,i))) := by
  apply CountVectorTransform.measure_eq_of_pow_integrals_fintype
  intro z _
  rw [integral_map_of_stronglyMeasurable measurable_coordinateSum
    (measurable_of_countable (fun v : ι → ℕ => ∏ i, z i ^ v i)).stronglyMeasurable,
    integral_coordinateSum, PoissonTransform.integral_poisson_product]

end CarryingCapacity.PoissonCoordinateSum
