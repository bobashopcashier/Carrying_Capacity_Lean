import CarryingCapacity.MarkedRectangleAlgebra
import CarryingCapacity.MarkedBoxApproximation
import CarryingCapacity.MarkedSetPoissonLimit

/-!
# From bounded rectangle-algebra laws to all finite-intensity Borel sets

This extension theorem isolates the finite grid calculation. Given the
product Poisson law on bounded intersections of finite Boolean combinations
of lower boxes, actual count stability first removes the bounded box and then
passes through disjoint measure-dense approximations. No target-set law,
independence, convergence of counts, or convergence of parameters is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter symmDiff
open scoped ENNReal NNReal BigOperators

namespace CarryingCapacity.MarkedAlgebraExtension
open MarkedNoise MarkedIntensity MarkedSetCounts MarkedSetPoissonLimit
  MarkedRectangleAlgebra MarkedBoxApproximation

variable {J ι : Type*} [Fintype ι] (j : J)
  (hbounded : ∀ (S : ι → Set (ℝ × ℝ)),
    (∀ i, S i ∈ algebra) → Pairwise (fun i l => Disjoint (S i) (S l)) → ∀ m : ℕ,
      Measure.map (fun ω : Sample J => fun i => count j (S i ∩ box m) ω) (law J) =
        Measure.pi (fun i => poissonMeasure (setRate (S i ∩ box m))))
include hbounded

/-- Summable box exhaustion removes boundedness from the finite algebra law. -/
theorem algebra_countVector_map (S : ι → Set (ℝ × ℝ))
    (hS : ∀ i, S i ∈ algebra) (hdis : Pairwise (fun i l => Disjoint (S i) (S l)))
    (hfin : ∀ i, (positiveVolume.prod positiveVolume) (S i) ≠ ∞) :
    Measure.map (fun ω : Sample J => fun i => count j (S i) ω) (law J) =
      Measure.pi (fun i => poissonMeasure (setRate (S i))) := by
  have hm (i : ι) : MeasurableSet (S i) := measurableSet_of_mem (hS i)
  obtain ⟨m, hsum⟩ := exists_summable_box_truncations S hm hfin
  exact countVector_map_of_summable_approximation j S hm hfin
    (fun n i => S i ∩ box (m n))
    (fun n i => (hm i).inter (measurableSet_box (m n))) hsum
    (fun n => hbounded S hS hdis (m n))

/-- Full independent Poisson vector law on arbitrary disjoint measurable sets
of finite intensity, derived from bounded finite-grid algebra laws. -/
theorem countVector_map (S : ι → Set (ℝ × ℝ))
    (hS : ∀ i, MeasurableSet (S i))
    (hdis : Pairwise (fun i l => Disjoint (S i) (S l)))
    (hfin : ∀ i, (positiveVolume.prod positiveVolume) (S i) ≠ ∞) :
    Measure.map (fun ω : Sample J => fun i => count j (S i) ω) (law J) =
      Measure.pi (fun i => poissonMeasure (setRate (S i))) := by
  obtain ⟨Sₙ, hmem, hdisₙ, hfinₙ, hsum⟩ :=
    MarkedRectangleAlgebra.exists_disjoint_summable_approximation S hS hfin hdis
  exact countVector_map_of_summable_approximation j S hS hfin Sₙ
    (fun n i => measurableSet_of_mem (hmem n i)) hsum
    (fun n => algebra_countVector_map j hbounded (Sₙ n) (hmem n) (hdisₙ n) (hfinₙ n))

/-- The result for the genuine planar random counting measure, embedded from
the independent Poisson natural counts. -/
theorem countingMeasure_map (S : ι → Set (ℝ × ℝ))
    (hS : ∀ i, MeasurableSet (S i))
    (hdis : Pairwise (fun i l => Disjoint (S i) (S l)))
    (hfin : ∀ i, (positiveVolume.prod positiveVolume) (S i) ≠ ∞) :
    Measure.map (fun ω : Sample J => fun i => countingMeasure j ω (S i)) (law J) =
      Measure.map (fun v : ι → ℕ => fun i => (v i : ℝ≥0∞))
        (Measure.pi (fun i => poissonMeasure (setRate (S i)))) := by
  rw [← countVector_map j hbounded S hS hdis hfin,
    Measure.map_map (measurable_of_countable _)
      (measurable_pi_lambda _ (fun i => measurable_count j (S i) (hS i)))]
  apply Measure.map_congr
  filter_upwards [ae_all_iff.mpr (fun i => ae_countingMeasure_eq_count j (S i) (hS i) (hfin i))]
    with ω hω
  exact funext hω

end CarryingCapacity.MarkedAlgebraExtension
