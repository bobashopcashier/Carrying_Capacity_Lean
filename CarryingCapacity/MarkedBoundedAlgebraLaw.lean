import CarryingCapacity.TimeGridRefinement
import CarryingCapacity.MarkedRectangleAlgebra
import CarryingCapacity.MarkedGridRectangles
import CarryingCapacity.MarkedSetPoissonLimit
import CarryingCapacity.MarkedCountMoments
import CarryingCapacity.PoissonCoordinateSum

/-!
# Actual product Poisson laws on bounded rectangle-algebra sets

Finite Boolean combinations of lower boxes are refined into a common time
grid, with measurable disjoint height categories in each cell. The existing
actual grid law and deterministic coordinate aggregation then give the full
product Poisson count law. The refinement and its intensity parameters are
proved; no count-law or independence premise is added.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators

namespace CarryingCapacity.MarkedBoundedAlgebraLaw
open MarkedNoise MarkedIntensity MarkedSetCounts MarkedSetPoissonLimit
  MarkedGridRectangles TimeGridRefinement

variable {J ι : Type*} [Fintype ι] {q : ℕ}

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

/-- The union of one height category over consecutive time windows. -/
def gridUnion (B : Fin q → ι → Set ℝ) (u : Fin (q + 1) → ℝ) (i : ι) : Set (ℝ × ℝ) :=
  ⋃ a : Fin q, Ioc (u a.castSucc) (u a.succ) ×ˢ B a i

omit [Fintype ι] in
theorem measurableSet_gridUnion (B : Fin q → ι → Set ℝ)
    (hB : ∀ a i, MeasurableSet (B a i)) (u : Fin (q + 1) → ℝ) (i : ι) :
    MeasurableSet (gridUnion B u i) :=
  MeasurableSet.iUnion (fun a => measurableSet_Ioc.prod (hB a i))

omit [Fintype ι] in
theorem pairwise_gridRectangles (B : Fin q → ι → Set ℝ)
    (u : Fin (q + 1) → ℝ) (hu : Monotone u) (i : ι) :
    Pairwise (fun a b : Fin q => Disjoint
      (Ioc (u a.castSucc) (u a.succ) ×ˢ B a i)
      (Ioc (u b.castSucc) (u b.succ) ×ˢ B b i)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro p ha hb
  exact Set.disjoint_left.mp (pairwise_grid_cells u hu hab) ha.1 hb.1

omit [Fintype ι] in
/-- The intensity of a grid union is the sum of its cell intensities. -/
theorem setRate_gridUnion (m : ℕ) (B : Fin q → ι → Set ℝ)
    (hB : ∀ a i, MeasurableSet (B a i)) (hbound : ∀ a i, B a i ⊆ Iio (m : ℝ))
    (u : Fin (q + 1) → ℝ) (hu : Monotone u) (hu0 : 0 ≤ u 0) (i : ι) :
    setRate (gridUnion B u i) = ∑ a : Fin q,
      (⟨(u a.succ - u a.castSucc) * positiveVolume.real (B a i),
        mul_nonneg (sub_nonneg.mpr (hu (Fin.castSucc_le_succ a)))
          measureReal_nonneg⟩ : ℝ≥0) := by
  have hheight (a : Fin q) : positiveVolume (B a i) ≠ ∞ := by
    exact ne_top_of_le_ne_top
      (show positiveVolume (Iic (m : ℝ)) ≠ ∞ by
        rw [positiveVolume_Iic]; exact ENNReal.ofReal_ne_top)
      (measure_mono ((hbound a i).trans Iio_subset_Iic_self))
  have hfinite (a : Fin q) : (positiveVolume.prod positiveVolume)
      (Ioc (u a.castSucc) (u a.succ) ×ˢ B a i) ≠ ∞ := by
    rw [Measure.prod_prod,
      MarkedCountMoments.positiveVolume_Ioc _ _ (hu0.trans (hu (Fin.zero_le _)))]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hheight a)
  apply NNReal.coe_injective
  change (positiveVolume.prod positiveVolume).real (gridUnion B u i) = _
  calc
    _ = ∑ a : Fin q, (positiveVolume.prod positiveVolume).real
        (Ioc (u a.castSucc) (u a.succ) ×ˢ B a i) :=
      measureReal_iUnion_fintype (pairwise_gridRectangles B u hu i)
        (fun a => measurableSet_Ioc.prod (hB a i)) hfinite
    _ = ∑ a : Fin q, (u a.succ - u a.castSucc) * positiveVolume.real (B a i) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Measure.real, Measure.prod_prod,
        MarkedCountMoments.positiveVolume_Ioc _ _ (hu0.trans (hu (Fin.zero_le _))),
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr (hu (Fin.castSucc_le_succ a)))]
      rfl
    _ = _ := (NNReal.coe_sum Finset.univ (fun a : Fin q =>
      (⟨(u a.succ - u a.castSucc) * positiveVolume.real (B a i),
        mul_nonneg (sub_nonneg.mpr (hu (Fin.castSucc_le_succ a)))
          measureReal_nonneg⟩ : ℝ≥0))).symm

omit [Fintype ι] in
/-- The actual natural counts of grid unions are sums of the actual grid counts. -/
theorem ae_count_gridUnion (j : J) (m : ℕ) (B : Fin q → ι → Set ℝ)
    (hB : ∀ a i, MeasurableSet (B a i)) (hbound : ∀ a i, B a i ⊆ Iio (m : ℝ))
    (u : Fin (q + 1) → ℝ) (hu : Monotone u) (hu0 : 0 ≤ u 0) :
    ∀ᵐ ω ∂law J, (fun i => count j (gridUnion B u i) ω) =
      PoissonCoordinateSum.coordinateSum (boundedGridVector j m B u ω) := by
  filter_upwards [MarkedBoundedCounts.ae_countingMeasure_eq_boundedWindowCount j] with ω hω
  funext i
  have hm : countingMeasure j ω (gridUnion B u i) =
      ((∑ a : Fin q, boundedGridVector j m B u ω (a,i) : ℕ) : ℝ≥0∞) := by
    rw [gridUnion, measure_iUnion (pairwise_gridRectangles B u hu i)
      (fun a => measurableSet_Ioc.prod (hB a i)), tsum_fintype, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact hω m (B a i) (hB a i) (hbound a i) (u a.castSucc) (u a.succ)
      (hu0.trans (hu (Fin.zero_le _))) (hu (Fin.castSucc_le_succ a))
  simp only [count, hm, ENNReal.toReal_natCast, Nat.floor_natCast,
    PoissonCoordinateSum.coordinateSum]

/-- Full joint law after aggregating the actual time-grid cells. -/
theorem gridUnion_countVector_map (j : J) (m : ℕ) (B : Fin q → ι → Set ℝ)
    (hB : ∀ a i, MeasurableSet (B a i)) (hbound : ∀ a i, B a i ⊆ Iio (m : ℝ))
    (hdis : ∀ a, Pairwise (fun i l => Disjoint (B a i) (B a l)))
    (u : Fin (q + 1) → ℝ) (hu : Monotone u) (hu0 : 0 ≤ u 0) :
    Measure.map (fun ω : Sample J => fun i => count j (gridUnion B u i) ω) (law J) =
      Measure.pi (fun i => poissonMeasure (setRate (gridUnion B u i))) := by
  rw [Measure.map_congr (ae_count_gridUnion j m B hB hbound u hu hu0)]
  change Measure.map (PoissonCoordinateSum.coordinateSum ∘ boundedGridVector j m B u) _ = _
  rw [← Measure.map_map PoissonCoordinateSum.measurable_coordinateSum
    (measurable_boundedGridVector j m B hB u),
    boundedGridVector_map j m B hB hbound hdis u hu hu0,
    PoissonCoordinateSum.coordinateSum_map]
  congr 1
  funext i
  rw [setRate_gridUnion m B hB hbound u hu hu0 i]

/-- Every finite Boolean combination of lower boxes has finite time thresholds. -/
theorem exists_thresholds {S : Set (ℝ × ℝ)} (hS : S ∈ MarkedRectangleAlgebra.algebra) :
    ∃ K, DeterminedBy K S := by
  apply exists_thresholds_of_mem_algebra MarkedRectangleAlgebra.lowerBoxes _ S hS
  intro R hR
  obtain ⟨U, ⟨a, rfl⟩, W, ⟨b, rfl⟩, rfl⟩ := hR
  exact ⟨{a}, lowerRectangle_determined a b⟩

/-- The proved bounded-set input for extending the actual Poisson law to
arbitrary finite-intensity disjoint measurable planar sets. -/
theorem countVector_map (j : J) (S : ι → Set (ℝ × ℝ))
    (hS : ∀ i, S i ∈ MarkedRectangleAlgebra.algebra)
    (hdis : Pairwise (fun i l => Disjoint (S i) (S l)))
    (T : ℝ) (hT : 0 ≤ T) (m : ℕ) :
    Measure.map (fun ω : Sample J => fun i => count j (S i ∩ (Ioc 0 T ×ˢ Iio (m : ℝ))) ω)
      (law J) =
      Measure.pi (fun i => poissonMeasure (setRate (S i ∩ (Ioc 0 T ×ˢ Iio (m : ℝ))))) := by
  obtain ⟨q, u, B, hu, hu0, _, hB, hbound, hd, he⟩ := exists_grid_representation S
    (fun i => MarkedRectangleAlgebra.measurableSet_of_mem (hS i))
    (fun i => exists_thresholds (hS i)) hdis T m hT
  have hz : 0 ≤ u 0 := by rw [hu0]
  simpa only [← he, gridUnion] using gridUnion_countVector_map j m B hB hbound hd u hu hz

end CarryingCapacity.MarkedBoundedAlgebraLaw
