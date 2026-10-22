import CarryingCapacity.MarkedIntensity
import CarryingCapacity.FiniteDisjointApproximation

/-!
# The planar lower-box algebra is dense for marked intensity

Finite Boolean combinations of lower boxes generate the actual planar Borel
sigma algebra. The intensity has finite spanning boxes in this family, so
mathlib's measure-dense algebra theorem supplies approximations, including
simultaneous disjoint approximations with summable errors.
-/

noncomputable section
open MeasureTheory MeasurableSpace Set symmDiff
open scoped ENNReal BigOperators

namespace CarryingCapacity.MarkedRectangleAlgebra
open MarkedIntensity

/-- The generating planar lower boxes. -/
def lowerBoxes : Set (Set (ℝ × ℝ)) :=
  image2 (· ×ˢ ·) (range (Iic : ℝ → Set ℝ)) (range (Iic : ℝ → Set ℝ))

/-- Their finite Boolean combinations. -/
def algebra : Set (Set (ℝ × ℝ)) := generateSetAlgebra lowerBoxes

theorem isSetAlgebra_algebra : IsSetAlgebra algebra := isSetAlgebra_generateSetAlgebra

theorem lowerBox_mem (t h : ℝ) : Iic t ×ˢ Iic h ∈ algebra :=
  self_subset_generateSetAlgebra (mem_image2_of_mem ⟨t, rfl⟩ ⟨h, rfl⟩)

theorem generateFrom_algebra :
    MeasurableSpace.generateFrom algebra = inferInstanceAs (MeasurableSpace (ℝ × ℝ)) := by
  rw [algebra, generateFrom_generateSetAlgebra_eq]
  exact generateFrom_eq_prod (borel_eq_generateFrom_Iic ℝ).symm
    (borel_eq_generateFrom_Iic ℝ).symm positiveVolume_spanning.isCountablySpanning
      positiveVolume_spanning.isCountablySpanning

/-- The actual quadrant Lebesgue intensity is finite on a spanning sequence
of sets in the lower-box algebra. -/
def finiteSpanning : (positiveVolume.prod positiveVolume).FiniteSpanningSetsIn algebra :=
  (positiveVolume_spanning.prod positiveVolume_spanning).mono self_subset_generateSetAlgebra

theorem measureDense : (positiveVolume.prod positiveVolume).MeasureDense algebra :=
  Measure.MeasureDense.of_generateFrom_isSetAlgebra_sigmaFinite
    isSetAlgebra_algebra finiteSpanning generateFrom_algebra.symm

theorem measurableSet_of_mem {S : Set (ℝ × ℝ)} (hS : S ∈ algebra) : MeasurableSet S :=
  measureDense.measurable S hS

/-- Every finite disjoint family of measurable finite-intensity sets has
disjoint lower-box-algebra approximations with summable intensity errors. -/
theorem exists_disjoint_summable_approximation {ι : Type*} [Fintype ι]
    (S : ι → Set (ℝ × ℝ)) (hS : ∀ i, MeasurableSet (S i))
    (hfin : ∀ i, (positiveVolume.prod positiveVolume) (S i) ≠ ∞)
    (hdis : Pairwise (fun i j => Disjoint (S i) (S j))) :
    ∃ Sₙ : ℕ → ι → Set (ℝ × ℝ),
      (∀ n i, Sₙ n i ∈ algebra) ∧
      (∀ n, Pairwise (fun i j => Disjoint (Sₙ n i) (Sₙ n j))) ∧
      (∀ n i, (positiveVolume.prod positiveVolume) (Sₙ n i) ≠ ∞) ∧
      ∀ i, (∑' n, (positiveVolume.prod positiveVolume) (Sₙ n i ∆ S i)) ≠ ∞ :=
  FiniteDisjointApproximation.exists_disjoint_summable_approximation_fintype
    (positiveVolume.prod positiveVolume) algebra isSetAlgebra_algebra measureDense S hS hfin hdis

end CarryingCapacity.MarkedRectangleAlgebra
