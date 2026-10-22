import CarryingCapacity.MarkedBoundedAlgebraLaw
import CarryingCapacity.MarkedAlgebraExtension

/-!
# The actual marked counting measure on arbitrary finite-intensity sets

For any fixed noise label, every finite family of disjoint measurable planar
sets of finite intensity has the full product Poisson count law. This follows
from the proved finite-grid law, finite Boolean rectangle refinement, bounded
box exhaustion, and disjoint measure-dense approximation. No Poisson law or
independence of the target counts is assumed.

The intensity is `positiveVolume.prod positiveVolume`. The natural-valued
count version agrees almost surely with the genuine random-measure mass;
the latter is also given its exact pushforward law and independence theorem.
This module makes no assertion about infinite-intensity sets or simultaneous
independence between different noise labels.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace CarryingCapacity.MarkedPoissonMeasure
open MarkedNoise MarkedIntensity MarkedSetCounts MarkedSetPoissonLimit

variable {J ι : Type*} [Fintype ι]

/-- The full product Poisson law of the actual finite-intensity set counts. -/
theorem countVector_map (j : J) (S : ι → Set (ℝ × ℝ))
    (hS : ∀ i, MeasurableSet (S i))
    (hdis : Pairwise (fun i l => Disjoint (S i) (S l)))
    (hfin : ∀ i, (positiveVolume.prod positiveVolume) (S i) ≠ ∞) :
    Measure.map (fun ω : Sample J => fun i => count j (S i) ω) (law J) =
      Measure.pi (fun i => poissonMeasure (setRate (S i))) := by
  apply MarkedAlgebraExtension.countVector_map j _ S hS hdis hfin
  intro A hA hd m
  exact MarkedBoundedAlgebraLaw.countVector_map j A hA hd (m : ℝ) (Nat.cast_nonneg m) m

/-- The same law stated directly for the genuine random counting measure. -/
theorem countingMeasure_map (j : J) (S : ι → Set (ℝ × ℝ))
    (hS : ∀ i, MeasurableSet (S i))
    (hdis : Pairwise (fun i l => Disjoint (S i) (S l)))
    (hfin : ∀ i, (positiveVolume.prod positiveVolume) (S i) ≠ ∞) :
    Measure.map (fun ω : Sample J => fun i => countingMeasure j ω (S i)) (law J) =
      Measure.map (fun v : ι → ℕ => fun i => (v i : ℝ≥0∞))
        (Measure.pi (fun i => poissonMeasure (setRate (S i)))) := by
  apply MarkedAlgebraExtension.countingMeasure_map j _ S hS hdis hfin
  intro A hA hd m
  exact MarkedBoundedAlgebraLaw.countVector_map j A hA hd (m : ℝ) (Nat.cast_nonneg m) m

/-- Each measurable finite-intensity set has its Poisson count distribution. -/
theorem count_map (j : J) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (hfin : (positiveVolume.prod positiveVolume) S ≠ ∞) :
    Measure.map (count j S) (law J) = poissonMeasure (setRate S) := by
  have hd : Pairwise (fun _ _ : Unit => Disjoint S S) := by
    intro i l hil
    exact False.elim (hil (Subsingleton.elim i l))
  have h := congrArg (Measure.map (fun v : Unit → ℕ => v ()))
    (countVector_map j (fun _ : Unit => S) (fun _ => hS) hd (fun _ => hfin))
  rw [Measure.map_map (measurable_pi_apply ())
    (measurable_pi_lambda _ (fun _ => measurable_count j S hS))] at h
  have hp := (measurePreserving_funUnique (poissonMeasure (setRate S)) Unit).map_eq
  change Measure.map (fun v : Unit → ℕ => v ())
    (Measure.pi (fun _ : Unit => poissonMeasure (setRate S))) = _ at hp
  rw [hp] at h
  exact h

/-- The mass of a finite-intensity measurable set is an embedded Poisson count. -/
theorem countingMeasure_set_map (j : J) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (hfin : (positiveVolume.prod positiveVolume) S ≠ ∞) :
    Measure.map (fun ω : Sample J => countingMeasure j ω S) (law J) =
      Measure.map (fun n : ℕ => (n : ℝ≥0∞)) (poissonMeasure (setRate S)) := by
  rw [← count_map j S hS hfin,
    Measure.map_map (measurable_of_countable _) (measurable_count j S hS)]
  exact Measure.map_congr (ae_countingMeasure_eq_count j S hS hfin)

/-- Independence is joint independence of every finite family, not merely
pairwise independence of the individual set counts. -/
theorem independent_counts (j : J) (S : ι → Set (ℝ × ℝ))
    (hS : ∀ i, MeasurableSet (S i))
    (hdis : Pairwise (fun i l => Disjoint (S i) (S l)))
    (hfin : ∀ i, (positiveVolume.prod positiveVolume) (S i) ≠ ∞) :
    iIndepFun (fun i => count j (S i)) (law J) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_count j (S i) (hS i)).aemeasurable)).mpr
  simp_rw [count_map j _ (hS _) (hfin _)]
  exact countVector_map j S hS hdis hfin

/-- Joint independence of the genuine random-measure masses of disjoint
measurable finite-intensity sets. -/
theorem independent_countingMeasure (j : J) (S : ι → Set (ℝ × ℝ))
    (hS : ∀ i, MeasurableSet (S i))
    (hdis : Pairwise (fun i l => Disjoint (S i) (S l)))
    (hfin : ∀ i, (positiveVolume.prod positiveVolume) (S i) ≠ ∞) :
    iIndepFun (fun i ω => countingMeasure j ω (S i)) (law J) := by
  have h := (independent_counts j S hS hdis hfin).comp
    (fun _ (n : ℕ) => (n : ℝ≥0∞)) (fun _ => measurable_of_countable _)
  apply h.congr
  intro i
  exact (ae_countingMeasure_eq_count j (S i) (hS i) (hfin i)).mono
    (fun _ he => he.symm)

end CarryingCapacity.MarkedPoissonMeasure
