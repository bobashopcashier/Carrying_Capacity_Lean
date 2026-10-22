import CarryingCapacity.MarkedSetCounts
import CarryingCapacity.PoissonLawLimit

/-!
# Passing product Poisson laws through planar set approximation

Summable intensity symmetric differences imply almost-sure eventual equality
of the actual count vectors and convergence of every intensity parameter.
Consequently a product Poisson law on approximating sets passes to the target
measurable finite-intensity sets. No target count law or independence is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter symmDiff
open scoped ENNReal NNReal BigOperators Topology

namespace CarryingCapacity.MarkedSetPoissonLimit
open MarkedNoise MarkedIntensity MarkedSetCounts

/-- Finite set masses vary by at most the mass of their symmetric difference. -/
theorem abs_measureReal_sub_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (S T : Set X) (hS : ν S ≠ ∞) (hT : ν T ≠ ∞) :
    |ν.real S - ν.real T| ≤ ν.real (S ∆ T) := by
  have hf := measure_symmDiff_ne_top hS hT
  have hST : ν.real S - ν.real T ≤ ν.real (S ∆ T) :=
    (le_measureReal_diff hT).trans (measureReal_mono (fun _ h => Or.inl h) hf)
  have hTS : ν.real T - ν.real S ≤ ν.real (S ∆ T) :=
    (le_measureReal_diff hS).trans (measureReal_mono (fun _ h => Or.inr h) hf)
  exact abs_le.mpr ⟨by linarith, hST⟩

/-- The intensity parameters converge as a consequence of summable symmetric
differences; parameter convergence need not be an additional assumption. -/
theorem tendsto_measureReal_of_summable_symmDiff {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (S : Set X) (hfin : ν S ≠ ∞) (Sₙ : ℕ → Set X)
    (hsum : (∑' n, ν (Sₙ n ∆ S)) ≠ ∞) :
    Tendsto (fun n => ν.real (Sₙ n)) atTop (𝓝 (ν.real S)) := by
  have hnfin (n : ℕ) : ν (Sₙ n) ≠ ∞ :=
    (measure_ne_top_iff_of_symmDiff (ENNReal.ne_top_of_tsum_ne_top hsum n)).mpr hfin
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun n => ?_) (ENNReal.summable_toReal hsum).tendsto_atTop_zero
  simpa only [Real.dist_eq] using abs_measureReal_sub_le ν (Sₙ n) S (hnfin n) hfin

/-- Finite planar intensity as the parameter of a Poisson count. -/
def setRate (S : Set (ℝ × ℝ)) : ℝ≥0 :=
  ⟨(positiveVolume.prod positiveVolume).real S, measureReal_nonneg⟩

variable {J ι : Type*} [Fintype ι]

/-- Extension of proved approximating count laws to arbitrary target sets
under summable intensity approximation. No pairwise-independence shortcut is used:
the conclusion is the full product law of the entire finite count vector. -/
theorem countVector_map_of_summable_approximation
    (j : J) (S : ι → Set (ℝ × ℝ)) (hS : ∀ i, MeasurableSet (S i))
    (hfin : ∀ i, (positiveVolume.prod positiveVolume) (S i) ≠ ∞)
    (Sₙ : ℕ → ι → Set (ℝ × ℝ)) (hSₙ : ∀ n i, MeasurableSet (Sₙ n i))
    (hsum : ∀ i, (∑' n, (positiveVolume.prod positiveVolume) (Sₙ n i ∆ S i)) ≠ ∞)
    (hLaw : ∀ n,
      Measure.map (fun ω : Sample J => fun i => count j (Sₙ n i) ω) (law J) =
        Measure.pi (fun i => poissonMeasure (setRate (Sₙ n i)))) :
    Measure.map (fun ω : Sample J => fun i => count j (S i) ω) (law J) =
      Measure.pi (fun i => poissonMeasure (setRate (S i))) := by
  apply PoissonLawLimit.map_eq_of_ae_eventually_eq (law J)
    (fun ω i => count j (S i) ω)
    (measurable_pi_lambda _ (fun i => measurable_count j (S i) (hS i)))
    (fun n ω i => count j (Sₙ n i) ω)
    (fun n => measurable_pi_lambda _ (fun i => measurable_count j (Sₙ n i) (hSₙ n i)))
    (fun i => setRate (S i)) (fun n i => setRate (Sₙ n i))
  · intro i
    exact tendsto_measureReal_of_summable_symmDiff (positiveVolume.prod positiveVolume)
      (S i) (hfin i) (fun n => Sₙ n i) (hsum i)
  · exact hLaw
  · exact ae_eventually_countVector_eq j S hS Sₙ hSₙ hsum

/-- The corresponding statement is about the genuine random counting measure,
not merely its chosen natural-valued representatives. -/
theorem countingMeasure_map_of_summable_approximation
    (j : J) (S : ι → Set (ℝ × ℝ)) (hS : ∀ i, MeasurableSet (S i))
    (hfin : ∀ i, (positiveVolume.prod positiveVolume) (S i) ≠ ∞)
    (Sₙ : ℕ → ι → Set (ℝ × ℝ)) (hSₙ : ∀ n i, MeasurableSet (Sₙ n i))
    (hsum : ∀ i, (∑' n, (positiveVolume.prod positiveVolume) (Sₙ n i ∆ S i)) ≠ ∞)
    (hLaw : ∀ n,
      Measure.map (fun ω : Sample J => fun i => count j (Sₙ n i) ω) (law J) =
        Measure.pi (fun i => poissonMeasure (setRate (Sₙ n i)))) :
    Measure.map (fun ω : Sample J => fun i => countingMeasure j ω (S i)) (law J) =
      Measure.map (fun v : ι → ℕ => fun i => (v i : ℝ≥0∞))
        (Measure.pi (fun i => poissonMeasure (setRate (S i)))) := by
  rw [← countVector_map_of_summable_approximation j S hS hfin Sₙ hSₙ hsum hLaw,
    Measure.map_map (measurable_of_countable _)
      (measurable_pi_lambda _ (fun i => measurable_count j (S i) (hS i)))]
  apply Measure.map_congr
  filter_upwards [ae_all_iff.mpr (fun i => ae_countingMeasure_eq_count j (S i) (hS i) (hfin i))]
    with ω hω
  exact funext hω

end CarryingCapacity.MarkedSetPoissonLimit
