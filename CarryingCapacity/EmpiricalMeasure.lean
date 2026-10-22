import CarryingCapacity.Transport
import CarryingCapacity.FiniteGenerator

/-!
# Empirical probability laws and paired transport

Finite configurations give genuine probability measures, with every real test
function integrable. Their integral identity connects the measure-theoretic
moment and transport definitions to the finite-system generator calculations.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace CarryingCapacity

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {N D : ℕ}

/-- The normalized sum of Dirac masses of a finite configuration. -/
def empiricalMeasure (z : Fin N → α) : Measure α :=
  (N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (z i)

/-- A positive population size makes the empirical measure a probability law. -/
theorem empiricalMeasure_probability (hN : 0 < N) (z : Fin N → α) :
    IsProbabilityMeasure (empiricalMeasure z) := by
  constructor
  have hne : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp [empiricalMeasure, Measure.finset_sum_apply, ENNReal.inv_mul_cancel hne (by simp)]

/-- Finite support makes every real-valued test function integrable. -/
theorem integrable_empiricalMeasure [MeasurableSingletonClass α]
    (hN : 0 < N) (z : Fin N → α) (f : α → ℝ) :
    Integrable f (empiricalMeasure z) := by
  apply Integrable.smul_measure
  · exact integrable_finset_sum_measure.mpr fun i _ => integrable_dirac
  · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast (Nat.ne_of_gt hN))

/-- Empirical integration is exactly the arithmetic mean, with repetitions counted. -/
theorem integral_empiricalMeasure [MeasurableSingletonClass α]
    (z : Fin N → α) (f : α → ℝ) :
    (∫ x, f x ∂empiricalMeasure z) = FiniteGenerator.empiricalMean f z := by
  rw [empiricalMeasure, integral_smul_measure,
    integral_finset_sum_measure (fun i _ => integrable_dirac)]
  simp [FiniteGenerator.empiricalMean, ENNReal.toReal_inv]

/-- Pushforward commutes with formation of an empirical measure. -/
theorem map_empiricalMeasure (z : Fin N → α) (f : α → β) (hf : Measurable f) :
    Measure.map f (empiricalMeasure z) = empiricalMeasure (fun i => f (z i)) := by
  unfold empiricalMeasure
  rw [Measure.map_smul]
  congr 1
  rw [← Measure.mapₗ_apply_of_measurable hf, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.mapₗ_apply_of_measurable hf, Measure.map_dirac hf]

/-- Index relabeling leaves the empirical measure unchanged. -/
@[simp] theorem empiricalMeasure_relabel (z : Fin N → α) (e : Equiv.Perm (Fin N)) :
    empiricalMeasure (z ∘ e) = empiricalMeasure z := by
  unfold empiricalMeasure
  congr 1
  exact Equiv.sum_comp e (fun i => Measure.dirac (z i))

variable (κ : MomentScale)

/-- The empirical probability law has every discrete κ-moment finite. -/
def empiricalLaw (hN : 0 < N) (z : Fin N → State D) : MomentLaw κ D where
  measure := empiricalMeasure z
  probability := empiricalMeasure_probability hN z
  integrable_weight := integrable_empiricalMeasure hN z (momentWeight κ)

@[simp] theorem empiricalLaw_measure (hN : 0 < N) (z : Fin N → State D) :
    (empiricalLaw κ hN z).measure = empiricalMeasure z := rfl

/-- Index relabeling leaves the full moment-law object unchanged. -/
@[simp] theorem empiricalLaw_relabel (hN : 0 < N) (z : Fin N → State D)
    (e : Equiv.Perm (Fin N)) :
    empiricalLaw κ hN (z ∘ e) = empiricalLaw κ hN z := by
  have h := empiricalMeasure_relabel z e
  cases a : empiricalLaw κ hN (z ∘ e)
  cases b : empiricalLaw κ hN z
  simp only [← empiricalLaw_measure κ hN] at h
  rw [a, b] at h
  cases h
  rfl

@[simp] theorem integral_empiricalLaw (hN : 0 < N) (z : Fin N → State D)
    (f : State D → ℝ) :
    (∫ x, f x ∂(empiricalLaw κ hN z).measure) =
      FiniteGenerator.empiricalMean f z :=
  integral_empiricalMeasure z f

@[simp] theorem moment_empiricalLaw (hN : 0 < N) (z : Fin N → State D) :
    moment (empiricalLaw κ hN z) = FiniteGenerator.empiricalMean (momentWeight κ) z :=
  integral_empiricalMeasure z (momentWeight κ)

namespace Coupling

/-- Pairing equal particle indices gives a genuine coupling of empirical laws. -/
def paired (hN : 0 < N) (z w : Fin N → State D) :
    Coupling (empiricalLaw κ hN z) (empiricalLaw κ hN w) where
  measure := empiricalMeasure (fun i => (z i, w i))
  first_marginal := map_empiricalMeasure _ Prod.fst measurable_fst
  second_marginal := map_empiricalMeasure _ Prod.snd measurable_snd

@[simp] theorem cost_paired (hN : 0 < N) (z w : Fin N → State D) :
    (paired κ hN z w).cost =
      (N : ℝ)⁻¹ * ∑ i, adaptedDistance κ (z i) (w i) := by
  exact integral_empiricalMeasure (fun i => (z i, w i))
    (fun p => adaptedDistance κ p.1 p.2)

end Coupling

/-- Empirical transport is bounded by the mean distance of any given pairing. -/
theorem wasserstein_empiricalLaw_le (hN : 0 < N) (z w : Fin N → State D) :
    wasserstein (empiricalLaw κ hN z) (empiricalLaw κ hN w) ≤
      (N : ℝ)⁻¹ * ∑ i, adaptedDistance κ (z i) (w i) := by
  simpa using wasserstein_le_cost (Coupling.paired κ hN z w)

/-- Any permutation of the second configuration yields a valid pairing bound. -/
theorem wasserstein_empiricalLaw_le_permuted (hN : 0 < N)
    (z w : Fin N → State D) (e : Equiv.Perm (Fin N)) :
    wasserstein (empiricalLaw κ hN z) (empiricalLaw κ hN w) ≤
      (N : ℝ)⁻¹ * ∑ i, adaptedDistance κ (z i) (w (e i)) := by
  simpa using wasserstein_empiricalLaw_le κ hN z (w ∘ e)

/-- A single-particle update moves the empirical law by at most its scaled jump length. -/
theorem wasserstein_empiricalLaw_update_le (hN : 0 < N)
    (z : Fin N → State D) (i : Fin N) (y : State D) :
    wasserstein (empiricalLaw κ hN z) (empiricalLaw κ hN (Function.update z i y)) ≤
      (N : ℝ)⁻¹ * adaptedDistance κ (z i) y := by
  classical
  convert wasserstein_empiricalLaw_le κ hN z (Function.update z i y) using 1
  congr 1
  symm
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · simp

section Generator

variable {H : Type*} [Fintype H]

/-- Exact finite-system generator identity for actual empirical-law integrals. -/
theorem systemGenerator_empiricalIntegral (hN : 0 < N)
    (transition : H → State D → State D)
    (rate : H → State D → MomentLaw κ D → ℝ) (f : State D → ℝ)
    (z : Fin N → State D) :
    FiniteGenerator.systemGenerator transition rate (empiricalLaw κ hN)
      (fun w => ∫ x, f x ∂(empiricalLaw κ hN w).measure) z =
      ∫ x, FiniteGenerator.singleGenerator transition rate (empiricalLaw κ hN z) f x
        ∂(empiricalLaw κ hN z).measure := by
  simp only [integral_empiricalLaw]
  exact FiniteGenerator.systemGenerator_empiricalMean transition rate (empiricalLaw κ hN) f z

/-- The Lyapunov drift calculation applies directly to genuine empirical measures. -/
theorem empiricalIntegral_lyapunov_drift (hN : 0 < N)
    (transition : H → State D → State D)
    (rate : H → State D → MomentLaw κ D → ℝ) (ψ : State D → ℝ) (C : ℝ)
    (z : Fin N → State D)
    (hdrift : ∀ i, FiniteGenerator.singleGenerator transition rate (empiricalLaw κ hN z)
      ψ (z i) ≤ C * (1 + ψ (z i) + ∫ x, ψ x ∂(empiricalLaw κ hN z).measure)) :
    FiniteGenerator.systemGenerator transition rate (empiricalLaw κ hN)
      (fun w => ∫ x, ψ x ∂(empiricalLaw κ hN w).measure) z ≤
      C * (1 + 2 * ∫ x, ψ x ∂(empiricalLaw κ hN z).measure) := by
  simp only [integral_empiricalLaw] at hdrift ⊢
  exact FiniteGenerator.averaged_lyapunov_drift hN transition rate (empiricalLaw κ hN)
    ψ C z hdrift

end Generator

end CarryingCapacity
