import Mathlib

/-!
# Finite-system generator identities

The algebra below is the deterministic identity used in Section 3 of the revised
paper. It does not construct a stochastic process. The law-valued map `empirical`
may be the empirical probability measure, but the generator identity only needs
it to be a function of the configuration.
-/

noncomputable section
open scoped BigOperators

namespace CarryingCapacity.FiniteGenerator

variable {α H Law : Type*} [Fintype H] {N : ℕ}

/-- An empirical average of a real test function. -/
def empiricalMean (f : α → ℝ) (z : Fin N → α) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, f (z i)

/-- One-lineage generator in a prescribed environment. -/
def singleGenerator (transition : H → α → α) (rate : H → α → Law → ℝ)
    (μ : Law) (f : α → ℝ) (x : α) : ℝ :=
  ∑ h, rate h x μ * (f (transition h x) - f x)

/-- The full configuration generator updates one lineage at a time. -/
def systemGenerator (transition : H → α → α) (rate : H → α → Law → ℝ)
    (empirical : (Fin N → α) → Law) (F : (Fin N → α) → ℝ)
    (z : Fin N → α) : ℝ :=
  ∑ i, ∑ h, rate h (z i) (empirical z) *
    (F (Function.update z i (transition h (z i))) - F z)

/-- Updating a single lineage changes an empirical average by its scaled increment. -/
theorem empiricalMean_update_sub (f : α → ℝ) (z : Fin N → α)
    (i : Fin N) (y : α) :
    empiricalMean f (Function.update z i y) - empiricalMean f z =
      (N : ℝ)⁻¹ * (f y - f (z i)) := by
  classical
  unfold empiricalMean
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · simp

/-- Generator/empirical-average identity, including the factor `1/N`.

This is valid even for `N = 0` under Lean's convention `0⁻¹ = 0`; the
probabilistic interpretation and the drift estimate below use `N > 0`.
-/
theorem systemGenerator_empiricalMean (transition : H → α → α)
    (rate : H → α → Law → ℝ) (empirical : (Fin N → α) → Law)
    (f : α → ℝ) (z : Fin N → α) :
    systemGenerator transition rate empirical (empiricalMean f) z =
      (N : ℝ)⁻¹ * ∑ i, singleGenerator transition rate (empirical z) f (z i) := by
  classical
  simp only [systemGenerator, empiricalMean_update_sub, singleGenerator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- Averaging a one-lineage Lyapunov drift bound closes the finite-system drift.

The environment term is the same empirical average for every lineage, so it
contributes exactly a second copy of that average. This is an algebraic theorem,
not an invocation of Dynkin's formula or a claim of non-explosion.
-/
theorem averaged_lyapunov_drift (hN : 0 < N)
    (transition : H → α → α) (rate : H → α → Law → ℝ)
    (empirical : (Fin N → α) → Law) (ψ : α → ℝ) (C : ℝ)
    (z : Fin N → α)
    (hdrift : ∀ i, singleGenerator transition rate (empirical z) ψ (z i) ≤
      C * (1 + ψ (z i) + empiricalMean ψ z)) :
    systemGenerator transition rate empirical (empiricalMean ψ) z ≤
      C * (1 + 2 * empiricalMean ψ z) := by
  classical
  rw [systemGenerator_empiricalMean]
  calc
    (N : ℝ)⁻¹ * ∑ i, singleGenerator transition rate (empirical z) ψ (z i) ≤
        (N : ℝ)⁻¹ * ∑ i, C * (1 + ψ (z i) + empiricalMean ψ z) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hdrift i)
        (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ = C * (1 + 2 * empiricalMean ψ z) := by
      rw [← Finset.mul_sum]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
      unfold empiricalMean
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      field_simp [hNr]
      ring_nf
      simp

end CarryingCapacity.FiniteGenerator
