import CarryingCapacity.EmpiricalMeasure
import CarryingCapacity.TransportMetric
import CarryingCapacity.TimeGridRefinement

/-!
# Deterministic time-grid bounds for actual empirical moment laws

The indexwise coupling and the transport triangle inequality give the exact
cell estimate used in Section 6. A monotone finite grid then converts bounds
on its empirical errors and centered average variations into a bound at every
real time. These are deterministic statements: no stochastic variation bound,
independence, law of large numbers, or uniform convergence is asserted here.
-/

noncomputable section
open Set
open scoped Classical BigOperators ENNReal

namespace CarryingCapacity.EmpiricalTimeGrid

variable {N D : ℕ} (κ : MomentScale) (hN : 0 < N)

/-- The empirical average of the coordinate variation bounds on one cell. -/
def meanVariation (V : Fin N → ℝ) : ℝ := (N : ℝ)⁻¹ * ∑ i, V i

/-- A deterministic coordinate displacement bound controls the genuine
empirical Wasserstein distance by its normalized average. -/
theorem empirical_distance_le_meanVariation (z w : Fin N → State D)
    (V : Fin N → ℝ) (hV : ∀ i, adaptedDistance κ (z i) (w i) ≤ V i) :
    wasserstein (empiricalLaw κ hN z) (empiricalLaw κ hN w) ≤ meanVariation V := by
  apply (wasserstein_empiricalLaw_le κ hN z w).trans
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hV i)) (by positivity)

/-- The Section 6 cell estimate uses the empirical error at the left endpoint,
actual coordinate variations, and the deterministic marginal-law modulus. -/
theorem error_le_cell (z w : Fin N → State D) (μ ν : MomentLaw κ D)
    (V : Fin N → ℝ) (hV : ∀ i, adaptedDistance κ (z i) (w i) ≤ V i) :
    wasserstein (empiricalLaw κ hN z) μ ≤
      wasserstein (empiricalLaw κ hN w) ν + meanVariation V + wasserstein ν μ := by
  have h1 := wasserstein_triangle (empiricalLaw κ hN z) (empiricalLaw κ hN w) μ
  have h2 := wasserstein_triangle (empiricalLaw κ hN w) ν μ
  have h3 := empirical_distance_le_meanVariation κ hN z w V hV
  linarith

/-- Centering the empirical variation isolates precisely the scalar error
that the interval-variation law of large numbers must control. -/
theorem error_le_cell_centered (z w : Fin N → State D) (μ ν : MomentLaw κ D)
    (V : Fin N → ℝ) (hV : ∀ i, adaptedDistance κ (z i) (w i) ≤ V i)
    (b L : ℝ) (hb : b ≤ L) (hmod : wasserstein ν μ ≤ L) :
    wasserstein (empiricalLaw κ hN z) μ ≤
      wasserstein (empiricalLaw κ hN w) ν + |meanVariation V - b| + 2 * L := by
  have h := error_le_cell κ hN z w μ ν V hV
  have ha := le_abs_self (meanVariation V - b)
  linarith

/-- Grid-point errors and centered cell averages control the empirical error
at every real time. The initial endpoint and a zero horizon are included. -/
theorem error_le_of_grid {m : ℕ} (u : Fin (m + 1) → ℝ) (hu : Monotone u)
    (T : ℝ) (hu0 : u 0 = 0) (huT : u (Fin.last m) = T)
    (z : ℝ → Fin N → State D) (v : ℝ → MomentLaw κ D)
    (V : Fin m → Fin N → ℝ) (b : Fin m → ℝ)
    (G A L : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hgrid : ∀ j, wasserstein (empiricalLaw κ hN (z (u j))) (v (u j)) ≤ G)
    (hdisp : ∀ (j : Fin m) (t : ℝ), t ∈ Ioc (u j.castSucc) (u j.succ) →
      ∀ i, adaptedDistance κ (z t i) (z (u j.castSucc) i) ≤ V j i)
    (hmean : ∀ j, b j ≤ L)
    (hmod : ∀ (j : Fin m) (t : ℝ), t ∈ Ioc (u j.castSucc) (u j.succ) →
      wasserstein (v (u j.castSucc)) (v t) ≤ L)
    (hcenter : ∀ j, |meanVariation (V j) - b j| ≤ A)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    wasserstein (empiricalLaw κ hN (z t)) (v t) ≤ G + A + 2 * L := by
  by_cases ht0 : t = 0
  · subst t
    have h := hgrid 0
    rw [hu0] at h
    linarith
  · have ht' : t ∈ Ioc (u 0) (u (Fin.last m)) := by
      rw [hu0, huT]
      exact ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
    obtain ⟨j, hj⟩ := (TimeGridRefinement.mem_grid_iff u hu t).mp ht'
    have h := error_le_cell_centered κ hN (z t) (z (u j.castSucc)) (v t) (v (u j.castSucc))
      (V j) (hdisp j t hj) (b j) L (hmean j) (hmod j t hj)
    linarith [hgrid j.castSucc, hcenter j]

/-- The same estimate for the genuine supremum over all real times. Taking
this supremum does not silently require a measurability assumption. -/
theorem supremum_error_le_of_grid {m : ℕ} (u : Fin (m + 1) → ℝ) (hu : Monotone u)
    (T : ℝ) (hu0 : u 0 = 0) (huT : u (Fin.last m) = T)
    (z : ℝ → Fin N → State D) (v : ℝ → MomentLaw κ D)
    (V : Fin m → Fin N → ℝ) (b : Fin m → ℝ)
    (G A L : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hgrid : ∀ j, wasserstein (empiricalLaw κ hN (z (u j))) (v (u j)) ≤ G)
    (hdisp : ∀ (j : Fin m) (t : ℝ), t ∈ Ioc (u j.castSucc) (u j.succ) →
      ∀ i, adaptedDistance κ (z t i) (z (u j.castSucc) i) ≤ V j i)
    (hmean : ∀ j, b j ≤ L)
    (hmod : ∀ (j : Fin m) (t : ℝ), t ∈ Ioc (u j.castSucc) (u j.succ) →
      wasserstein (v (u j.castSucc)) (v t) ≤ L)
    (hcenter : ∀ j, |meanVariation (V j) - b j| ≤ A) :
    (⨆ t : Icc (0 : ℝ) T, ENNReal.ofReal (wasserstein (empiricalLaw κ hN (z t)) (v t))) ≤
      ENNReal.ofReal (G + A + 2 * L) := by
  apply iSup_le
  intro t
  exact ENNReal.ofReal_le_ofReal (error_le_of_grid κ hN u hu T hu0 huT z v V b G A L
    hA hL hgrid hdisp hmean hmod hcenter t t.property)

/-- The manuscript's equally spaced deterministic grid. -/
def uniformGrid (T : ℝ) (m : ℕ) (i : Fin (m + 1)) : ℝ := (i : ℕ) * T / m

theorem uniformGrid_monotone (T : ℝ) (hT : 0 ≤ T) (m : ℕ) :
    Monotone (uniformGrid T m) := by
  intro i j hij
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hT) (Nat.cast_nonneg m)

@[simp] theorem uniformGrid_zero (T : ℝ) (m : ℕ) : uniformGrid T m 0 = 0 := by
  simp [uniformGrid]

@[simp] theorem uniformGrid_last (T : ℝ) (m : ℕ) (hm : 0 < m) :
    uniformGrid T m (Fin.last m) = T := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  simp [uniformGrid, mul_div_cancel_left₀, hm']

/-- Every adjacent grid cell has the exact mesh T/m. -/
theorem uniformGrid_mesh (T : ℝ) (m : ℕ) (j : Fin m) :
    uniformGrid T m j.succ - uniformGrid T m j.castSucc = T / m := by
  simp only [uniformGrid, Fin.val_succ, Fin.coe_castSucc, Nat.cast_add, Nat.cast_one]
  ring

end CarryingCapacity.EmpiricalTimeGrid
