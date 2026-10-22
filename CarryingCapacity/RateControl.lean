import CarryingCapacity.Framework
import CarryingCapacity.FiniteGenerator

/-!
# Activity and finite localization sets

These are deterministic connections used by the frozen construction. Every
admissible jump has adapted length at least one, so weighted activity controls
total jump rate. A finite system's empirical Lyapunov sublevel is a finite set.
No stochastic construction or exit estimate is asserted here.
-/

noncomputable section
open scoped BigOperators

namespace CarryingCapacity

namespace Jump

/-- Each admissible birth, death, or type transition changes at least one
coordinate by one, hence its adapted length is at least one. -/
theorem one_le_adaptedDistance_advance {D : ℕ} (κ : MomentScale)
    (h : Jump D) (x : State D) (hx : Admissible h x) :
    1 ≤ adaptedDistance κ (advance h x) x := by
  rcases h with (i | i) | ⟨⟨i,j⟩, hij⟩
  · have hs := κ.step (x i)
    have hc := coordinateDistance_le κ (advance (birth i) x) x i
    simp only [birth, advance, Function.update_self] at hc
    simpa only [advance, if_pos hx] using (hs.trans (le_abs_self _)).trans hc
  · change 0 < x i at hx
    have hn : x i - 1 + 1 = x i := Nat.sub_add_cancel (by omega)
    have hs := κ.step (x i - 1)
    rw [hn] at hs
    have hc := coordinateDistance_le κ (advance (death i) x) x i
    simp only [death, advance, if_pos hx, Function.update_self] at hc
    rw [abs_sub_comm] at hc
    simpa only [advance, if_pos hx] using (hs.trans (le_abs_self _)).trans hc
  · change 0 < x i at hx
    have hn : x i - 1 + 1 = x i := Nat.sub_add_cancel (by omega)
    have hs := κ.step (x i - 1)
    rw [hn] at hs
    have hc := coordinateDistance_le κ (advance (mutation i j hij) x) x i
    simp only [mutation, advance, if_pos hx, Function.update_of_ne hij,
      Function.update_self] at hc
    rw [abs_sub_comm] at hc
    simpa only [advance, if_pos hx] using (hs.trans (le_abs_self _)).trans hc

end Jump

/-- The activity bound controls the total number of jumps, because invalid
jumps have zero rate and every valid jump has adapted length at least one. -/
theorem totalRate_le_weightedActivity {D : ℕ} (κ : MomentScale)
    (q : Rates D (MomentLaw κ D)) (x : State D) (μ : MomentLaw κ D) :
    q.totalRate x μ ≤ weightedActivity κ q x μ := by
  unfold Rates.totalRate weightedActivity
  apply Finset.sum_le_sum
  intro h _
  by_cases hh : Jump.Admissible h x
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Jump.one_le_adaptedDistance_advance κ h x hh) (q.nonnegative h x μ)
  · simp [q.invalid_zero h x μ hh]

/-- Configuration sublevels of an empirical Lyapunov function are finite.
The initial configuration need not belong to such a sublevel; in that case the
frozen construction leaves that initial state fixed. -/
theorem finite_configuration_lyapunov_sublevel {D N : ℕ} (hN : 0 < N)
    (κ : MomentScale) (Ψ : State D → ℝ)
    (hΨ : ∀ x, momentWeight κ x ≤ Ψ x) (R : ℝ) :
    {z : Fin N → State D | FiniteGenerator.empiricalMean Ψ z < R}.Finite := by
  apply (Set.finite_Iic (fun _ : Fin N => fun _ : Fin D => Nat.ceil ((N : ℝ) * R))).subset
  intro z hz i j
  have hnonneg : ∀ k : Fin N, 0 ≤ Ψ (z k) :=
    fun k => (momentWeight_nonneg κ (z k)).trans (hΨ (z k))
  have hcoord : (z i j : ℝ) ≤ momentWeight κ (z i) := by
    apply (κ.nat_le_value (z i j)).trans
    exact Finset.single_le_sum (fun k _ => κ.value_nonneg (z i k)) (Finset.mem_univ j)
  have hsum : Ψ (z i) ≤ ∑ k, Ψ (z k) :=
    Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ i)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hidentity : (∑ k, Ψ (z k)) =
      (N : ℝ) * FiniteGenerator.empiricalMean Ψ z := by
    unfold FiniteGenerator.empiricalMean
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hNr), one_mul]
  have hbound : (z i j : ℝ) ≤ (N : ℝ) * R := by
    calc
      (z i j : ℝ) ≤ momentWeight κ (z i) := hcoord
      _ ≤ Ψ (z i) := hΨ (z i)
      _ ≤ ∑ k, Ψ (z k) := hsum
      _ = (N : ℝ) * FiniteGenerator.empiricalMean Ψ z := hidentity
      _ ≤ (N : ℝ) * R := mul_le_mul_of_nonneg_left (le_of_lt hz) (le_of_lt hNr)
  have hceil : (z i j : ℝ) ≤ (Nat.ceil ((N : ℝ) * R) : ℝ) :=
    hbound.trans (Nat.le_ceil _)
  exact_mod_cast hceil

end CarryingCapacity
