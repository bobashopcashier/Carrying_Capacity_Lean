import CarryingCapacity.ConfigurationLocalization

/-!
# Finite backward jump support on the configuration lattice

Each predecessor coordinate is at most the corresponding post-jump coordinate
plus one. Therefore a finite set has finitely many one-jump predecessors.
A finitely supported test function can change only on the resulting finite
influence set. Its raw configuration generator is consequently finitely
supported and bounded, even when the rates are globally unbounded.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators

namespace CarryingCapacity.FiniteSupportGeometry
open ConfigurationLocalization

variable {N D : ℕ}

/-- Birth, death and mutation decrease each coordinate by at most one. -/
theorem coordinate_le_advance_add_one (h : Jump D) (x : State D) (k : Fin D) :
    x k ≤ Jump.advance h x k + 1 := by
  rcases h with (i | i) | ⟨⟨i,j⟩, hij⟩
  · by_cases hk : k = i
    · subst k
      simp only [Jump.advance, Function.update_self]
      omega
    · simp [Jump.advance, Function.update_of_ne hk]
  · by_cases hi : 0 < x i <;> by_cases hk : k = i
    · subst k
      simp only [Jump.advance, if_pos hi, Function.update_self]
      omega
    · simp [Jump.advance, hi, Function.update_of_ne hk]
    · simp [Jump.advance, hi]
    · simp [Jump.advance, hi]
  · by_cases hi : 0 < x i
    · by_cases hkj : k = j
      · subst k
        simp only [Jump.advance, if_pos hi, Function.update_self]
        omega
      · by_cases hki : k = i
        · subst k
          simp only [Jump.advance, if_pos hi, Function.update_of_ne hij, Function.update_self]
          omega
        · simp [Jump.advance, hi, Function.update_of_ne hkj, Function.update_of_ne hki]
    · simp [Jump.advance, hi]

/-- The same coordinate control holds for a one-particle configuration update. -/
theorem coordinate_le_jump_add_one (h : Label N D) (z : Configuration N D)
    (i : Fin N) (k : Fin D) : z i k ≤ jump h z i k + 1 := by
  by_cases hi : i = h.1
  · subst i
    simpa only [jump, Function.update_self] using coordinate_le_advance_add_one h.2 (z h.1) k
  · simp [jump, Function.update_of_ne hi]

/-- Every fiber of an actual configuration jump is finite. -/
theorem finite_jump_fiber (h : Label N D) (y : Configuration N D) :
    {z : Configuration N D | jump h z = y}.Finite := by
  apply (Set.finite_Iic (fun i : Fin N => fun k : Fin D => y i k + 1)).subset
  intro z hz i k
  change jump h z = y at hz
  simpa only [hz] using coordinate_le_jump_add_one h z i k

theorem finite_jump_preimage (h : Label N D) (s : Set (Configuration N D))
    (hs : s.Finite) : (jump h ⁻¹' s).Finite := by
  have hf : (⋃ y ∈ s, {z : Configuration N D | jump h z = y}).Finite :=
    hs.biUnion (fun y _ => finite_jump_fiber h y)
  apply hf.subset
  intro z hz
  exact mem_iUnion.mpr ⟨jump h z, mem_iUnion.mpr ⟨hz, rfl⟩⟩

/-- States at which F itself or one of its one-jump successor values can be nonzero. -/
def influenceSet (F : Configuration N D → ℝ) : Set (Configuration N D) :=
  Function.support F ∪ ⋃ h : Label N D, jump h ⁻¹' Function.support F

theorem finite_influenceSet (F : Configuration N D → ℝ) (hF : (Function.support F).Finite) :
    (influenceSet F).Finite :=
  hF.union (Set.finite_iUnion (fun h => finite_jump_preimage h (Function.support F) hF))

/-- The deterministic finite set relevant to a finitely supported test function. -/
def influence (F : Configuration N D → ℝ) (hF : (Function.support F).Finite) :
    Finset (Configuration N D) := (finite_influenceSet F hF).toFinset

@[simp] theorem mem_influence (F : Configuration N D → ℝ)
    (hF : (Function.support F).Finite) (z : Configuration N D) :
    z ∈ influence F hF ↔ F z ≠ 0 ∨ ∃ h : Label N D, F (jump h z) ≠ 0 := by
  simp only [influence, Set.Finite.mem_toFinset, influenceSet, mem_union, mem_iUnion,
    mem_preimage, Function.mem_support]

theorem increment_eq_zero_of_not_mem (F : Configuration N D → ℝ)
    (hF : (Function.support F).Finite) (z : Configuration N D)
    (hz : z ∉ influence F hF) (h : Label N D) : F (jump h z) - F z = 0 := by
  have hx : F z = 0 := by
    by_contra hx
    exact hz ((mem_influence F hF z).mpr (Or.inl hx))
  have hy : F (jump h z) = 0 := by
    by_contra hy
    exact hz ((mem_influence F hF z).mpr (Or.inr ⟨h, hy⟩))
  simp only [hx, hy, sub_self]

/-- A deterministic bound for F itself. -/
def functionBound (F : Configuration N D → ℝ) (hF : (Function.support F).Finite) : ℝ :=
  ∑ z ∈ hF.toFinset, |F z|

theorem norm_le_functionBound (F : Configuration N D → ℝ)
    (hF : (Function.support F).Finite) (z : Configuration N D) :
    ‖F z‖ ≤ functionBound F hF := by
  by_cases hz : F z = 0
  · rw [hz, norm_zero]
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  · change |F z| ≤ ∑ y ∈ hF.toFinset, |F y|
    exact Finset.single_le_sum (f := fun y : Configuration N D => |F y|)
      (fun _ _ => abs_nonneg _) (hF.mem_toFinset.mpr hz)

variable (κ : MomentScale) (q : Rates D (MomentLaw κ D)) (hN : 0 < N)
  (F : Configuration N D → ℝ) (hF : (Function.support F).Finite)

theorem generator_eq_zero_of_not_mem (z : Configuration N D) (hz : z ∉ influence F hF) :
    generator κ q hN F z = 0 := by
  unfold generator
  simp only [increment_eq_zero_of_not_mem F hF z hz, mul_zero, Finset.sum_const_zero]

include hF

/-- Globally unbounded rates still produce a finitely supported generator on F. -/
theorem finite_generator_support : (Function.support (generator κ q hN F)).Finite := by
  apply (finite_influenceSet F hF).subset
  intro z hz
  by_contra hn
  have hn' : z ∉ influence F hF := by simpa only [influence, Set.Finite.mem_toFinset] using hn
  exact hz (generator_eq_zero_of_not_mem κ q hN F hF z hn')

def generatorBound : ℝ := ∑ z ∈ influence F hF, |generator κ q hN F z|

theorem norm_generator_le (z : Configuration N D) :
    ‖generator κ q hN F z‖ ≤ generatorBound κ q hN F hF := by
  by_cases hz : z ∈ influence F hF
  · change |generator κ q hN F z| ≤ ∑ y ∈ influence F hF, |generator κ q hN F y|
    exact Finset.single_le_sum (f := fun y : Configuration N D => |generator κ q hN F y|)
      (fun _ _ => abs_nonneg _) hz
  · rw [generator_eq_zero_of_not_mem κ q hN F hF z hz, norm_zero]
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

end CarryingCapacity.FiniteSupportGeometry
