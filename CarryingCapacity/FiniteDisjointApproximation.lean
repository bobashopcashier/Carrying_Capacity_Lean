import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Summable disjoint approximations in a measure-dense set algebra

A finite disjoint family of measurable sets of finite measure can be
approximated by finite disjoint families in a measure-dense algebra. The
symmetric-difference errors are summable. Disjointification only increases
an individual error by the sum of the original finite family's errors.
-/

noncomputable section
open MeasureTheory Set Filter symmDiff
open scoped ENNReal BigOperators

namespace CarryingCapacity.FiniteDisjointApproximation

variable {X : Type*} {k : ℕ}

/-- Retain a point only in the earliest member of a finite family. -/
def disjointify (S : Fin k → Set X) (i : Fin k) : Set X :=
  S i \ ⋃ j ∈ Finset.Iio i, S j

theorem pairwise_disjointify (S : Fin k → Set X) :
    Pairwise (fun i j => Disjoint (disjointify S i) (disjointify S j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hj.2 (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_Iio.mpr hlt, hi.1⟩⟩)
  · exact hi.2 (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨Finset.mem_Iio.mpr hgt, hj.1⟩⟩)

theorem disjointify_mem {𝒜 : Set (Set X)} (h𝒜 : IsSetAlgebra 𝒜)
    (S : Fin k → Set X) (hS : ∀ i, S i ∈ 𝒜) (i : Fin k) :
    disjointify S i ∈ 𝒜 :=
  h𝒜.diff_mem (hS i) (h𝒜.biUnion_mem _ (fun j _ => hS j))

/-- Overlap removal costs at most all original approximation errors. -/
theorem symmDiff_disjointify_subset (S T : Fin k → Set X)
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (i : Fin k) :
    disjointify T i ∆ S i ⊆ ⋃ j, T j ∆ S j := by
  intro x hx
  rcases hx with hx | hx
  · exact mem_iUnion.mpr ⟨i, Or.inl ⟨hx.1.1, hx.2⟩⟩
  · by_cases hTi : x ∈ T i
    · have hprevious : x ∈ ⋃ j ∈ Finset.Iio i, T j := by
        by_contra hn
        exact hx.2 ⟨hTi, hn⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp hprevious
      obtain ⟨hji, hxj⟩ := mem_iUnion.mp hj
      have hnot : x ∉ S j := fun h =>
        Set.disjoint_left.mp (hS (ne_of_lt (Finset.mem_Iio.mp hji))) h hx.1
      exact mem_iUnion.mpr ⟨j, Or.inl ⟨hxj, hnot⟩⟩
    · exact mem_iUnion.mpr ⟨i, Or.inr ⟨hx.1, hTi⟩⟩

variable [MeasurableSpace X]

/-- A measure-dense algebra admits simultaneous, disjoint, summably accurate
approximations of any finite disjoint finite-measure family. -/
theorem exists_disjoint_summable_approximation
    (ν : Measure X) (𝒜 : Set (Set X)) (h𝒜 : IsSetAlgebra 𝒜)
    (hdense : ν.MeasureDense 𝒜) (S : Fin k → Set X)
    (hS : ∀ i, MeasurableSet (S i)) (hfin : ∀ i, ν (S i) ≠ ∞)
    (hdis : Pairwise (fun i j => Disjoint (S i) (S j))) :
    ∃ Sₙ : ℕ → Fin k → Set X,
      (∀ n i, Sₙ n i ∈ 𝒜) ∧
      (∀ n, Pairwise (fun i j => Disjoint (Sₙ n i) (Sₙ n j))) ∧
      (∀ n i, ν (Sₙ n i) ≠ ∞) ∧
      ∀ i, (∑' n, ν (Sₙ n i ∆ S i)) ≠ ∞ := by
  have hchoose (n : ℕ) (i : Fin k) : ∃ T ∈ 𝒜,
      ν (S i ∆ T) < ENNReal.ofReal ((1 / 2 : ℝ) ^ n) :=
    hdense.approx (S i) (hS i) (hfin i) _ (pow_pos (by norm_num) n)
  choose T hT herror using hchoose
  refine ⟨fun n => disjointify (T n), ?_, ?_, ?_, ?_⟩
  · exact fun n i => disjointify_mem h𝒜 (T n) (hT n) i
  · exact fun n => pairwise_disjointify (T n)
  · intro n i
    apply measure_ne_top_of_subset (show disjointify (T n) i ⊆ T n i from fun _ h => h.1)
    exact (measure_ne_top_iff_of_symmDiff (ne_top_of_lt (herror n i))).mp (hfin i)
  · intro i
    have herr (n : ℕ) : ν (disjointify (T n) i ∆ S i) ≤
        (k : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n := by
      calc
        _ ≤ ν (⋃ j, T n j ∆ S j) := measure_mono (symmDiff_disjointify_subset S (T n) hdis i)
        _ ≤ ∑ j, ν (T n j ∆ S j) := measure_iUnion_fintype_le ν _
        _ ≤ ∑ _j : Fin k, (2 : ℝ≥0∞)⁻¹ ^ n := by
          apply Finset.sum_le_sum
          intro j _
          have h := (herror n j).le
          have he : ENNReal.ofReal ((1 / 2 : ℝ) ^ n) = (2 : ℝ≥0∞)⁻¹ ^ n := by
            rw [ENNReal.ofReal_pow (by norm_num)]
            congr 1
            rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
            norm_num
          rw [he] at h
          simpa only [symmDiff_comm] using h
        _ = _ := by simp
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum herr)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.mul_ne_top (by simp) (by norm_num)

/-- Reindexing supplies the same approximation for every finite index type. -/
theorem exists_disjoint_summable_approximation_fintype {ι : Type*} [Fintype ι]
    (ν : Measure X) (𝒜 : Set (Set X)) (h𝒜 : IsSetAlgebra 𝒜)
    (hdense : ν.MeasureDense 𝒜) (S : ι → Set X)
    (hS : ∀ i, MeasurableSet (S i)) (hfin : ∀ i, ν (S i) ≠ ∞)
    (hdis : Pairwise (fun i j => Disjoint (S i) (S j))) :
    ∃ Sₙ : ℕ → ι → Set X,
      (∀ n i, Sₙ n i ∈ 𝒜) ∧
      (∀ n, Pairwise (fun i j => Disjoint (Sₙ n i) (Sₙ n j))) ∧
      (∀ n i, ν (Sₙ n i) ≠ ∞) ∧
      ∀ i, (∑' n, ν (Sₙ n i ∆ S i)) ≠ ∞ := by
  let e := Fintype.equivFin ι
  obtain ⟨Sₙ, hmem, hd, hf, hs⟩ := exists_disjoint_summable_approximation ν 𝒜 h𝒜 hdense
    (fun i => S (e.symm i)) (fun i => hS (e.symm i)) (fun i => hfin (e.symm i))
    (fun _ _ hij => hdis (e.symm.injective.ne hij))
  refine ⟨fun n i => Sₙ n (e i), fun n i => hmem n (e i),
    fun n _ _ hij => hd n (e.injective.ne hij), fun n i => hf n (e i), ?_⟩
  intro i
  simpa only [Equiv.symm_apply_apply] using hs (e i)

end CarryingCapacity.FiniteDisjointApproximation
