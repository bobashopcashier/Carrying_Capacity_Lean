import CarryingCapacity.EmpiricalMeasure
import Mathlib.Analysis.Convex.Birkhoff

/-!
# Optimal matching of equal-weight empirical laws

Repeated states are handled by splitting their mass uniformly among all particle
indices carrying that state. An arbitrary coupling therefore lifts to a doubly
stochastic matrix; Birkhoff's theorem then identifies the minimum transport cost
with a permutation matching.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical ENNReal

namespace CarryingCapacity.EmpiricalMatching

variable {D N : ℕ} {κ : MomentScale}

/-- Number of particle labels carrying a given state. -/
def multiplicity (z : Fin N → State D) (x : State D) : ℕ :=
  (Finset.univ.filter (fun i => z i = x)).card

/-- Fraction of an atom assigned to one of its original particle labels. -/
def indexWeight (z : Fin N → State D) (i : Fin N) (x : State D) : ℝ :=
  if x = z i then (multiplicity z (z i) : ℝ)⁻¹ else 0

theorem multiplicity_pos (z : Fin N → State D) (i : Fin N) :
    0 < multiplicity z (z i) := by
  apply Finset.card_pos.mpr
  exact ⟨i, by simp⟩

theorem indexWeight_nonneg (z : Fin N → State D) (i : Fin N) (x : State D) :
    0 ≤ indexWeight z i x := by
  unfold indexWeight
  split_ifs <;> positivity

theorem indexWeight_le_one (z : Fin N → State D) (i : Fin N) (x : State D) :
    indexWeight z i x ≤ 1 := by
  unfold indexWeight
  split_ifs
  · have hm : (1 : ℝ) ≤ multiplicity z (z i) := by exact_mod_cast multiplicity_pos z i
    exact inv_le_one_of_one_le₀ hm
  · norm_num

/-- Splitting restores exactly one unit of mass at every supported state. -/
theorem sum_indexWeight (z : Fin N → State D) (x : State D) (hx : x ∈ Set.range z) :
    ∑ i, indexWeight z i x = 1 := by
  have hm : 0 < multiplicity z x := by
    obtain ⟨i, rfl⟩ := hx
    exact multiplicity_pos z i
  have hsum : (∑ i, indexWeight z i x) =
      (multiplicity z x : ℝ) * (multiplicity z x : ℝ)⁻¹ := by
    calc
      (∑ i, indexWeight z i x) =
          ∑ i, if z i = x then (multiplicity z x : ℝ)⁻¹ else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : z i = x
        · simp [indexWeight, hi]
        · simp [indexWeight, hi, Ne.symm hi]
      _ = _ := by
        rw [← Finset.sum_filter]
        simp [multiplicity]
  rw [hsum, mul_inv_cancel₀]
  exact_mod_cast Nat.ne_of_gt hm

/-- The normalized empirical law assigns exactly mass 1/N to each split label. -/
theorem integral_indexWeight (z : Fin N → State D) (i : Fin N) :
    (∫ x, indexWeight z i x ∂empiricalMeasure z) = (N : ℝ)⁻¹ := by
  rw [integral_empiricalMeasure]
  unfold FiniteGenerator.empiricalMean
  have hs : (∑ j, indexWeight z i (z j)) = 1 := by
    have hsum : (∑ j, indexWeight z i (z j)) =
        (multiplicity z (z i) : ℝ) * (multiplicity z (z i) : ℝ)⁻¹ := by
      simp only [indexWeight]
      rw [← Finset.sum_filter]
      simp [multiplicity]
    rw [hsum, mul_inv_cancel₀]
    exact_mod_cast Nat.ne_of_gt (multiplicity_pos z i)
  rw [hs, mul_one]

/-- Empirical measures are concentrated on the finite configuration range. -/
theorem ae_mem_range (z : Fin N → State D) :
    ∀ᵐ x ∂empiricalMeasure z, x ∈ Set.range z := by
  rw [ae_iff]
  have hs : MeasurableSet {x : State D | ¬x ∈ Set.range z} :=
    Set.to_countable _ |>.measurableSet
  simp [empiricalMeasure, Measure.finset_sum_apply, hs, Measure.dirac_apply']

section CouplingMatrix

variable (hN : 0 < N) (z w : Fin N → State D)
  (c : Coupling (empiricalLaw κ hN z) (empiricalLaw κ hN w))

/-- The arbitrary empirical coupling, lifted to particle labels. -/
def labelMass (i j : Fin N) : ℝ :=
  ∫ p, indexWeight z i p.1 * indexWeight w j p.2 ∂c.measure

theorem integrable_weight_product (i j : Fin N) :
    Integrable (fun p : State D × State D => indexWeight z i p.1 * indexWeight w j p.2)
      c.measure := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (indexWeight_nonneg z i p.1)
      (indexWeight_nonneg w j p.2))]
    exact (mul_le_mul (indexWeight_le_one z i p.1) (indexWeight_le_one w j p.2)
      (indexWeight_nonneg w j p.2) zero_le_one).trans_eq (one_mul 1)

theorem labelMass_nonneg (i j : Fin N) : 0 ≤ labelMass hN z w c i j :=
  integral_nonneg fun p => mul_nonneg (indexWeight_nonneg z i p.1) (indexWeight_nonneg w j p.2)

theorem ae_first_mem_range : ∀ᵐ p ∂c.measure, p.1 ∈ Set.range z := by
  have h := ae_mem_range z
  change ∀ᵐ x ∂(empiricalLaw κ hN z).measure, x ∈ Set.range z at h
  rw [← c.first_marginal] at h
  exact ae_of_ae_map measurable_fst.aemeasurable h

theorem ae_second_mem_range : ∀ᵐ p ∂c.measure, p.2 ∈ Set.range w := by
  have h := ae_mem_range w
  change ∀ᵐ x ∂(empiricalLaw κ hN w).measure, x ∈ Set.range w at h
  rw [← c.second_marginal] at h
  exact ae_of_ae_map measurable_snd.aemeasurable h

theorem labelMass_row (i : Fin N) : ∑ j, labelMass hN z w c i j = (N : ℝ)⁻¹ := by
  unfold labelMass
  rw [← integral_finset_sum _ (fun j _ => integrable_weight_product hN z w c i j)]
  calc
    (∫ p, ∑ j, indexWeight z i p.1 * indexWeight w j p.2 ∂c.measure) =
        ∫ p, indexWeight z i p.1 ∂c.measure := by
      apply integral_congr_ae
      filter_upwards [ae_second_mem_range hN z w c] with p hp
      rw [← Finset.mul_sum, sum_indexWeight w p.2 hp, mul_one]
    _ = (N : ℝ)⁻¹ := by
      rw [← integral_map_of_stronglyMeasurable measurable_fst
        (measurable_of_countable (indexWeight z i)).stronglyMeasurable, c.first_marginal]
      exact integral_indexWeight z i

theorem labelMass_col (j : Fin N) : ∑ i, labelMass hN z w c i j = (N : ℝ)⁻¹ := by
  unfold labelMass
  rw [← integral_finset_sum _ (fun i _ => integrable_weight_product hN z w c i j)]
  calc
    (∫ p, ∑ i, indexWeight z i p.1 * indexWeight w j p.2 ∂c.measure) =
        ∫ p, indexWeight w j p.2 ∂c.measure := by
      apply integral_congr_ae
      filter_upwards [ae_first_mem_range hN z w c] with p hp
      rw [← Finset.sum_mul, sum_indexWeight z p.1 hp, one_mul]
    _ = (N : ℝ)⁻¹ := by
      rw [← integral_map_of_stronglyMeasurable measurable_snd
        (measurable_of_countable (indexWeight w j)).stronglyMeasurable, c.second_marginal]
      exact integral_indexWeight w j

/-- Multiplying the label coupling by N gives a doubly stochastic matrix. -/
theorem labelMass_doublyStochastic :
    (fun i j => (N : ℝ) * labelMass hN z w c i j) ∈ doublyStochastic ℝ (Fin N) := by
  rw [mem_doublyStochastic_iff_sum]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  refine ⟨fun i j => mul_nonneg (Nat.cast_nonneg N) (labelMass_nonneg hN z w c i j), ?_, ?_⟩
  · intro i
    rw [← Finset.mul_sum, labelMass_row hN z w c i, mul_inv_cancel₀ hNr]
  · intro j
    rw [← Finset.mul_sum, labelMass_col hN z w c j, mul_inv_cancel₀ hNr]

/-- Lifting to particle indices preserves the cost exactly, even with repeated states. -/
theorem labelMass_cost :
    (∑ i, ∑ j, labelMass hN z w c i j * adaptedDistance κ (z i) (w j)) = c.cost := by
  let F : Fin N → Fin N → State D × State D → ℝ := fun i j p =>
    indexWeight z i p.1 * indexWeight w j p.2 * adaptedDistance κ (z i) (w j)
  have hF (i j : Fin N) : Integrable (F i j) c.measure :=
    (integrable_weight_product hN z w c i j).mul_const _
  have hrow (i : Fin N) :
      (∑ j, labelMass hN z w c i j * adaptedDistance κ (z i) (w j)) =
        ∫ p, ∑ j, F i j p ∂c.measure := by
    simp only [labelMass, ← integral_mul_const]
    exact (integral_finset_sum _ (fun j _ => hF i j)).symm
  simp_rw [hrow]
  rw [← integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hF i j))]
  apply integral_congr_ae
  filter_upwards [ae_first_mem_range hN z w c, ae_second_mem_range hN z w c] with p hp₁ hp₂
  have hterm (i j : Fin N) : F i j p =
      indexWeight z i p.1 * indexWeight w j p.2 * adaptedDistance κ p.1 p.2 := by
    by_cases hx : p.1 = z i <;> by_cases hy : p.2 = w j <;> simp [F, indexWeight, hx, hy]
  simp_rw [hterm]
  calc
    (∑ i, ∑ j, indexWeight z i p.1 * indexWeight w j p.2 * adaptedDistance κ p.1 p.2) =
        (∑ i, indexWeight z i p.1) * (∑ j, indexWeight w j p.2) *
          adaptedDistance κ p.1 p.2 := by
            simp only [Finset.sum_mul, Finset.mul_sum]
            exact Finset.sum_comm
    _ = _ := by rw [sum_indexWeight z p.1 hp₁, sum_indexWeight w p.2 hp₂]; ring

end CouplingMatrix

/-- A linear cost on a doubly stochastic matrix is at least the smallest
permutation cost. This is the exact consequence of Birkhoff's theorem used here. -/
theorem permutation_min_le_matrix {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : M ∈ doublyStochastic ℝ n) (d : n → n → ℝ)
    (e : Equiv.Perm n) (hmin : ∀ σ : Equiv.Perm n, (∑ i, d i (e i)) ≤ ∑ i, d i (σ i)) :
    (∑ i, d i (e i)) ≤ ∑ i, ∑ j, M i j * d i j := by
  obtain ⟨a, ha, hsum, hmatrix⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  have hcost : (∑ i, ∑ j, M i j * d i j) =
      ∑ σ : Equiv.Perm n, a σ * ∑ i, d i (σ i) := by
    rw [← hmatrix]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
    calc
      (∑ i, ∑ j, ∑ σ : Equiv.Perm n, a σ * σ.permMatrix ℝ i j * d i j) =
          ∑ i, ∑ σ : Equiv.Perm n, ∑ j, a σ * σ.permMatrix ℝ i j * d i j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ σ : Equiv.Perm n, ∑ i, ∑ j, a σ * σ.permMatrix ℝ i j * d i j :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro σ _
        simp only [mul_assoc, ← Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  rw [hcost]
  calc
    (∑ i, d i (e i)) = ∑ σ : Equiv.Perm n, a σ * ∑ i, d i (e i) := by
      rw [← Finset.sum_mul, hsum, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hmin σ) (ha σ)

/-- The arithmetic mean cost of a permutation matching. -/
def matchingCost (z w : Fin N → State D) (e : Equiv.Perm (Fin N)) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, adaptedDistance κ (z i) (w (e i))

/-- Equal-weight empirical transport has an optimal permutation matching,
including configurations with repeated states. -/
theorem exists_optimal_permutation (hN : 0 < N) (z w : Fin N → State D) :
    ∃ e : Equiv.Perm (Fin N),
      wasserstein (empiricalLaw κ hN z) (empiricalLaw κ hN w) = matchingCost (κ := κ) z w e ∧
      ∀ σ, matchingCost (κ := κ) z w e ≤ matchingCost (κ := κ) z w σ := by
  obtain ⟨e, _, he⟩ := Finset.exists_min_image Finset.univ
    (fun σ : Equiv.Perm (Fin N) => ∑ i, adaptedDistance κ (z i) (w (σ i))) Finset.univ_nonempty
  have hmin : ∀ σ : Equiv.Perm (Fin N),
      (∑ i, adaptedDistance κ (z i) (w (e i))) ≤ ∑ i, adaptedDistance κ (z i) (w (σ i)) :=
    fun σ => he σ (Finset.mem_univ σ)
  refine ⟨e, ?_, ?_⟩
  · apply le_antisymm (wasserstein_empiricalLaw_le_permuted κ hN z w e)
    apply le_csInf (Set.range_nonempty _)
    rintro r ⟨c, rfl⟩
    have h := permutation_min_le_matrix
      (fun i j => (N : ℝ) * labelMass hN z w c i j)
      (labelMass_doublyStochastic hN z w c)
      (fun i j => adaptedDistance κ (z i) (w j)) e hmin
    simp only [mul_assoc, ← Finset.mul_sum] at h
    rw [labelMass_cost hN z w c] at h
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    have hscaled := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Nat.cast_nonneg N))
    simpa only [matchingCost, ← mul_assoc, inv_mul_cancel₀ hNr, one_mul] using hscaled
  · intro σ
    exact mul_le_mul_of_nonneg_left (hmin σ) (inv_nonneg.mpr (Nat.cast_nonneg N))

/-- The transport infimum is exactly the attained minimum over finitely many matchings. -/
theorem wasserstein_eq_minimum_matching (hN : 0 < N) (z w : Fin N → State D) :
    wasserstein (empiricalLaw κ hN z) (empiricalLaw κ hN w) =
      sInf (Set.range (matchingCost (κ := κ) z w)) := by
  obtain ⟨e, he, hmin⟩ := exists_optimal_permutation hN z w
  rw [he]
  apply le_antisymm
  · exact le_csInf (Set.range_nonempty _) (by rintro r ⟨σ, rfl⟩; exact hmin σ)
  · apply csInf_le _ (Set.mem_range_self e)
    refine ⟨matchingCost (κ := κ) z w e, ?_⟩
    rintro r ⟨σ, rfl⟩
    exact hmin σ

/-- A fixed choice of optimal index permutation for every pair of configurations. -/
def optimalPermutation (hN : 0 < N) (z w : Fin N → State D) : Equiv.Perm (Fin N) :=
  Classical.choose (exists_optimal_permutation (κ := κ) hN z w)

/-- Relabel the second configuration by the chosen optimal permutation. -/
def optimalMatching (hN : 0 < N) (z w : Fin N → State D) : Fin N → State D :=
  w ∘ optimalPermutation (κ := κ) hN z w

/-- Matching changes labels, so its empirical law is exactly preserved. -/
theorem empiricalLaw_optimalMatching (hN : 0 < N) (z w : Fin N → State D) :
    empiricalLaw κ hN (optimalMatching (κ := κ) hN z w) = empiricalLaw κ hN w :=
  empiricalLaw_relabel κ hN w (optimalPermutation (κ := κ) hN z w)

/-- The chosen relabeling realizes the exact empirical transport distance. -/
theorem optimalMatching_cost (hN : 0 < N) (z w : Fin N → State D) :
    (N : ℝ)⁻¹ * ∑ i, adaptedDistance κ (z i) (optimalMatching (κ := κ) hN z w i) =
      wasserstein (empiricalLaw κ hN z) (empiricalLaw κ hN w) :=
  (Classical.choose_spec (exists_optimal_permutation (κ := κ) hN z w)).1.symm

/-- The matched configuration is a measurable function of both input vectors.
This supplies the measurable optimal-pairing step for random initial vectors. -/
theorem measurable_optimalMatching (hN : 0 < N) :
    Measurable (fun p : (Fin N → State D) × (Fin N → State D) =>
      optimalMatching (κ := κ) hN p.1 p.2) :=
  measurable_of_countable _

end CarryingCapacity.EmpiricalMatching
