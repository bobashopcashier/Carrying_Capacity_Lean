import CarryingCapacity.EmpiricalMeasure

/-!
# Permutation symmetry of the finite system

The finite-system generator commutes with relabelling whenever its environment
map is permutation invariant. Averaging this identity over all permutations
proves the symmetrization identity used by the original paper. These are exact
identities for arbitrary real test functions; exchangeability of a stochastic
process additionally requires its construction and uniqueness in law.
-/

noncomputable section
open scoped BigOperators ENNReal Classical

namespace CarryingCapacity.Symmetrization

open FiniteGenerator
open MeasureTheory

variable {α H Law : Type*} [Fintype H] {N : ℕ}

def relabel (e : Equiv.Perm (Fin N)) (z : Fin N → α) : Fin N → α := z ∘ e

@[simp] theorem relabel_apply (e : Equiv.Perm (Fin N)) (z : Fin N → α) (i : Fin N) :
    relabel e z i = z (e i) := rfl

@[simp] theorem relabel_refl (z : Fin N → α) : relabel (Equiv.refl _) z = z := rfl

theorem relabel_trans (e f : Equiv.Perm (Fin N)) (z : Fin N → α) :
    relabel e (relabel f z) = relabel (e.trans f) z := rfl

theorem relabel_update (e : Equiv.Perm (Fin N)) (z : Fin N → α) (i : Fin N) (y : α) :
    relabel e (Function.update z i y) = Function.update (relabel e z) (e.symm i) y :=
  Function.update_comp_equiv z e i y

theorem empiricalMean_relabel (e : Equiv.Perm (Fin N)) (f : α → ℝ) (z : Fin N → α) :
    empiricalMean f (relabel e z) = empiricalMean f z := by
  unfold empiricalMean
  congr 1
  exact Equiv.sum_comp e (fun i => f (z i))

/-- The original finite generator is equivariant under every lineage permutation. -/
theorem generator_relabel (transition : H → α → α) (rate : H → α → Law → ℝ)
    (empirical : (Fin N → α) → Law)
    (hinvariant : ∀ e z, empirical (relabel e z) = empirical z)
    (e : Equiv.Perm (Fin N)) (F : (Fin N → α) → ℝ) (z : Fin N → α) :
    systemGenerator transition rate empirical F (relabel e z) =
      systemGenerator transition rate empirical (fun w => F (relabel e w)) z := by
  unfold systemGenerator
  rw [hinvariant e z]
  calc
    (∑ i, ∑ h, rate h (relabel e z i) (empirical z) *
        (F (Function.update (relabel e z) i (transition h (relabel e z i))) -
         F (relabel e z))) =
      ∑ i, ∑ h, rate h (z (e i)) (empirical z) *
        (F (relabel e (Function.update z (e i) (transition h (z (e i))))) -
         F (relabel e z)) := by
      simp only [relabel_apply, relabel_update, Equiv.symm_apply_apply]
    _ = _ := Equiv.sum_comp e (fun i => ∑ h, rate h (z i) (empirical z) *
      (F (relabel e (Function.update z i (transition h (z i)))) - F (relabel e z)))

theorem generator_smul (transition : H → α → α) (rate : H → α → Law → ℝ)
    (empirical : (Fin N → α) → Law) (c : ℝ) (F : (Fin N → α) → ℝ)
    (z : Fin N → α) :
    systemGenerator transition rate empirical (fun w => c * F w) z =
      c * systemGenerator transition rate empirical F z := by
  unfold systemGenerator
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro h _
  ring

theorem generator_sum {I : Type*} [Fintype I]
    (transition : H → α → α) (rate : H → α → Law → ℝ)
    (empirical : (Fin N → α) → Law) (F : I → (Fin N → α) → ℝ)
    (z : Fin N → α) :
    systemGenerator transition rate empirical (fun w => ∑ j, F j w) z =
      ∑ j, systemGenerator transition rate empirical (F j) z := by
  unfold systemGenerator
  simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
  calc
    (∑ i, ∑ h, ∑ j, rate h (z i) (empirical z) *
      (F j (Function.update z i (transition h (z i))) - F j z)) =
      ∑ i, ∑ j, ∑ h, rate h (z i) (empirical z) *
      (F j (Function.update z i (transition h (z i))) - F j z) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Uniform averaging over labelled permutations, including multiplicities
when a configuration contains repeated lineage states. -/
def symmetrize (F : (Fin N → α) → ℝ) (z : Fin N → α) : ℝ :=
  (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ * ∑ e : Equiv.Perm (Fin N), F (relabel e z)

theorem symmetrize_relabel (F : (Fin N → α) → ℝ) (e : Equiv.Perm (Fin N))
    (z : Fin N → α) : symmetrize F (relabel e z) = symmetrize F z := by
  unfold symmetrize
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft e) (fun σ => F (relabel σ z))

theorem symmetrize_of_invariant (F : (Fin N → α) → ℝ)
    (hF : ∀ e z, F (relabel e z) = F z) (z : Fin N → α) :
    symmetrize F z = F z := by
  unfold symmetrize
  simp only [hF, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (Equiv.Perm (Fin N)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin N)) ≠ 0)
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem symmetrize_idempotent (F : (Fin N → α) → ℝ) (z : Fin N → α) :
    symmetrize (symmetrize F) z = symmetrize F z :=
  symmetrize_of_invariant _ (symmetrize_relabel F) z

/-- Averaging the generator over all lineage permutations commutes with
applying the generator to the averaged test function. This is the labelled
form of the original paper's symmetrization identity. -/
theorem generator_symmetrize (transition : H → α → α) (rate : H → α → Law → ℝ)
    (empirical : (Fin N → α) → Law)
    (hinvariant : ∀ e z, empirical (relabel e z) = empirical z)
    (F : (Fin N → α) → ℝ) (z : Fin N → α) :
    systemGenerator transition rate empirical (symmetrize F) z =
      symmetrize (systemGenerator transition rate empirical F) z := by
  unfold symmetrize
  rw [generator_smul, generator_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  exact (generator_relabel transition rate empirical hinvariant e F z).symm

/-- The symmetrization identity for the actual moment empirical law. It
requires no assumptions on the rates beyond their dependence on the empirical
law and the currently jumping lineage. -/
theorem empirical_generator_symmetrize {D : ℕ} (κ : MomentScale) (hN : 0 < N)
    (transition : H → State D → State D)
    (rate : H → State D → MomentLaw κ D → ℝ)
    (F : (Fin N → State D) → ℝ) (z : Fin N → State D) :
    systemGenerator transition rate (empiricalLaw κ hN) (symmetrize F) z =
      symmetrize (systemGenerator transition rate (empiricalLaw κ hN) F) z := by
  apply generator_symmetrize
  intro e w
  exact empiricalLaw_relabel κ hN w e

section Measures

variable [MeasurableSpace α]

/-- The genuine empirical probability measure used by the original theorem,
without imposing any moment condition on its possible limiting law. -/
def empiricalProbability (hN : 0 < N) (z : Fin N → α) : ProbabilityMeasure α :=
  ⟨empiricalMeasure z, empiricalMeasure_probability hN z⟩

@[simp] theorem empiricalProbability_relabel (hN : 0 < N) (e : Equiv.Perm (Fin N))
    (z : Fin N → α) : empiricalProbability hN (relabel e z) = empiricalProbability hN z := by
  apply Subtype.ext
  exact empiricalMeasure_relabel z e

theorem original_generator_symmetrize (hN : 0 < N)
    (transition : H → α → α) (rate : H → α → ProbabilityMeasure α → ℝ)
    (F : (Fin N → α) → ℝ) (z : Fin N → α) :
    systemGenerator transition rate (empiricalProbability hN) (symmetrize F) z =
      symmetrize (systemGenerator transition rate (empiricalProbability hN) F) z := by
  apply generator_symmetrize
  exact empiricalProbability_relabel hN

theorem measurable_relabel (e : Equiv.Perm (Fin N)) :
    Measurable (relabel e : (Fin N → α) → (Fin N → α)) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply (e i)

/-- Law of a uniformly random permutation of a fixed configuration. Repeated
states are counted with their permutation multiplicities. -/
def symmetrizedMeasure (z : Fin N → α) : Measure (Fin N → α) :=
  (Fintype.card (Equiv.Perm (Fin N)) : ℝ≥0∞)⁻¹ •
    ∑ e : Equiv.Perm (Fin N), Measure.dirac (relabel e z)

instance symmetrizedMeasure_probability (z : Fin N → α) :
    IsProbabilityMeasure (symmetrizedMeasure z) := by
  constructor
  have hc : (Fintype.card (Equiv.Perm (Fin N)) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin N)) ≠ 0)
  simp [symmetrizedMeasure, Measure.finset_sum_apply,
    ENNReal.inv_mul_cancel hc (by simp)]

variable [MeasurableSingletonClass α]

theorem integrable_symmetrizedMeasure (z : Fin N → α) (F : (Fin N → α) → ℝ) :
    Integrable F (symmetrizedMeasure z) := by
  apply Integrable.smul_measure
  · exact integrable_finset_sum_measure.mpr fun e _ => integrable_dirac
  · apply ENNReal.inv_ne_top.mpr
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin N)) ≠ 0)

/-- The probabilistic symmetrization kernel integrates test functions exactly
as the uniform permutation average used in the generator identity. -/
theorem integral_symmetrizedMeasure (z : Fin N → α) (F : (Fin N → α) → ℝ) :
    (∫ w, F w ∂symmetrizedMeasure z) = symmetrize F z := by
  rw [symmetrizedMeasure, integral_smul_measure,
    integral_finset_sum_measure (fun e _ => integrable_dirac)]
  simp [symmetrize, ENNReal.toReal_inv]

omit [MeasurableSingletonClass α] in
/-- The constructed initial law is exchangeable as an equality of measures. -/
theorem map_relabel_symmetrizedMeasure (e : Equiv.Perm (Fin N)) (z : Fin N → α) :
    Measure.map (relabel e) (symmetrizedMeasure z) = symmetrizedMeasure z := by
  unfold symmetrizedMeasure
  rw [Measure.map_smul]
  congr 1
  rw [← Measure.mapₗ_apply_of_measurable (measurable_relabel e), map_sum]
  simp only [Measure.mapₗ_apply_of_measurable (measurable_relabel e),
    Measure.map_dirac (measurable_relabel e)]
  exact Equiv.sum_comp (Equiv.mulRight e) (fun σ => Measure.dirac (relabel σ z))

omit [MeasurableSingletonClass α] in
/-- Choosing another permutation of the initial labels gives the same law. -/
theorem symmetrizedMeasure_relabel (e : Equiv.Perm (Fin N)) (z : Fin N → α) :
    symmetrizedMeasure (relabel e z) = symmetrizedMeasure z := by
  unfold symmetrizedMeasure
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft e) (fun σ => Measure.dirac (relabel σ z))

/-- The empirical integral of a singleton test is its exact normalized count. -/
theorem empirical_singleton_integral (z : Fin N → α) (x : α) :
    (∫ y, (if y = x then (1 : ℝ) else 0) ∂empiricalMeasure z) =
      (N : ℝ)⁻¹ * (Fintype.card {i : Fin N // z i = x} : ℝ) := by
  rw [integral_empiricalMeasure]
  simp [empiricalMean, Fintype.card_subtype]

/-- Equal empirical measures are exactly relabelings of the same finite
configuration. This includes repeated states, using equivalences of fibers. -/
theorem empiricalMeasure_eq_iff_relabel (hN : 0 < N) (z w : Fin N → α) :
    empiricalMeasure z = empiricalMeasure w ↔
      ∃ e : Equiv.Perm (Fin N), relabel e w = z := by
  constructor
  · intro h
    have hc (x : α) : Fintype.card {i : Fin N // z i = x} =
        Fintype.card {i : Fin N // w i = x} := by
      have hi := congrArg (fun μ : Measure α => ∫ y, (if y = x then (1 : ℝ) else 0) ∂μ) h
      dsimp only at hi
      rw [empirical_singleton_integral z x, empirical_singleton_integral w x] at hi
      have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
      exact_mod_cast mul_left_cancel₀ (inv_ne_zero hNreal) hi
    let ef : ∀ x : α, {i : Fin N // z i = x} ≃ {i : Fin N // w i = x} :=
      fun x => Fintype.equivOfCardEq (hc x)
    refine ⟨Equiv.ofFiberEquiv ef, ?_⟩
    funext i
    exact Equiv.ofFiberEquiv_map ef i
  · rintro ⟨e, he⟩
    rw [← he]
    exact empiricalMeasure_relabel w e

/-- Thus the symmetrized law depends only on the empirical measure, not on a
chosen labelled representative of its fiber. -/
theorem symmetrizedMeasure_eq_of_empirical_eq (hN : 0 < N) (z w : Fin N → α)
    (h : empiricalMeasure z = empiricalMeasure w) :
    symmetrizedMeasure z = symmetrizedMeasure w := by
  obtain ⟨e, he⟩ := (empiricalMeasure_eq_iff_relabel hN z w).mp h
  rw [← he]
  exact symmetrizedMeasure_relabel e w

/-- Under this law, the initial empirical measure is deterministic, exactly
as in the original paper's symmetrized initialization. -/
theorem ae_empirical_eq [Countable α] (z : Fin N → α) :
    ∀ᵐ w ∂symmetrizedMeasure z, empiricalMeasure w = empiricalMeasure z := by
  rw [ae_iff]
  have hs : MeasurableSet {w : Fin N → α | ¬empiricalMeasure w = empiricalMeasure z} :=
    Set.to_countable _ |>.measurableSet
  simp [symmetrizedMeasure, Measure.finset_sum_apply, hs, Measure.dirac_apply',
    relabel, empiricalMeasure_relabel]

end Measures

end CarryingCapacity.Symmetrization
