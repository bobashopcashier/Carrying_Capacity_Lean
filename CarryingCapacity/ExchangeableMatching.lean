import CarryingCapacity.EmpiricalMatching
import CarryingCapacity.Symmetrization
import CarryingCapacity.TransportMetric

/-!
# Exchangeable optimal initialization

Choose an optimal matching, then apply an independent uniform permutation to
both members of every matched pair. The resulting law has the prescribed
exchangeable vector marginals and is jointly exchangeable. Its pairing cost is
exactly the empirical transport distance, including repeated particle states.
-/

noncomputable section
open scoped BigOperators ENNReal Classical
open MeasureTheory

namespace CarryingCapacity.ExchangeableMatching

open Symmetrization EmpiricalMatching

variable {N D : ℕ}

/-- Invariance of the full vector law under every permutation of its labels. -/
def ExchangeableLaw {α : Type*} [MeasurableSpace α]
    (μ : Measure (Fin N → α)) : Prop :=
  ∀ e : Equiv.Perm (Fin N), μ.map (relabel e) = μ

private theorem map_bind_countable {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [Countable α] [MeasurableSingletonClass α]
    [Countable β] [MeasurableSingletonClass β]
    (μ : Measure α) (k : α → Measure β) (f : β → γ) :
    (μ.bind k).map f = μ.bind (fun x => (k x).map f) := by
  rw [← Measure.bind_dirac_eq_map _ (measurable_of_countable f),
    Measure.bind_bind (measurable_of_countable k).aemeasurable
      (measurable_of_countable _).aemeasurable]
  congr 1
  funext x
  exact Measure.bind_dirac_eq_map _ (measurable_of_countable f)

private theorem bind_map_countable {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [Countable α] [MeasurableSingletonClass α]
    [Countable β] [MeasurableSingletonClass β]
    (μ : Measure α) (f : α → β) (k : β → Measure γ) :
    (μ.map f).bind k = μ.bind (fun x => k (f x)) := by
  rw [← Measure.bind_dirac_eq_map _ (measurable_of_countable f),
    Measure.bind_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable k).aemeasurable]
  simp only [Measure.dirac_bind (measurable_of_countable k)]

/-- Applying a coordinatewise measurable map commutes with uniform relabeling. -/
theorem map_symmetrizedMeasure {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) (z : Fin N → α) :
    (symmetrizedMeasure z).map (fun w i => f (w i)) =
      symmetrizedMeasure (fun i => f (z i)) := by
  have hm : Measurable (fun w : Fin N → α => fun i => f (w i)) :=
    measurable_pi_lambda _ (fun i => hf.comp (measurable_pi_apply i))
  unfold symmetrizedMeasure
  rw [Measure.map_smul]
  congr 1
  rw [← Measure.mapₗ_apply_of_measurable hm, map_sum]
  simp only [Measure.mapₗ_apply_of_measurable hm, Measure.map_dirac hm]
  rfl

/-- Symmetrizing a random vector already having an exchangeable law preserves
that entire vector law, rather than only its coordinate marginals. -/
theorem bind_symmetrizedMeasure_eq {α : Type*} [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α]
    (μ : Measure (Fin N → α)) (hμ : ExchangeableLaw μ) :
    μ.bind symmetrizedMeasure = μ := by
  ext s hs
  rw [Measure.bind_apply hs (measurable_of_countable _).aemeasurable]
  simp only [symmetrizedMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.finset_sum_apply]
  rw [lintegral_const_mul _ (measurable_of_countable _),
    lintegral_finset_sum _ (fun _ _ => measurable_of_countable _)]
  have hi (e : Equiv.Perm (Fin N)) :
      (∫⁻ z, Measure.dirac (relabel e z) s ∂μ) = μ s := by
    rw [← Measure.bind_apply hs (measurable_of_countable _).aemeasurable,
      Measure.bind_dirac_eq_map _ (measurable_relabel e), hμ e]
  simp only [hi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (Equiv.Perm (Fin N)) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin N)) ≠ 0)
  rw [← mul_assoc, ENNReal.inv_mul_cancel hc (by simp), one_mul]

/-- The vector of optimally matched pairs, before the additional random relabeling. -/
def matchedArray (κ : MomentScale) (hN : 0 < N)
    (p : (Fin N → State D) × (Fin N → State D)) : Fin N → State D × State D :=
  fun i => (p.1 i, optimalMatching (κ := κ) hN p.1 p.2 i)

/-- Conditional on both input vectors, uniformly relabel their optimal pairs. -/
def matchingLaw (κ : MomentScale) (hN : 0 < N)
    (joint : Measure ((Fin N → State D) × (Fin N → State D))) :
    Measure (Fin N → State D × State D) :=
  joint.bind (fun p => symmetrizedMeasure (matchedArray κ hN p))

instance matchingLaw_probability (κ : MomentScale) (hN : 0 < N)
    (joint : Measure ((Fin N → State D) × (Fin N → State D))) [IsProbabilityMeasure joint] :
    IsProbabilityMeasure (matchingLaw κ hN joint) := by
  constructor
  rw [matchingLaw, Measure.bind_apply MeasurableSet.univ
    (measurable_of_countable _).aemeasurable]
  simp

/-- The paired array is exchangeable even if the input joint law is not. -/
theorem matchingLaw_exchangeable (κ : MomentScale) (hN : 0 < N)
    (joint : Measure ((Fin N → State D) × (Fin N → State D))) :
    ExchangeableLaw (matchingLaw κ hN joint) := by
  intro e
  rw [matchingLaw, map_bind_countable]
  simp only [map_relabel_symmetrizedMeasure]

/-- The first entire vector law is preserved when that input marginal is exchangeable. -/
theorem matchingLaw_first (κ : MomentScale) (hN : 0 < N)
    (joint : Measure ((Fin N → State D) × (Fin N → State D)))
    (hjoint : ExchangeableLaw (joint.map Prod.fst)) :
    (matchingLaw κ hN joint).map (fun a i => (a i).1) = joint.map Prod.fst := by
  rw [matchingLaw, map_bind_countable]
  simp only [map_symmetrizedMeasure Prod.fst measurable_fst, matchedArray]
  rw [← bind_map_countable joint Prod.fst symmetrizedMeasure]
  exact bind_symmetrizedMeasure_eq _ hjoint

/-- Optimal matching alone can alter the second vector law. The independent
uniform common relabeling restores its prescribed exchangeable law. -/
theorem matchingLaw_second (κ : MomentScale) (hN : 0 < N)
    (joint : Measure ((Fin N → State D) × (Fin N → State D)))
    (hjoint : ExchangeableLaw (joint.map Prod.snd)) :
    (matchingLaw κ hN joint).map (fun a i => (a i).2) = joint.map Prod.snd := by
  rw [matchingLaw, map_bind_countable]
  simp only [map_symmetrizedMeasure Prod.snd measurable_snd, matchedArray]
  have hr (p : (Fin N → State D) × (Fin N → State D)) :
      symmetrizedMeasure (optimalMatching (κ := κ) hN p.1 p.2) =
        symmetrizedMeasure p.2 :=
    symmetrizedMeasure_relabel (optimalPermutation (κ := κ) hN p.1 p.2) p.2
  simp only [hr]
  rw [← bind_map_countable joint Prod.snd symmetrizedMeasure]
  exact bind_symmetrizedMeasure_eq _ hjoint



/-- Product laws of identically distributed coordinates are exchangeable. -/
theorem iid_exchangeable {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SigmaFinite ν] : ExchangeableLaw (Measure.pi (fun _ : Fin N => ν)) := by
  intro e
  have he : (relabel e : (Fin N → α) → (Fin N → α)) =
      MeasurableEquiv.piCongrLeft (fun _ : Fin N => α) e.symm := by
    ext z i
    simp [relabel, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [he]
  exact (measurePreserving_piCongrLeft (fun _ : Fin N => ν) e.symm).map_eq

/-- The construction applied to independent input vectors retains their full
laws. In particular its second vector can retain an iid product law. -/
theorem matchingLaw_product_marginals (κ : MomentScale) (hN : 0 < N)
    (μ ν : Measure (Fin N → State D)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ExchangeableLaw μ) (hν : ExchangeableLaw ν) :
    (matchingLaw κ hN (μ.prod ν)).map (fun a i => (a i).1) = μ ∧
    (matchingLaw κ hN (μ.prod ν)).map (fun a i => (a i).2) = ν := by
  constructor
  · simpa using matchingLaw_first κ hN (μ.prod ν) (by simpa using hμ)
  · simpa using matchingLaw_second κ hN (μ.prod ν) (by simpa using hν)

/-- The average adapted distance between members of the paired array. -/
def pairingCost (κ : MomentScale) (a : Fin N → State D × State D) : ℝ :=
  FiniteGenerator.empiricalMean (fun p => adaptedDistance κ p.1 p.2) a

theorem pairingCost_relabel (κ : MomentScale) (e : Equiv.Perm (Fin N))
    (a : Fin N → State D × State D) :
    pairingCost κ (relabel e a) = pairingCost κ a :=
  empiricalMean_relabel e _ a

theorem pairingCost_matchedArray (κ : MomentScale) (hN : 0 < N)
    (p : (Fin N → State D) × (Fin N → State D)) :
    pairingCost κ (matchedArray κ hN p) =
      wasserstein (empiricalLaw κ hN p.1) (empiricalLaw κ hN p.2) :=
  optimalMatching_cost hN p.1 p.2

/-- Every relabeling of the matched array has exactly the optimal cost between
its own two empirical marginal laws. -/
theorem relabeled_pairingCost_eq_transport (κ : MomentScale) (hN : 0 < N)
    (p : (Fin N → State D) × (Fin N → State D)) (e : Equiv.Perm (Fin N)) :
    pairingCost κ (relabel e (matchedArray κ hN p)) =
      wasserstein
        (empiricalLaw κ hN (fun i => (relabel e (matchedArray κ hN p) i).1))
        (empiricalLaw κ hN (fun i => (relabel e (matchedArray κ hN p) i).2)) := by
  rw [pairingCost_relabel, pairingCost_matchedArray]
  change wasserstein (empiricalLaw κ hN p.1) (empiricalLaw κ hN p.2) =
    wasserstein (empiricalLaw κ hN (p.1 ∘ e))
      (empiricalLaw κ hN (optimalMatching (κ := κ) hN p.1 p.2 ∘ e))
  rw [empiricalLaw_relabel, empiricalLaw_relabel, empiricalLaw_optimalMatching]

private theorem map_symmetrizedMeasure_invariant {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α]
    (F : (Fin N → α) → β) (hF : ∀ e z, F (relabel e z) = F z)
    (z : Fin N → α) : (symmetrizedMeasure z).map F = Measure.dirac (F z) := by
  ext s hs
  rw [Measure.map_apply (measurable_of_countable F) hs]
  simp only [symmetrizedMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.finset_sum_apply, Measure.dirac_apply' _ ((measurable_of_countable F) hs),
    Set.indicator_apply, Pi.one_apply, Set.mem_preimage, hF, Measure.dirac_apply' _ hs,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (Equiv.Perm (Fin N)) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin N)) ≠ 0)
  rw [← mul_assoc, ENNReal.inv_mul_cancel hc (by simp), one_mul]

/-- The cost has precisely the distribution of the empirical transport distance
between the input vectors, not just a bound on its expectation. -/
theorem matchingLaw_cost_distribution (κ : MomentScale) (hN : 0 < N)
    (joint : Measure ((Fin N → State D) × (Fin N → State D))) :
    (matchingLaw κ hN joint).map (pairingCost κ) =
      joint.map (fun p => wasserstein (empiricalLaw κ hN p.1) (empiricalLaw κ hN p.2)) := by
  rw [matchingLaw, map_bind_countable]
  simp only [map_symmetrizedMeasure_invariant (pairingCost κ) (pairingCost_relabel κ),
    pairingCost_matchedArray]
  exact Measure.bind_dirac_eq_map _ (measurable_of_countable _)

/-- Integrability of the transport error is exactly integrability of the
constructed coupling's pairing error. -/
theorem matchingLaw_cost_integrable_iff (κ : MomentScale) (hN : 0 < N)
    (joint : Measure ((Fin N → State D) × (Fin N → State D))) :
    Integrable (pairingCost κ) (matchingLaw κ hN joint) ↔
      Integrable (fun p => wasserstein (empiricalLaw κ hN p.1) (empiricalLaw κ hN p.2)) joint := by
  have h₁ := integrable_map_measure (μ := matchingLaw κ hN joint)
    (f := pairingCost κ) (g := fun r : ℝ => r)
    measurable_id.aestronglyMeasurable (measurable_of_countable _).aemeasurable
  have h₂ := integrable_map_measure (μ := joint)
    (f := fun p => wasserstein (empiricalLaw κ hN p.1) (empiricalLaw κ hN p.2))
    (g := fun r : ℝ => r) measurable_id.aestronglyMeasurable
    (measurable_of_countable _).aemeasurable
  rw [matchingLaw_cost_distribution] at h₁
  exact h₁.symm.trans h₂

/-- The expectation equality used in the initial-coupling lemma. The preceding
integrability equivalence records when these are finite genuine expectations. -/
theorem integral_matchingLaw_cost (κ : MomentScale) (hN : 0 < N)
    (joint : Measure ((Fin N → State D) × (Fin N → State D))) :
    (∫ a, pairingCost κ a ∂matchingLaw κ hN joint) =
      ∫ p, wasserstein (empiricalLaw κ hN p.1) (empiricalLaw κ hN p.2) ∂joint := by
  have hi := congrArg (fun m : Measure ℝ => ∫ r, r ∂m)
    (matchingLaw_cost_distribution κ hN joint)
  dsimp only at hi
  have e₁ : (∫ r : ℝ, r ∂(matchingLaw κ hN joint).map (pairingCost κ)) =
      ∫ a, pairingCost κ a ∂matchingLaw κ hN joint :=
    integral_map_of_stronglyMeasurable (f := fun r : ℝ => r)
      (measurable_of_countable _) stronglyMeasurable_id
  have e₂ : (∫ r : ℝ, r ∂joint.map
      (fun p => wasserstein (empiricalLaw κ hN p.1) (empiricalLaw κ hN p.2))) =
      ∫ p, wasserstein (empiricalLaw κ hN p.1) (empiricalLaw κ hN p.2) ∂joint :=
    integral_map_of_stronglyMeasurable (f := fun r : ℝ => r)
      (measurable_of_countable _) stronglyMeasurable_id
  rw [e₁, e₂] at hi
  exact hi


/-- The expected coupling error is bounded by the two expected empirical
errors against any common deterministic reference law. -/
theorem integral_matchingLaw_cost_le (κ : MomentScale) (hN : 0 < N)
    (joint : Measure ((Fin N → State D) × (Fin N → State D)))
    (ν : MomentLaw κ D)
    (h₁ : Integrable (fun p => wasserstein (empiricalLaw κ hN p.1) ν) joint)
    (h₂ : Integrable (fun p => wasserstein (empiricalLaw κ hN p.2) ν) joint) :
    (∫ a, pairingCost κ a ∂matchingLaw κ hN joint) ≤
      (∫ p, wasserstein (empiricalLaw κ hN p.1) ν ∂joint) +
      ∫ p, wasserstein (empiricalLaw κ hN p.2) ν ∂joint := by
  have hb (p : (Fin N → State D) × (Fin N → State D)) :
      wasserstein (empiricalLaw κ hN p.1) (empiricalLaw κ hN p.2) ≤
        wasserstein (empiricalLaw κ hN p.1) ν + wasserstein (empiricalLaw κ hN p.2) ν := by
    simpa only [wasserstein_symm ν] using
      wasserstein_triangle (empiricalLaw κ hN p.1) ν (empiricalLaw κ hN p.2)
  have hi : Integrable
      (fun p => wasserstein (empiricalLaw κ hN p.1) (empiricalLaw κ hN p.2)) joint := by
    apply (h₁.add h₂).mono' (measurable_of_countable _).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (wasserstein_nonneg _ _)] using hb p
  rw [integral_matchingLaw_cost, ← integral_add h₁ h₂]
  exact integral_mono hi (h₁.add h₂) hb

/-- Once the two empirical errors vanish in expectation, the constructed
exchangeable optimal pairing has vanishing expected error. Population sizes
may vary, and no uniform convergence rate is required. -/
theorem integral_matchingLaw_cost_tendsto_zero (κ : MomentScale)
    (size : ℕ → ℕ) (hsize : ∀ n, 0 < size n)
    (joint : ∀ n, Measure ((Fin (size n) → State D) × (Fin (size n) → State D)))
    (ν : MomentLaw κ D)
    (h₁ : ∀ n, Integrable (fun p => wasserstein (empiricalLaw κ (hsize n) p.1) ν) (joint n))
    (h₂ : ∀ n, Integrable (fun p => wasserstein (empiricalLaw κ (hsize n) p.2) ν) (joint n))
    (lim₁ : Filter.Tendsto
      (fun n => ∫ p, wasserstein (empiricalLaw κ (hsize n) p.1) ν ∂joint n)
      Filter.atTop (nhds 0))
    (lim₂ : Filter.Tendsto
      (fun n => ∫ p, wasserstein (empiricalLaw κ (hsize n) p.2) ν ∂joint n)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ a, pairingCost κ a ∂matchingLaw κ (hsize n) (joint n))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    rw [integral_matchingLaw_cost]
    exact integral_nonneg fun p => wasserstein_nonneg _ _
  · intro n
    exact integral_matchingLaw_cost_le κ (hsize n) (joint n) ν (h₁ n) (h₂ n)
  · simpa only [add_zero] using lim₁.add lim₂

section IndependentPermutation

/-- Permutations are given their discrete sigma algebra. -/
local instance permutationMeasurableSpace : MeasurableSpace (Equiv.Perm (Fin N)) := ⊤
local instance permutationMeasurableSingletonClass :
    MeasurableSingletonClass (Equiv.Perm (Fin N)) := ⟨fun _ => trivial⟩

/-- Uniform law on the finite group of label permutations. -/
def uniformPermutation : Measure (Equiv.Perm (Fin N)) :=
  (Fintype.card (Equiv.Perm (Fin N)) : ℝ≥0∞)⁻¹ •
    ∑ e : Equiv.Perm (Fin N), Measure.dirac e

instance uniformPermutation_probability : IsProbabilityMeasure (uniformPermutation (N := N)) := by
  constructor
  have hc : (Fintype.card (Equiv.Perm (Fin N)) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin N)) ≠ 0)
  simp [uniformPermutation, Measure.finset_sum_apply,
    ENNReal.inv_mul_cancel hc (by simp)]

theorem map_uniformPermutation {α : Type*} [MeasurableSpace α] (z : Fin N → α) :
    (uniformPermutation (N := N)).map (fun e => relabel e z) = symmetrizedMeasure z := by
  unfold uniformPermutation symmetrizedMeasure
  rw [Measure.map_smul]
  congr 1
  rw [← Measure.mapₗ_apply_of_measurable (measurable_of_countable _), map_sum]
  simp only [Measure.mapₗ_apply_of_measurable (measurable_of_countable _),
    Measure.map_dirac (measurable_of_countable _)]

/-- Concrete realization: take the product with an independent uniform
permutation, and apply that same permutation to both members of each pair. -/
def sampledArray (κ : MomentScale) (hN : 0 < N)
    (s : ((Fin N → State D) × (Fin N → State D)) × Equiv.Perm (Fin N)) :
    Fin N → State D × State D := relabel s.2 (matchedArray κ hN s.1)

/-- The conditional-mixture definition is exactly the law of the construction
on the independent product probability space. -/
theorem independent_uniform_realization (κ : MomentScale) (hN : 0 < N)
    (joint : Measure ((Fin N → State D) × (Fin N → State D))) :
    (joint.prod uniformPermutation).map (sampledArray κ hN) = matchingLaw κ hN joint := by
  rw [Measure.prod, map_bind_countable]
  simp only [Measure.map_map (measurable_of_countable _) measurable_prodMk_left]
  change joint.bind (fun p => uniformPermutation.map
      (fun e => relabel e (matchedArray κ hN p))) = _
  simp only [map_uniformPermutation]
  rfl

/-- On the explicit product space, every sample has the exact optimal error. -/
theorem sampledArray_cost (κ : MomentScale) (hN : 0 < N)
    (s : ((Fin N → State D) × (Fin N → State D)) × Equiv.Perm (Fin N)) :
    pairingCost κ (sampledArray κ hN s) =
      wasserstein (empiricalLaw κ hN s.1.1) (empiricalLaw κ hN s.1.2) := by
  rw [sampledArray, pairingCost_relabel, pairingCost_matchedArray]


/-- Under the constructed law, almost every paired array realizes the optimal
transport between its own empirical marginals. -/
theorem matchingLaw_ae_optimal (κ : MomentScale) (hN : 0 < N)
    (joint : Measure ((Fin N → State D) × (Fin N → State D))) :
    ∀ᵐ a ∂matchingLaw κ hN joint,
      pairingCost κ a = wasserstein
        (empiricalLaw κ hN (fun i => (a i).1))
        (empiricalLaw κ hN (fun i => (a i).2)) := by
  rw [← independent_uniform_realization]
  apply (ae_map_iff (measurable_of_countable _).aemeasurable
    ((Set.to_countable _).measurableSet)).mpr
  exact Filter.Eventually.of_forall fun s =>
    relabeled_pairingCost_eq_transport κ hN s.1 s.2

end IndependentPermutation


/-- Finite-population initialization coupling with an iid comparison vector:
the whole interacting vector law and the whole iid law are retained, the paired
array is exchangeable, and its empirical matching cost is optimal almost surely.
The expectation identity and convergence upgrade are proved above. -/
theorem exists_exchangeable_optimal_iid_coupling (κ : MomentScale) (hN : 0 < N)
    (μ : Measure (Fin N → State D)) [IsProbabilityMeasure μ]
    (hμ : ExchangeableLaw μ) (ν : Measure (State D)) [IsProbabilityMeasure ν] :
    ∃ γ : Measure (Fin N → State D × State D),
      IsProbabilityMeasure γ ∧ ExchangeableLaw γ ∧
      γ.map (fun a i => (a i).1) = μ ∧
      γ.map (fun a i => (a i).2) = Measure.pi (fun _ : Fin N => ν) ∧
      (∀ᵐ a ∂γ, pairingCost κ a = wasserstein
        (empiricalLaw κ hN (fun i => (a i).1))
        (empiricalLaw κ hN (fun i => (a i).2))) := by
  letI : IsProbabilityMeasure (Measure.pi (fun _ : Fin N => ν)) :=
    Measure.pi.instIsProbabilityMeasure _
  let joint := μ.prod (Measure.pi (fun _ : Fin N => ν))
  letI : IsProbabilityMeasure joint := inferInstanceAs
    (IsProbabilityMeasure (μ.prod (Measure.pi (fun _ : Fin N => ν))))
  refine ⟨matchingLaw κ hN joint, inferInstance, matchingLaw_exchangeable κ hN joint, ?_, ?_,
    matchingLaw_ae_optimal κ hN joint⟩
  · exact (matchingLaw_product_marginals κ hN μ _ hμ (iid_exchangeable ν)).1
  · exact (matchingLaw_product_marginals κ hN μ _ hμ (iid_exchangeable ν)).2

end CarryingCapacity.ExchangeableMatching
