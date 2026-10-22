import CarryingCapacity.EmpiricalArrayError
import CarryingCapacity.ExchangeableMatching

/-!
# Exchangeable initialization with vanishing expected pairing cost

The original initialization assumptions supply convergence in measure and a
uniform bound on the expected empirical Lyapunov average. The two expected
transport errors are derived here, before constructing the jointly exchangeable
optimal pairing with the exact original and iid vector marginals.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

namespace CarryingCapacity.InitialCoupling
open ExchangeableMatching EmpiricalArrayError EmpiricalMeanError EmpiricalLLN

variable {Ω : Type*} [MeasurableSpace Ω] {D : ℕ} {κ : MomentScale}

/-- The full initial-coupling lemma under the manuscript's original
exchangeable initialization hypotheses. No convergence of expected errors is
assumed, and no per-coordinate Lyapunov bound is required. -/
theorem exists_initial_coupling
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : MomentLaw κ D) (Ψ : State D → ℝ)
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (hνΨ : Integrable Ψ ν.measure)
    (z : ∀ n, Ω → Fin (n + 1) → State D) (hm : ∀ n, Measurable (z n))
    (hex : ∀ n, ExchangeableLaw (Measure.map (z n) P))
    (hΨ : ∀ n, Integrable (fun ω => FiniteGenerator.empiricalMean Ψ (z n ω)) P)
    (C : ℝ)
    (hbound : ∀ n, (∫ ω, FiniteGenerator.empiricalMean Ψ (z n ω) ∂P) ≤ C)
    (hconv : TendstoInMeasure P
      (fun n ω => wasserstein (empiricalLaw κ (Nat.succ_pos n) (z n ω)) ν) atTop 0) :
    ∃ γ : ∀ n, Measure (Fin (n + 1) → State D × State D),
      (∀ n, IsProbabilityMeasure (γ n)) ∧
      (∀ n, ExchangeableLaw (γ n)) ∧
      (∀ n, (γ n).map (fun a i => (a i).1) = Measure.map (z n) P) ∧
      (∀ n, (γ n).map (fun a i => (a i).2) = Measure.pi (fun _ : Fin (n + 1) => ν.measure)) ∧
      (∀ n, Integrable (pairingCost κ) (γ n)) ∧
      (∀ n, ∀ᵐ a ∂γ n, pairingCost κ a = wasserstein
        (empiricalLaw κ (Nat.succ_pos n) (fun i => (a i).1))
        (empiricalLaw κ (Nat.succ_pos n) (fun i => (a i).2))) ∧
      Tendsto (fun n => ∫ a, pairingCost κ a ∂γ n) atTop (𝓝 0) := by
  have hC : 0 ≤ C := by
    apply le_trans ?_ (hbound 0)
    apply integral_nonneg
    intro ω
    unfold FiniteGenerator.empiricalMean
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro i _
    linarith [hdom (z 0 ω i), momentWeight_nonneg κ (z 0 ω i)]
  letI : IsProbabilityMeasure ν.measure := ν.probability
  let μv : ∀ n, Measure (Fin (n + 1) → State D) := fun n => Measure.map (z n) P
  let νv : ∀ n, Measure (Fin (n + 1) → State D) :=
    fun n => Measure.pi (fun _ : Fin (n + 1) => ν.measure)
  letI : ∀ n, IsProbabilityMeasure (μv n) := fun n => isProbabilityMeasure_map (hm n).aemeasurable
  letI : ∀ n, IsProbabilityMeasure (νv n) := fun n => Measure.pi.instIsProbabilityMeasure _
  let joint : ∀ n, Measure ((Fin (n + 1) → State D) × (Fin (n + 1) → State D)) :=
    fun n => (μv n).prod (νv n)
  letI : ∀ n, IsProbabilityMeasure (joint n) := fun n => inferInstanceAs
    (IsProbabilityMeasure ((μv n).prod (νv n)))
  let F : ∀ n, (Fin (n + 1) → State D) → ℝ :=
    fun n w => wasserstein (empiricalLaw κ (Nat.succ_pos n) w) ν
  have hmF (n : ℕ) : Measurable (fun ω => F n (z n ω)) :=
    (measurable_of_countable (F n)).comp (hm n)
  have hui := LyapunovTails.uniformIntegrable_empirical_transport P hdom hsuper
    (fun n => n + 1) Nat.succ_pos z ν (fun n => (hmF n).aestronglyMeasurable) hΨ C hC hbound
  have hiOriginal (n : ℕ) : Integrable (fun ω => F n (z n ω)) P :=
    memLp_one_iff_integrable.mp (hui.memLp n)
  have limOriginal : Tendsto (fun n => ∫ ω, F n (z n ω) ∂P) atTop (𝓝 0) :=
    LyapunovTails.integral_empirical_transport_tendsto_zero P hdom hsuper
      (fun n => n + 1) Nat.succ_pos z ν (fun n => (hmF n).aestronglyMeasurable)
      hΨ C hC hbound hconv
  have hiFirst (n : ℕ) : Integrable (F n) (μv n) :=
    (integrable_map_measure (measurable_of_countable (F n)).aestronglyMeasurable
      (hm n).aemeasurable).mpr (hiOriginal n)
  have eqFirst (n : ℕ) : (∫ w, F n w ∂μv n) = ∫ ω, F n (z n ω) ∂P :=
    integral_map_of_stronglyMeasurable (hm n) (measurable_of_countable (F n)).stronglyMeasurable
  have hiCanonical (n : ℕ) : Integrable
      (fun ω : ℕ → State D => F n (fun i => ω i.val)) (canonicalLaw ν) :=
    integrable_sampleError (canonicalLaw ν) ν (fun i ω => ω i)
      (fun i => measurable_pi_apply i) (canonical_coordinate_map ν) n
  have hiSecond (n : ℕ) : Integrable (F n) (νv n) := by
    have hh := (integrable_map_measure (measurable_of_countable (F n)).aestronglyMeasurable
      (measurable_pi_lambda _ (fun i : Fin (n + 1) => measurable_pi_apply i.val)).aemeasurable).mpr
      (hiCanonical n)
    rwa [canonical_vector_map] at hh
  have eqSecond (n : ℕ) : (∫ w, F n w ∂νv n) =
      ∫ ω : ℕ → State D, F n (fun i => ω i.val) ∂canonicalLaw ν := by
    rw [show νv n = Measure.map (fun (ω : ℕ → State D) (i : Fin (n + 1)) => ω i.val)
        (canonicalLaw ν) from (canonical_vector_map ν n).symm]
    exact integral_map_of_stronglyMeasurable
      (measurable_pi_lambda _ (fun i => measurable_pi_apply i.val))
      (measurable_of_countable (F n)).stronglyMeasurable
  have limCanonical : Tendsto
      (fun n => ∫ ω : ℕ → State D, F n (fun i => ω i.val) ∂canonicalLaw ν) atTop (𝓝 0) :=
    integral_sampleError_tendsto_zero (canonicalLaw ν) ν Ψ hdom hsuper hνΨ
      (fun i ω => ω i) (fun i => measurable_pi_apply i)
      (fun i j hij => (canonical_independent ν).indepFun hij) (canonical_coordinate_map ν)
  have hjFirst (n : ℕ) : (joint n).map Prod.fst = μv n := by
    change Measure.map Prod.fst ((μv n).prod (νv n)) = μv n
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hjSecond (n : ℕ) : (joint n).map Prod.snd = νv n := by
    change Measure.map Prod.snd ((μv n).prod (νv n)) = νv n
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hj₁ (n : ℕ) : Integrable (fun p => F n p.1) (joint n) := by
    have hh : Integrable (F n) ((joint n).map Prod.fst) := by rw [hjFirst]; exact hiFirst n
    exact hh.comp_measurable measurable_fst
  have hj₂ (n : ℕ) : Integrable (fun p => F n p.2) (joint n) := by
    have hh : Integrable (F n) ((joint n).map Prod.snd) := by rw [hjSecond]; exact hiSecond n
    exact hh.comp_measurable measurable_snd
  have eqj₁ (n : ℕ) : (∫ p, F n p.1 ∂joint n) = ∫ ω, F n (z n ω) ∂P := by
    rw [← integral_map_of_stronglyMeasurable measurable_fst
      (measurable_of_countable (F n)).stronglyMeasurable, hjFirst, eqFirst]
  have eqj₂ (n : ℕ) : (∫ p, F n p.2 ∂joint n) =
      ∫ ω : ℕ → State D, F n (fun i => ω i.val) ∂canonicalLaw ν := by
    rw [← integral_map_of_stronglyMeasurable measurable_snd
      (measurable_of_countable (F n)).stronglyMeasurable, hjSecond, eqSecond]
  let γ : ∀ n, Measure (Fin (n + 1) → State D × State D) :=
    fun n => matchingLaw κ (Nat.succ_pos n) (joint n)
  refine ⟨γ, fun n => inferInstanceAs (IsProbabilityMeasure (matchingLaw κ (Nat.succ_pos n) (joint n))),
    fun n => matchingLaw_exchangeable κ (Nat.succ_pos n) (joint n), ?_, ?_, ?_,
    fun n => matchingLaw_ae_optimal κ (Nat.succ_pos n) (joint n), ?_⟩
  · intro n
    exact (matchingLaw_product_marginals κ (Nat.succ_pos n) (μv n) (νv n)
      (hex n) (iid_exchangeable ν.measure)).1
  · intro n
    exact (matchingLaw_product_marginals κ (Nat.succ_pos n) (μv n) (νv n)
      (hex n) (iid_exchangeable ν.measure)).2
  · intro n
    apply (matchingLaw_cost_integrable_iff κ (Nat.succ_pos n) (joint n)).mpr
    apply ((hj₁ n).add (hj₂ n)).mono' (measurable_of_countable _).aestronglyMeasurable
    exact Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (wasserstein_nonneg _ _)]
      simpa only [F, Pi.add_apply, wasserstein_symm ν] using
        wasserstein_triangle (empiricalLaw κ (Nat.succ_pos n) p.1) ν
          (empiricalLaw κ (Nat.succ_pos n) p.2)
  · apply integral_matchingLaw_cost_tendsto_zero κ (fun n => n + 1) Nat.succ_pos joint ν hj₁ hj₂
    · change Tendsto (fun n => ∫ p, F n p.1 ∂joint n) atTop (𝓝 0)
      simpa only [eqj₁] using limOriginal
    · change Tendsto (fun n => ∫ p, F n p.2 ∂joint n) atTop (𝓝 0)
      simpa only [eqj₂] using limCanonical

end CarryingCapacity.InitialCoupling
