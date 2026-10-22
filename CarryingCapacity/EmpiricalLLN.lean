import CarryingCapacity.TransportCompleteness
import CarryingCapacity.EmpiricalMeasure
import CarryingCapacity.LyapunovTails

/-!
# Strong laws for empirical observables and finite-state approximation

The sample assumptions are genuine measurable, identically distributed,
pairwise independent random variables. Integrability is taken under the actual
common law. Scalar, moment, and event-frequency strong laws are derived from
mathlib's Etemadi strong law. The finite-state truncation bounds use genuine
transport plans and integrable moment tails.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

namespace CarryingCapacity.EmpiricalLLN
variable {Ω : Type*} [MeasurableSpace Ω] {D : ℕ} {κ : MomentScale}

/-- The first `n+1` samples, using positive sample sizes throughout. -/
def sampleConfig (X : ℕ → Ω → State D) (n : ℕ) (ω : Ω) : Fin (n + 1) → State D :=
  fun i => X i ω

def sampleLaw (κ : MomentScale) (X : ℕ → Ω → State D) (n : ℕ) (ω : Ω) : MomentLaw κ D :=
  empiricalLaw κ (Nat.succ_pos n) (sampleConfig X n ω)

omit [MeasurableSpace Ω] in
theorem integral_sampleLaw (X : ℕ → Ω → State D) (n : ℕ) (ω : Ω) (f : State D → ℝ) :
    (∫ x, f x ∂(sampleLaw κ X n ω).measure) =
      (∑ i ∈ Finset.range (n + 1), f (X i ω)) / (n + 1) := by
  rw [sampleLaw, integral_empiricalLaw]
  unfold FiniteGenerator.empiricalMean sampleConfig
  rw [Fin.sum_univ_eq_sum_range (fun i => f (X i ω))]
  simp [div_eq_mul_inv, mul_comm]

/-- The strong law for every integrable empirical observable, with independence
and the common law supplied as ordinary probabilistic hypotheses. -/
theorem observable_strongLaw (P : Measure Ω) (μ : MomentLaw κ D)
    (X : ℕ → Ω → State D) (hm : ∀ i, Measurable (X i))
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) P))
    (hlaw : ∀ i, Measure.map (X i) P = μ.measure)
    (f : State D → ℝ) (hf : Integrable f μ.measure) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∫ x, f x ∂(sampleLaw κ X n ω).measure)
      atTop (𝓝 (∫ x, f x ∂μ.measure)) := by
  have hident (i : ℕ) : IdentDistrib (X i) (X 0) P P :=
    ⟨(hm i).aemeasurable, (hm 0).aemeasurable, (hlaw i).trans (hlaw 0).symm⟩
  have hint : Integrable (fun ω => f (X 0 ω)) P := by
    have hh : Integrable f (Measure.map (X 0) P) := by rwa [hlaw 0]
    exact hh.comp_measurable (hm 0)
  have heq : (∫ ω, f (X 0 ω) ∂P) = ∫ x, f x ∂μ.measure := by
    rw [← integral_map_of_stronglyMeasurable (hm 0)
      (measurable_of_countable f).stronglyMeasurable, hlaw 0]
  have hs := strong_law_ae_real (fun i ω => f (X i ω)) hint
    (fun i j hij => (hind hij).comp (measurable_of_countable f) (measurable_of_countable f))
    (fun i => (hident i).comp (measurable_of_countable f))
  filter_upwards [hs] with ω hω
  have hh := hω.comp (tendsto_add_atTop_nat 1)
  simpa only [integral_sampleLaw, heq, Function.comp_def, Nat.cast_add, Nat.cast_one] using hh

/-- Finite κ-moment is exactly the integrability needed for empirical moments. -/
theorem moment_strongLaw (P : Measure Ω) (μ : MomentLaw κ D)
    (X : ℕ → Ω → State D) (hm : ∀ i, Measurable (X i))
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) P))
    (hlaw : ∀ i, Measure.map (X i) P = μ.measure) :
    ∀ᵐ ω ∂P, Tendsto (fun n => moment (sampleLaw κ X n ω)) atTop (𝓝 (moment μ)) :=
  observable_strongLaw P μ X hm hind hlaw (momentWeight κ) μ.integrable_weight

/-- All state frequencies converge simultaneously on a single probability-one set. -/
theorem singleton_strongLaw (P : Measure Ω) (μ : MomentLaw κ D)
    (X : ℕ → Ω → State D) (hm : ∀ i, Measurable (X i))
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) P))
    (hlaw : ∀ i, Measure.map (X i) P = μ.measure) :
    ∀ᵐ ω ∂P, ∀ z : State D,
      Tendsto (fun n => (sampleLaw κ X n ω).measure.real {z}) atTop (𝓝 (μ.measure.real {z})) := by
  letI : IsProbabilityMeasure μ.measure := μ.probability
  haveI : IsFiniteMeasure μ.measure := inferInstance
  rw [ae_all_iff]
  intro z
  have hh := observable_strongLaw P μ X hm hind hlaw (({z} : Set (State D)).indicator (fun _ => (1 : ℝ)))
    ((integrable_const (1 : ℝ)).indicator (measurableSet_singleton z))
  simpa only [integral_indicator_const (1 : ℝ) (measurableSet_singleton z), smul_eq_mul,
    mul_one] using hh

/-- Finite Lyapunov moment implies finite adapted moment by actual domination. -/
def lawOfLyapunov (μ : ProbabilityMeasure (State D)) (Ψ : State D → ℝ)
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x) (hΨ : Integrable Ψ (μ : Measure (State D))) :
    MomentLaw κ D where
  measure := μ
  probability := inferInstance
  integrable_weight := hΨ.mono' (measurable_of_countable _).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (momentWeight_nonneg κ x)]
      linarith [hdom x])

/-- Truncate to a finite adapted-moment sublevel, sending its complement to zero. -/
def truncate (κ : MomentScale) (K : ℕ) (x : State D) : State D :=
  if momentWeight κ x ≤ K then x else 0

def tailWeight (κ : MomentScale) (K : ℕ) (x : State D) : ℝ :=
  if momentWeight κ x ≤ K then 0 else momentWeight κ x

theorem tailWeight_nonneg (K : ℕ) (x : State D) : 0 ≤ tailWeight κ K x := by
  unfold tailWeight
  split_ifs
  · exact le_rfl
  · exact momentWeight_nonneg κ x

theorem tailWeight_le (K : ℕ) (x : State D) : tailWeight κ K x ≤ momentWeight κ x := by
  unfold tailWeight
  split_ifs
  · exact momentWeight_nonneg κ x
  · exact le_rfl

theorem distance_truncate (K : ℕ) (x : State D) :
    adaptedDistance κ x (truncate κ K x) = tailWeight κ K x := by
  unfold truncate tailWeight
  split_ifs <;> simp

theorem weight_truncate_le (K : ℕ) (x : State D) :
    momentWeight κ (truncate κ K x) ≤ momentWeight κ x := by
  unfold truncate
  split_ifs
  · exact le_rfl
  · simpa [momentWeight, κ.at_zero] using momentWeight_nonneg κ x

theorem finite_range_truncate (K : ℕ) : (Set.range (truncate κ K : State D → State D)).Finite := by
  apply ((finite_moment_sublevel (D := D) κ K).insert 0).subset
  rintro y ⟨x, rfl⟩
  by_cases hx : momentWeight κ x ≤ K
  · simp only [truncate, if_pos hx, Set.mem_insert_iff, Set.mem_setOf_eq]
    exact Or.inr hx
  · simp [truncate, hx]

theorem integrable_tailWeight (μ : MomentLaw κ D) (K : ℕ) : Integrable (tailWeight κ K) μ.measure :=
  μ.integrable_weight.mono' (measurable_of_countable _).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tailWeight_nonneg K x)]
      exact tailWeight_le K x)

/-- All fixed-cutoff empirical tails satisfy strong laws on one probability-one set. -/
theorem tail_strongLaw (P : Measure Ω) (μ : MomentLaw κ D)
    (X : ℕ → Ω → State D) (hm : ∀ i, Measurable (X i))
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) P))
    (hlaw : ∀ i, Measure.map (X i) P = μ.measure) :
    ∀ᵐ ω ∂P, ∀ K : ℕ, Tendsto
      (fun n => ∫ x, tailWeight κ K x ∂(sampleLaw κ X n ω).measure)
      atTop (𝓝 (∫ x, tailWeight κ K x ∂μ.measure)) := by
  rw [ae_all_iff]
  intro K
  exact observable_strongLaw P μ X hm hind hlaw _ (integrable_tailWeight μ K)

/-- The deterministic tail of each finite-moment law tends to zero. -/
theorem integral_tailWeight_tendsto_zero (μ : MomentLaw κ D) :
    Tendsto (fun K => ∫ x, tailWeight κ K x ∂μ.measure) atTop (𝓝 0) := by
  have hpoint (x : State D) : Tendsto (fun K => tailWeight κ K x) atTop (𝓝 (0 : ℝ)) := by
    have heq : (fun K => tailWeight κ K x) =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
      refine eventually_atTop.mpr ⟨Nat.ceil (momentWeight κ x), ?_⟩
      intro K hK
      have hh : momentWeight κ x ≤ (K : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hK)
      simp [tailWeight, hh]
    exact tendsto_const_nhds.congr' heq.symm
  have hh := tendsto_integral_of_dominated_convergence (momentWeight κ)
    (fun K => (measurable_of_countable (tailWeight κ K)).aestronglyMeasurable)
    μ.integrable_weight (fun K => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tailWeight_nonneg K x)]
      exact tailWeight_le K x) (Eventually.of_forall hpoint)
  simpa only [integral_zero] using hh

/-- The truncated law remains a genuine finite-moment probability measure. -/
def truncateLaw (μ : MomentLaw κ D) (K : ℕ) : MomentLaw κ D where
  measure := Measure.map (truncate κ K) μ.measure
  probability := by
    letI : IsProbabilityMeasure μ.measure := μ.probability
    exact isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  integrable_weight := by
    apply (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable).mpr
    apply μ.integrable_weight.mono' (measurable_of_countable _).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      change ‖momentWeight κ (truncate κ K x)‖ ≤ momentWeight κ x
      rw [Real.norm_eq_abs, abs_of_nonneg (momentWeight_nonneg κ _)]
      exact weight_truncate_le K x

/-- The truncated measure is concentrated on a deterministic finite range. -/
theorem truncateLaw_range_mass (μ : MomentLaw κ D) (K : ℕ) :
    (truncateLaw μ K).measure (Set.range (truncate κ K : State D → State D)) = 1 := by
  letI : IsProbabilityMeasure μ.measure := μ.probability
  change (Measure.map (truncate κ K) μ.measure) (Set.range (truncate κ K)) = 1
  rw [Measure.map_apply (measurable_of_countable _) (finite_range_truncate K).measurableSet]
  have he : (truncate κ K) ⁻¹' Set.range (truncate κ K : State D → State D) = Set.univ := by
    ext x
    simp
  rw [he, measure_univ]

/-- Pair each state with its finite-state truncation. -/
def truncationCoupling (μ : MomentLaw κ D) (K : ℕ) : Coupling μ (truncateLaw μ K) where
  measure := Measure.map (fun x => (x, truncate κ K x)) μ.measure
  first_marginal := by
    rw [Measure.map_map measurable_fst (measurable_of_countable _)]
    exact Measure.map_id
  second_marginal := by
    rw [Measure.map_map measurable_snd (measurable_of_countable _)]
    rfl

theorem truncationCoupling_cost (μ : MomentLaw κ D) (K : ℕ) :
    (truncationCoupling μ K).cost = ∫ x, tailWeight κ K x ∂μ.measure := by
  change (∫ p : State D × State D, adaptedDistance κ p.1 p.2
    ∂Measure.map (fun x => (x, truncate κ K x)) μ.measure) = _
  rw [integral_map_of_stronglyMeasurable (measurable_of_countable _)
    (measurable_of_countable _).stronglyMeasurable]
  exact integral_congr_ae (Eventually.of_forall (distance_truncate K))

/-- Truncation error is controlled by the actual moment tail. -/
theorem wasserstein_truncateLaw_le (μ : MomentLaw κ D) (K : ℕ) :
    wasserstein μ (truncateLaw μ K) ≤ ∫ x, tailWeight κ K x ∂μ.measure :=
  (wasserstein_le_cost (truncationCoupling μ K)).trans_eq (truncationCoupling_cost μ K)

/-- Every finite-moment law is approximated in transport by finite-state laws. -/
theorem wasserstein_truncateLaw_tendsto_zero (μ : MomentLaw κ D) :
    Tendsto (fun K => wasserstein μ (truncateLaw μ K)) atTop (𝓝 0) :=
  squeeze_zero (fun _ => wasserstein_nonneg _ _) (wasserstein_truncateLaw_le μ)
    (integral_tailWeight_tendsto_zero μ)

omit [MeasurableSpace Ω] in
/-- Truncation commutes with the empirical-law construction. -/
theorem truncateLaw_sampleLaw (X : ℕ → Ω → State D) (n : ℕ) (ω : Ω) (K : ℕ) :
    truncateLaw (sampleLaw κ X n ω) K =
      sampleLaw κ (fun i ω => truncate κ K (X i ω)) n ω := by
  apply MomentLaw.ext
  exact map_empiricalMeasure _ (truncate κ K) (measurable_of_countable _)

omit [MeasurableSpace Ω] in
/-- The finite-state empirical approximation has an exact moment-tail bound. -/
theorem sample_truncation_bound (X : ℕ → Ω → State D) (n : ℕ) (ω : Ω) (K : ℕ) :
    wasserstein (sampleLaw κ X n ω)
      (sampleLaw κ (fun i ω => truncate κ K (X i ω)) n ω) ≤
      ∫ x, tailWeight κ K x ∂(sampleLaw κ X n ω).measure := by
  rw [← truncateLaw_sampleLaw]
  exact wasserstein_truncateLaw_le _ K

end CarryingCapacity.EmpiricalLLN
