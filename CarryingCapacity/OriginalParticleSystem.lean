import CarryingCapacity.ArbitraryInitialNonexplosion
import CarryingCapacity.Symmetrization

/-!
# The actual finite system under the original paper's assumptions

The rates are evaluated at genuine empirical probability measures, without a
moment-law restriction. The original linear growth bound gives a total-population
Lyapunov estimate with finite sublevels. The previously constructed common-noise
localizations then give nonexplosion and the counting equation for arbitrary
independent initial laws. This does not assert the Feller/core conclusion of
Proposition 2.3, the Markov property, or the mean-field theorem.

Source: DeWitt--Evans--Hiesmayr--Hummel, arXiv:2307.06010v2, Assumption 2.1.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.OriginalParticleSystem
open ConfigurationLocalization CommonInitialNoise

variable {N D : ℕ}

/-- Total number of individuals in all lineages, as a real Lyapunov function. -/
def totalPopulation (z : Configuration N D) : ℝ := ∑ i, populationSize (z i)

theorem population_nonnegative (x : State D) : 0 ≤ populationSize x :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem totalPopulation_nonnegative (z : Configuration N D) : 0 ≤ totalPopulation z :=
  Finset.sum_nonneg (fun _ _ => population_nonnegative _)

/-- Updating one coordinate gives its exact contribution to total population. -/
theorem population_update_sub (x : State D) (i : Fin D) (n : ℕ) :
    populationSize (Function.update x i n) - populationSize x = (n : ℝ) - x i := by
  unfold populationSize
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · simp

theorem population_birth_sub (x : State D) (i : Fin D) :
    populationSize (Jump.advance (Jump.birth i) x) - populationSize x = 1 := by
  rw [Jump.birth, Jump.advance, population_update_sub]
  push_cast
  ring

theorem population_death_sub_nonpos (x : State D) (i : Fin D) :
    populationSize (Jump.advance (Jump.death i) x) - populationSize x ≤ 0 := by
  simp only [Jump.death, Jump.advance]
  split_ifs with hi
  · rw [population_update_sub]
    have h : ((x i - 1 : ℕ) : ℝ) ≤ x i := by exact_mod_cast Nat.sub_le (x i) 1
    linarith
  · simp

theorem population_mutation_sub (x : State D) (i j : Fin D) (hij : i ≠ j) :
    populationSize (Jump.advance (Jump.mutation i j hij) x) - populationSize x = 0 := by
  simp only [Jump.mutation, Jump.advance]
  split_ifs with hi
  · have hfirst := population_update_sub x i (x i - 1)
    have hsecond := population_update_sub (Function.update x i (x i - 1)) j (x j + 1)
    simp only [Function.update_of_ne hij.symm, Nat.cast_add, Nat.cast_one] at hsecond
    have hcast : ((x i - 1 : ℕ) : ℝ) = (x i : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ x i)]
      simp
    rw [hcast] at hfirst
    linarith
  · simp

/-- A finite total-population sublevel contains only finitely many configurations. -/
theorem finite_totalPopulation_sublevel (R : ℝ) :
    {z : Configuration N D | totalPopulation z < R}.Finite := by
  apply (Set.finite_Iic (fun _ : Fin N => fun _ : Fin D => Nat.ceil R)).subset
  intro z hz i j
  have hc : (z i j : ℝ) ≤ populationSize (z i) :=
    Finset.single_le_sum (fun k _ => Nat.cast_nonneg (z i k)) (Finset.mem_univ j)
  have hp : populationSize (z i) ≤ totalPopulation z :=
    Finset.single_le_sum (fun k _ => population_nonnegative (z k)) (Finset.mem_univ i)
  have hceil := ((hc.trans hp).trans hz.le).trans (Nat.le_ceil R)
  exact_mod_cast hceil

/-- A one-lineage update changes total population by that lineage's increment. -/
theorem totalPopulation_jump_sub (h : Label N D) (z : Configuration N D) :
    totalPopulation (jump h z) - totalPopulation z =
      populationSize (Jump.advance h.2 (z h.1)) - populationSize (z h.1) := by
  unfold totalPopulation jump
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single h.1]
  · simp
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · simp

variable (q : Rates D (ProbabilityMeasure (State D)))

/-- The original law argument is the empirical probability measure itself. -/
def rate (hN : 0 < N) (h : Label N D) (z : Configuration N D) : ℝ :=
  q.rate h.2 (z h.1) (Symmetrization.empiricalProbability hN z)

theorem rate_nonnegative (hN : 0 < N) (h : Label N D) (z : Configuration N D) :
    0 ≤ rate q hN h z := q.nonnegative _ _ _

/-- The original particle generator on arbitrary real configuration tests. -/
def generator (hN : 0 < N) (F : Configuration N D → ℝ) (z : Configuration N D) : ℝ :=
  ∑ h : Label N D, rate q hN h z * (F (jump h z) - F z)

theorem generator_eq_systemGenerator (hN : 0 < N)
    (F : Configuration N D → ℝ) (z : Configuration N D) :
    generator q hN F z = FiniteGenerator.systemGenerator Jump.advance q.rate
      (Symmetrization.empiricalProbability hN) F z := by
  unfold generator FiniteGenerator.systemGenerator rate
  rw [Fintype.sum_prod_type]
  rfl

variable (original : OriginalAssumptions q)

/-- A constant from the original uniform linear-growth and TV assumptions. -/
def growthConstant : ℝ := Classical.choose original.bounds

theorem growthConstant_nonnegative : 0 ≤ growthConstant q original :=
  (Classical.choose_spec original.bounds).1

theorem growth_bound (h : Jump D) (x : State D) (ν : ProbabilityMeasure (State D)) :
    q.rate h x ν ≤ growthConstant q original * (populationSize x + 1) :=
  (Classical.choose_spec original.bounds).2.1 h x ν

/-- Only births contribute positively to total population; mutations conserve it. -/
theorem single_population_drift_le (x : State D) (ν : ProbabilityMeasure (State D)) :
    q.generator ν populationSize x ≤ (D : ℝ) * growthConstant q original * (populationSize x + 1) := by
  have hs : q.generator ν populationSize x ≤ ∑ h : Jump D,
      (match h with
       | .inl (.inl _) => growthConstant q original * (populationSize x + 1)
       | _ => 0) := by
    apply Finset.sum_le_sum
    intro h _
    rcases h with (i | i) | ⟨⟨i,j⟩, hij⟩
    · change q.rate (Jump.birth i) x ν *
        (populationSize (Jump.advance (Jump.birth i) x) - populationSize x) ≤ _
      rw [population_birth_sub, mul_one]
      exact growth_bound q original _ _ _
    · change q.rate (Jump.death i) x ν *
        (populationSize (Jump.advance (Jump.death i) x) - populationSize x) ≤ 0
      exact mul_nonpos_of_nonneg_of_nonpos (q.nonnegative _ _ _) (population_death_sub_nonpos x i)
    · change q.rate (Jump.mutation i j hij) x ν *
        (populationSize (Jump.advance (Jump.mutation i j hij) x) - populationSize x) ≤ 0
      rw [population_mutation_sub, mul_zero]
  simpa only [Fintype.sum_sum_type, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_const_zero, mul_zero, add_zero, mul_assoc] using hs

/-- Exact finite-system total-population generator identity. -/
theorem generator_totalPopulation (hN : 0 < N) (z : Configuration N D) :
    generator q hN totalPopulation z =
      ∑ i, q.generator (Symmetrization.empiricalProbability hN z) populationSize (z i) := by
  unfold generator
  simp_rw [totalPopulation_jump_sub]
  rw [Fintype.sum_prod_type]
  rfl

/-- The original linear growth bound directly yields a configuration Lyapunov bound. -/
theorem generator_totalPopulation_le (hN : 0 < N) (z : Configuration N D) :
    generator q hN totalPopulation z ≤
      (D : ℝ) * growthConstant q original * (totalPopulation z + N) := by
  rw [generator_totalPopulation]
  calc
    _ ≤ ∑ i, (D : ℝ) * growthConstant q original * (populationSize (z i) + 1) :=
      Finset.sum_le_sum (fun i _ => single_population_drift_le q original (z i) _)
    _ = _ := by
      rw [← Finset.mul_sum]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, totalPopulation]

/-- A finite affine drift constant for each original finite particle system. -/
def driftConstant : ℝ := (D : ℝ) * growthConstant q original * ((N : ℝ) + 1)

theorem driftConstant_nonnegative : 0 ≤ driftConstant (N := N) q original := by
  unfold driftConstant
  have hL := growthConstant_nonnegative q original
  positivity

/-- The precise affine form required by the actual nonexplosion construction. -/
theorem generator_affine_bound (hN : 0 < N) (z : Configuration N D) :
    (∑ h : Label N D, rate q hN h z * (totalPopulation (jump h z) - totalPopulation z)) ≤
      driftConstant (N := N) q original * (1 + totalPopulation z) := by
  have hb := generator_totalPopulation_le q original hN z
  have hL := growthConstant_nonnegative q original
  have hV := totalPopulation_nonnegative z
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  change generator q hN totalPopulation z ≤ _
  apply hb.trans
  unfold driftConstant
  have hcoef : 0 ≤ (D : ℝ) * growthConstant q original := mul_nonneg (Nat.cast_nonneg D) hL
  calc
    _ ≤ ((D : ℝ) * growthConstant q original) * (((N : ℝ) + 1) * (1 + totalPopulation z)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hcoef
    _ = _ := by ring


section Process
variable {A : Type*} (hN : 0 < N) (initial : A → Configuration N D)

/-- The original finite system on the actual independent initial/noise space. -/
def process (p : Sample A (Label N D)) (t : ℝ) : Configuration N D :=
  GlobalLocalizedProcess.process totalPopulation finite_totalPopulation_sublevel
    jump (rate q hN) initial 0 p t

/-- The genuine exit of the total-population localization at integer level n. -/
def exit (n : ℕ) (p : Sample A (Label N D)) : ℝ≥0∞ :=
  LyapunovLocalization.exit totalPopulation finite_totalPopulation_sublevel
    jump (rate q hN) initial n p

/-- The actual strict-past representative used by the counting equation. -/
def preState (p : Sample A (Label N D)) (t : ℝ) : Configuration N D :=
  GlobalLocalizedCountingIdentity.preState totalPopulation finite_totalPopulation_sublevel
    jump (rate q hN) initial 0 p t

/-- The original accepted-increment field, with neither active-set nor height cutoff. -/
def horizonIncrement (F : Configuration N D → ℝ) (j : Label N D) (T : ℝ)
    (p : Sample A (Label N D) × (ℝ × ℝ)) : ℝ :=
  GlobalLocalizedCountingIdentity.horizonIncrement totalPopulation finite_totalPopulation_sublevel
    jump (rate q hN) initial 0 F j T p

/-- The field is exactly the time-windowed rate-threshold jump increment. -/
theorem horizonIncrement_apply (F : Configuration N D → ℝ) (j : Label N D) (T : ℝ)
    (p : Sample A (Label N D)) (r : ℝ × ℝ) :
    horizonIncrement q hN initial F j T (p,r) =
      if r.1 ∈ Ioc 0 T ∧ r.2 ≤ rate q hN j (preState q hN initial p r.1)
      then F (jump j (preState q hN initial p r.1)) - F (preState q hN initial p r.1) else 0 :=
  GlobalLocalizedCountingIdentity.horizonIncrement_apply totalPopulation finite_totalPopulation_sublevel
    jump (rate q hN) initial 0 F j T p r

variable [MeasurableSpace A]

/-- Joint measurability of the actual original-model construction. -/
theorem measurable_process (hinit : Measurable initial) :
    Measurable (fun p : Sample A (Label N D) × ℝ => process q hN initial p.1 p.2) :=
  GlobalLocalizedProcess.measurable_process totalPopulation finite_totalPopulation_sublevel
    jump (rate q hN) initial 0 hinit

/-- Adaptedness to the raw initial-record plus arrived-mark history. -/
theorem measurable_process_at (hinit : Measurable initial) (t : ℝ) :
    Measurable[CommonInitialNoise.filtration A (Label N D) t]
      (fun p => process q hN initial p t) :=
  GlobalLocalizedProcess.measurable_process_at totalPopulation finite_totalPopulation_sublevel
    jump (rate q hN) initial 0 hinit t

variable (μ : Measure A)

/-- The prescribed sampled initial state is retained. -/
theorem ae_initial : ∀ᵐ p ∂law μ (Label N D), process q hN initial p 0 = initial p.1 :=
  GlobalLocalizedProcess.ae_process_zero totalPopulation finite_totalPopulation_sublevel
    jump (rate q hN) initial 0 μ

include original

/-- Original Assumption 2.1 implies actual nonexplosion for every independent
initial law. There is no initial moment, tail, or compact-support condition. -/
theorem ae_exhaustive : ∀ᵐ p ∂law μ (Label N D), ∀ T : ℝ≥0, ∃ n,
    (T : ℝ≥0∞) < exit q hN initial n p :=
  ArbitraryInitialNonexplosion.ae_exhaustive totalPopulation finite_totalPopulation_sublevel
    jump (rate q hN) initial (driftConstant (N := N) q original)
    (driftConstant_nonnegative q original) totalPopulation_nonnegative
    (fun z j => rate_nonnegative q hN j z) (generator_affine_bound q original hN) μ

/-- The original-model paths are cadlag under arbitrary independent initial laws. -/
theorem ae_cadlag : ∀ᵐ p ∂law μ (Label N D),
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (process q hN initial p) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : Configuration N D,
      Tendsto (process q hN initial p) (𝓝[<] t) (𝓝 y)) :=
  GlobalLocalizedProcess.ae_process_cadlag totalPopulation finite_totalPopulation_sublevel
    jump (rate q hN) initial 0 μ (ae_exhaustive q original hN initial μ)

/-- Nonexplosion gives finite actual jump activity on every bounded horizon. -/
theorem ae_finite_activity : ∀ᵐ p ∂law μ (Label N D), ∀ T : ℝ≥0,
    ∃ times : Finset ℝ, (times : Set ℝ) ⊆ Ioc 0 T ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        (∀ u ∈ times, u ∉ Ioc s t) → process q hN initial p s = process q hN initial p t := by
  filter_upwards [GlobalLocalizedActivity.ae_finite_activity totalPopulation finite_totalPopulation_sublevel
    jump (rate q hN) initial 0 μ (ae_exhaustive q original hN initial μ)] with p hp
  intro T
  obtain ⟨n, hn, hconst⟩ := hp T
  exact ⟨GlobalLocalizedActivity.horizonTimes totalPopulation finite_totalPopulation_sublevel
    (rate q hN) n p T, hn, hconst⟩

/-- Pathwise integrability of every real test's accepted increments. -/
theorem ae_integrable_horizonIncrement : ∀ᵐ p ∂law μ (Label N D),
    ∀ (T : ℝ≥0) (F : Configuration N D → ℝ) (j : Label N D),
      Integrable (fun r => horizonIncrement q hN initial F j T (p,r))
        (MarkedNoise.countingMeasure j p.2) :=
  GlobalLocalizedCountingIdentity.ae_integrable_horizonIncrement totalPopulation
    finite_totalPopulation_sublevel jump (rate q hN) initial 0 μ
      (ae_exhaustive q original hN initial μ)

/-- The actual original finite system solves the unrestricted counting equation. -/
theorem ae_counting_identity (F : Configuration N D → ℝ) :
    ∀ᵐ p ∂law μ (Label N D), ∀ T : ℝ≥0,
      F (process q hN initial p T) - F (initial p.1) =
        ∑ j : Label N D, ∫ r, horizonIncrement q hN initial F j T (p,r)
          ∂MarkedNoise.countingMeasure j p.2 :=
  GlobalLocalizedCountingIdentity.ae_testFunction_counting_identity totalPopulation
    finite_totalPopulation_sublevel jump (rate q hN) initial 0 μ F
      (ae_exhaustive q original hN initial μ)

/-- Coordinate equations are simultaneous over the finite family of particles
and types and every nonnegative time. -/
theorem ae_coordinate_counting_identity : ∀ᵐ p ∂law μ (Label N D),
    ∀ i : Fin N × Fin D, ∀ T : ℝ≥0,
      (process q hN initial p T i.1 i.2 : ℝ) - (initial p.1 i.1 i.2 : ℝ) =
        ∑ j : Label N D, ∫ r, horizonIncrement q hN initial
          (ActualGlobalUniqueness.ConfigurationCoordinates.test i) j T (p,r)
          ∂MarkedNoise.countingMeasure j p.2 :=
  ae_all_iff.mpr (fun i => ae_counting_identity q original hN initial μ
    (ActualGlobalUniqueness.ConfigurationCoordinates.test i))

/-- Pathwise uniqueness follows from the original particle-coordinate equations,
with no candidate moment or finite-activity hypothesis. -/
theorem ae_eq_of_coordinate_equations
    (X : Sample A (Label N D) → ℝ → Configuration N D)
    (hcadlag : ∀ᵐ p ∂law μ (Label N D),
      (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (X p) (Ici t) t) ∧
      (∀ t : ℝ, 0 < t → ∃ y : Configuration N D, Tendsto (X p) (𝓝[<] t) (𝓝 y)))
    (hzero : ∀ᵐ p ∂law μ (Label N D), X p 0 = initial p.1)
    (heq : ∀ i : Fin N × Fin D, ∀ᵐ p ∂law μ (Label N D), ∀ T : ℝ≥0,
      (X p T i.1 i.2 : ℝ) - (initial p.1 i.1 i.2 : ℝ) =
        ∑ j : Label N D, ∫ r, GlobalCountingUniqueness.candidateIncrement jump (rate q hN) X 0
          (ActualGlobalUniqueness.ConfigurationCoordinates.test i) j T (p,r)
            ∂MarkedNoise.countingMeasure j p.2) :
    ∀ᵐ p ∂law μ (Label N D), ∀ t : ℝ, 0 ≤ t → X p t = process q hN initial p t :=
  GlobalCountingUniqueness.ae_candidate_eq_process_of_separating_tests
    totalPopulation finite_totalPopulation_sublevel jump (rate q hN) initial 0 μ
    ActualGlobalUniqueness.ConfigurationCoordinates.test
    ActualGlobalUniqueness.ConfigurationCoordinates.separate
    (ae_exhaustive q original hN initial μ) X hcadlag hzero heq

end Process

end CarryingCapacity.OriginalParticleSystem
