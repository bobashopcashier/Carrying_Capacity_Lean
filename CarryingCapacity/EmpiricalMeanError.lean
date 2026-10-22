import CarryingCapacity.EmpiricalLLN

/-!
# Expected empirical transport error

The finite-sample Lyapunov integrals and their expectations are derived from the
actual common marginal law. The empirical transport strong law and the proved
Lyapunov uniform-integrability theorem then give convergence of expected error.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

namespace CarryingCapacity.EmpiricalMeanError
open EmpiricalLLN

variable {Ω : Type*} [MeasurableSpace Ω] {D : ℕ} {κ : MomentScale}

theorem integrable_sampleMean (P : Measure Ω) (μ : MomentLaw κ D)
    (X : ℕ → Ω → State D) (hm : ∀ i, Measurable (X i))
    (hlaw : ∀ i, Measure.map (X i) P = μ.measure)
    (f : State D → ℝ) (hf : Integrable f μ.measure) (n : ℕ) :
    Integrable (fun ω => FiniteGenerator.empiricalMean f (sampleConfig X n ω)) P := by
  apply Integrable.const_mul
  apply integrable_finset_sum
  intro i _
  have hh : Integrable f (Measure.map (X i.val) P) := by rwa [hlaw]
  exact hh.comp_measurable (hm i.val)

/-- The expected empirical average is exactly the common-law integral. -/
theorem integral_sampleMean (P : Measure Ω) (μ : MomentLaw κ D)
    (X : ℕ → Ω → State D) (hm : ∀ i, Measurable (X i))
    (hlaw : ∀ i, Measure.map (X i) P = μ.measure)
    (f : State D → ℝ) (hf : Integrable f μ.measure) (n : ℕ) :
    (∫ ω, FiniteGenerator.empiricalMean f (sampleConfig X n ω) ∂P) = ∫ x, f x ∂μ.measure := by
  have hi (i : ℕ) : Integrable (fun ω => f (X i ω)) P := by
    have hh : Integrable f (Measure.map (X i) P) := by rwa [hlaw]
    exact hh.comp_measurable (hm i)
  have he (i : ℕ) : (∫ ω, f (X i ω) ∂P) = ∫ x, f x ∂μ.measure := by
    rw [← integral_map_of_stronglyMeasurable (hm i)
      (measurable_of_countable f).stronglyMeasurable, hlaw i]
  unfold FiniteGenerator.empiricalMean sampleConfig
  rw [integral_const_mul, integral_finset_sum _ (fun i _ => hi i.val)]
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- Finite configurations form a countable discrete space, so transport to a
fixed target is measurable without postulating measurability of the error. -/
theorem measurable_sampleError (μ : MomentLaw κ D) (X : ℕ → Ω → State D)
    (hm : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable (fun ω => wasserstein (sampleLaw κ X n ω) μ) := by
  have hc : Measurable (fun ω => sampleConfig X n ω) := measurable_pi_lambda _ fun i => hm i.val
  exact (measurable_of_countable (fun z : Fin (n + 1) → State D =>
    wasserstein (empiricalLaw κ (Nat.succ_pos n) z) μ)).comp hc

section Probability
variable (P : Measure Ω) [IsProbabilityMeasure P]

theorem integrable_sampleError (μ : MomentLaw κ D) (X : ℕ → Ω → State D)
    (hm : ∀ i, Measurable (X i)) (hlaw : ∀ i, Measure.map (X i) P = μ.measure) (n : ℕ) :
    Integrable (fun ω => wasserstein (sampleLaw κ X n ω) μ) P := by
  have havg := integrable_sampleMean P μ X hm hlaw (momentWeight κ) μ.integrable_weight n
  apply (havg.add (integrable_const (moment μ))).mono'
    (measurable_sampleError μ X hm n).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (wasserstein_nonneg _ _)]
    simpa only [sampleLaw, moment_empiricalLaw, Pi.add_apply] using
      wasserstein_le_moments (sampleLaw κ X n ω) μ

/-- The common marginal gives the manuscript's uniform error bound. -/
theorem integral_sampleError_le (μ : MomentLaw κ D) (X : ℕ → Ω → State D)
    (hm : ∀ i, Measurable (X i)) (hlaw : ∀ i, Measure.map (X i) P = μ.measure) (n : ℕ) :
    (∫ ω, wasserstein (sampleLaw κ X n ω) μ ∂P) ≤ 2 * moment μ := by
  have havg := integrable_sampleMean P μ X hm hlaw (momentWeight κ) μ.integrable_weight n
  calc
    _ ≤ ∫ ω, (FiniteGenerator.empiricalMean (momentWeight κ) (sampleConfig X n ω) + moment μ) ∂P :=
      integral_mono (integrable_sampleError P μ X hm hlaw n)
        (havg.add (integrable_const _)) (fun ω => by
          simpa only [sampleLaw, moment_empiricalLaw] using
            wasserstein_le_moments (sampleLaw κ X n ω) μ)
    _ = 2 * moment μ := by
      rw [integral_add havg (integrable_const _), integral_sampleMean P μ X hm hlaw _ μ.integrable_weight]
      simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      change moment μ + moment μ = 2 * moment μ
      ring

/-- Uniform integrability follows from the actual common-law Lyapunov integral,
with no separately assumed expected empirical bound. -/
theorem uniformIntegrable_sampleError (μ : MomentLaw κ D) (Ψ : State D → ℝ)
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (hΨ : Integrable Ψ μ.measure) (X : ℕ → Ω → State D)
    (hm : ∀ i, Measurable (X i)) (hlaw : ∀ i, Measure.map (X i) P = μ.measure) :
    UniformIntegrable (fun n ω => wasserstein (sampleLaw κ X n ω) μ) 1 P := by
  apply LyapunovTails.uniformIntegrable_empirical_transport P hdom hsuper
    (fun n => n + 1) Nat.succ_pos (fun n ω => sampleConfig X n ω) μ
    (fun n => (measurable_sampleError μ X hm n).aestronglyMeasurable)
    (integrable_sampleMean P μ X hm hlaw Ψ hΨ) (∫ x, Ψ x ∂μ.measure)
  · apply integral_nonneg
    intro x
    change 0 ≤ Ψ x
    linarith [hdom x, momentWeight_nonneg κ x]
  · intro n
    exact (integral_sampleMean P μ X hm hlaw Ψ hΨ n).le

/-- Fixed-time expected empirical transport error tends to zero. Almost-sure
transport convergence and uniform integrability are both proved from the stated
probabilistic and Lyapunov hypotheses. -/
theorem integral_sampleError_tendsto_zero (μ : MomentLaw κ D) (Ψ : State D → ℝ)
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (hΨ : Integrable Ψ μ.measure) (X : ℕ → Ω → State D)
    (hm : ∀ i, Measurable (X i))
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) P))
    (hlaw : ∀ i, Measure.map (X i) P = μ.measure) :
    Tendsto (fun n => ∫ ω, wasserstein (sampleLaw κ X n ω) μ ∂P) atTop (𝓝 0) := by
  have hui := uniformIntegrable_sampleError P μ Ψ hdom hsuper hΨ X hm hlaw
  have hconv : TendstoInMeasure P (fun n ω => wasserstein (sampleLaw κ X n ω) μ) atTop 0 :=
    tendstoInMeasure_of_tendsto_ae (fun n => (measurable_sampleError μ X hm n).aestronglyMeasurable)
      (wasserstein_strongLaw P μ X hm hind hlaw)
  have hh := LyapunovTails.integral_abs_tendsto_zero_of_uniformIntegrable P _ hui hconv
  simpa only [abs_of_nonneg (wasserstein_nonneg _ _)] using hh

/-- Finite Ψ-moment itself supplies the finite κ-moment required by the expected
transport convergence theorem. -/
theorem integral_sampleError_tendsto_zero_of_lyapunov
    (μ : ProbabilityMeasure (State D)) (Ψ : State D → ℝ)
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (hΨ : Integrable Ψ (μ : Measure (State D))) (X : ℕ → Ω → State D)
    (hm : ∀ i, Measurable (X i))
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) P))
    (hlaw : ∀ i, Measure.map (X i) P = (μ : Measure (State D))) :
    Tendsto (fun n => ∫ ω,
      wasserstein (sampleLaw κ X n ω) (lawOfLyapunov μ Ψ hdom hΨ) ∂P) atTop (𝓝 0) :=
  integral_sampleError_tendsto_zero P (lawOfLyapunov μ Ψ hdom hΨ) Ψ hdom hsuper hΨ X hm hind hlaw

end Probability

section Time
variable {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]

/-- Joint measurability of transport error follows from jointly measurable
samples and a continuous law curve. The countable configuration variable avoids
assuming a separate measurable-space structure on the space of laws. -/
theorem measurable_joint_sampleError (ν : T → MomentLaw κ D) (hν : Continuous ν)
    (X : ℕ → T → Ω → State D) (hm : ∀ i, Measurable (Function.uncurry (X i))) (n : ℕ) :
    Measurable (fun p : T × Ω =>
      wasserstein (sampleLaw κ (fun i => X i p.1) n p.2) (ν p.1)) := by
  have hF : Measurable (fun p : T × (Fin (n + 1) → State D) =>
      wasserstein (empiricalLaw κ (Nat.succ_pos n) p.2) (ν p.1)) := by
    apply measurable_from_prod_countable
    intro z
    change Measurable (fun t => dist (empiricalLaw κ (Nat.succ_pos n) z) (ν t))
    have hc : Continuous (fun t : T => dist (empiricalLaw κ (Nat.succ_pos n) z) (ν t)) :=
      (continuous_const : Continuous (fun _ : T => empiricalLaw κ (Nat.succ_pos n) z)).dist hν
    exact hc.measurable
  have hz : Measurable (fun p : T × Ω => (fun i : Fin (n + 1) => X i.val p.1 p.2)) :=
    measurable_pi_lambda _ fun i => hm i.val
  have hconf := (measurable_fst : Measurable (fun p : T × Ω => p.1)).prodMk hz
  simpa only [Function.comp_def, sampleLaw, sampleConfig] using hF.comp hconf

/-- Section 7's integrated independent empirical error. Joint measurability,
the common marginal, and a uniform Lyapunov integral bound supply every
measurability and domination input to the time dominated-convergence theorem.
The time measure may in particular be Lebesgue measure restricted to `[0,T]`. -/
theorem integral_time_sampleError_tendsto_zero
    (τ : Measure T) [IsFiniteMeasure τ] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : T → MomentLaw κ D) (hν : Continuous ν) (Ψ : State D → ℝ)
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (hΨ : ∀ t, Integrable Ψ (ν t).measure)
    (C : ℝ) (hbound : ∀ t, (∫ x, Ψ x ∂(ν t).measure) ≤ C)
    (X : ℕ → T → Ω → State D) (hm : ∀ i, Measurable (Function.uncurry (X i)))
    (hind : ∀ t, Pairwise (fun i j => IndepFun (X i t) (X j t) P))
    (hlaw : ∀ t i, Measure.map (X i t) P = (ν t).measure) :
    Tendsto (fun n => ∫ t, (∫ ω,
      wasserstein (sampleLaw κ (fun i => X i t) n ω) (ν t) ∂P) ∂τ) atTop (𝓝 0) := by
  have hXm (t : T) (i : ℕ) : Measurable (X i t) :=
    (hm i).comp (measurable_const.prodMk measurable_id)
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun t => ∫ ω,
      wasserstein (sampleLaw κ (fun i => X i t) n ω) (ν t) ∂P) τ :=
    (measurable_joint_sampleError ν hν X hm n).stronglyMeasurable.integral_prod_right.aestronglyMeasurable
  have hpoint (t : T) := integral_sampleError_tendsto_zero P (ν t) Ψ hdom hsuper (hΨ t)
    (fun i => X i t) (hXm t) (hind t) (hlaw t)
  have hmajor (n : ℕ) (t : T) :
      ‖∫ ω, wasserstein (sampleLaw κ (fun i => X i t) n ω) (ν t) ∂P‖ ≤ 2 * C := by
    rw [Real.norm_of_nonneg (integral_nonneg (fun ω => wasserstein_nonneg _ _))]
    have hκ : moment (ν t) ≤ ∫ x, Ψ x ∂(ν t).measure := by
      apply integral_mono (ν t).integrable_weight (hΨ t)
      intro x
      linarith [hdom x]
    have he := integral_sampleError_le P (ν t) (fun i => X i t) (hXm t) (hlaw t) n
    linarith [hbound t]
  have hh := tendsto_integral_of_dominated_convergence (fun _ : T => 2 * C)
    hmeas (integrable_const (2 * C)) (fun n => Eventually.of_forall (hmajor n))
    (Eventually.of_forall hpoint)
  simpa only [integral_zero] using hh

end Time

end CarryingCapacity.EmpiricalMeanError
