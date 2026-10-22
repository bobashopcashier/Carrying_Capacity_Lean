import CarryingCapacity.EmpiricalMeanError

/-!
# Independent empirical arrays

Finite iid vectors have the actual product pushforward law. Their empirical
errors are therefore identically distributed with the errors of initial
segments of a constructed infinite iid sequence. This transfers expected-error
convergence to arrays whose samples and probability spaces may depend on N.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

namespace CarryingCapacity.EmpiricalArrayError
open EmpiricalLLN EmpiricalMeanError

variable {D : ℕ} {κ : MomentScale}

/-- The canonical countable iid sample space, with the stated common law. -/
def canonicalLaw (μ : MomentLaw κ D) : Measure (ℕ → State D) := by
  letI : IsProbabilityMeasure μ.measure := μ.probability
  exact Measure.infinitePi (fun _ : ℕ => μ.measure)

instance canonicalLaw_probability (μ : MomentLaw κ D) : IsProbabilityMeasure (canonicalLaw μ) := by
  unfold canonicalLaw
  letI : IsProbabilityMeasure μ.measure := μ.probability
  infer_instance

theorem canonical_coordinate_event (μ : MomentLaw κ D) (i : ℕ)
    (s : Set (State D)) (hs : MeasurableSet s) :
    canonicalLaw μ {ω | ω i ∈ s} = μ.measure s := by
  have he : {ω : ℕ → State D | ω i ∈ s} = Set.pi ({i} : Finset ℕ) (fun _ => s) := by
    ext ω
    simp
  unfold canonicalLaw
  letI : IsProbabilityMeasure μ.measure := μ.probability
  rw [he, Measure.infinitePi_pi _ (fun _ _ => hs)]
  simp

theorem canonical_coordinate_map (μ : MomentLaw κ D) (i : ℕ) :
    Measure.map (fun ω : ℕ → State D => ω i) (canonicalLaw μ) = μ.measure := by
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  exact canonical_coordinate_event μ i s hs

theorem canonical_independent (μ : MomentLaw κ D) :
    iIndepFun (fun i (ω : ℕ → State D) => ω i) (canonicalLaw μ) := by
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S sets hs
  have he : (⋂ i ∈ S, (fun ω : ℕ → State D => ω i) ⁻¹' sets i) = Set.pi S sets := by
    ext ω
    simp
  rw [he]
  unfold canonicalLaw
  letI : IsProbabilityMeasure μ.measure := μ.probability
  rw [Measure.infinitePi_pi _ hs]
  apply Finset.prod_congr rfl
  intro i hi
  exact (canonical_coordinate_event μ i (sets i) (hs i hi)).symm

section Vector
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {N : ℕ}

/-- Joint independence and the actual coordinate marginals determine the full
finite-vector law, not only the separate one-coordinate distributions. -/
theorem iid_vector_map (μ : MomentLaw κ D) (Y : Fin N → Ω → State D)
    (hm : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (hlaw : ∀ i, Measure.map (Y i) P = μ.measure) :
    Measure.map (fun ω i => Y i ω) P = Measure.pi (fun _ : Fin N => μ.measure) := by
  rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hm i).aemeasurable)).mp hind]
  simp_rw [hlaw]

theorem canonical_vector_map (μ : MomentLaw κ D) (n : ℕ) :
    Measure.map (fun ω (i : Fin (n + 1)) => ω i.val) (canonicalLaw μ) =
      Measure.pi (fun _ : Fin (n + 1) => μ.measure) := by
  exact iid_vector_map (canonicalLaw μ) μ (fun i ω => ω i.val)
    (fun i => measurable_pi_apply i.val) ((canonical_independent μ).precomp Fin.val_injective)
    (fun i => canonical_coordinate_map μ i.val)

/-- Empirical transport errors have the same distribution as those of the
constructed infinite iid sequence. -/
theorem error_identDistrib (μ : MomentLaw κ D) (n : ℕ) (Y : Fin (n + 1) → Ω → State D)
    (hm : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (hlaw : ∀ i, Measure.map (Y i) P = μ.measure) :
    IdentDistrib
      (fun ω => wasserstein (empiricalLaw κ (Nat.succ_pos n) (fun i => Y i ω)) μ)
      (fun ω => wasserstein (sampleLaw κ (fun i (ω : ℕ → State D) => ω i) n ω) μ)
      P (canonicalLaw μ) := by
  have hv : IdentDistrib (fun ω i => Y i ω)
      (fun (ω : ℕ → State D) (i : Fin (n + 1)) => ω i.val) P (canonicalLaw μ) :=
    ⟨(measurable_pi_lambda _ hm).aemeasurable,
      (measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)).aemeasurable,
      (iid_vector_map P μ Y hm hind hlaw).trans (canonical_vector_map μ n).symm⟩
  exact hv.comp (measurable_of_countable (fun z : Fin (n + 1) → State D =>
    wasserstein (empiricalLaw κ (Nat.succ_pos n) z) μ))

/-- In particular, the transferred finite-array error is genuinely integrable. -/
theorem integrable_error (μ : MomentLaw κ D) (n : ℕ) (Y : Fin (n + 1) → Ω → State D)
    (hm : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (hlaw : ∀ i, Measure.map (Y i) P = μ.measure) :
    Integrable (fun ω => wasserstein (empiricalLaw κ (Nat.succ_pos n) (fun i => Y i ω)) μ) P := by
  apply (error_identDistrib P μ n Y hm hind hlaw).integrable_iff.mpr
  exact integrable_sampleError (canonicalLaw μ) μ (fun i ω => ω i)
    (fun i => measurable_pi_apply i) (canonical_coordinate_map μ) n

theorem integral_error_eq (μ : MomentLaw κ D) (n : ℕ) (Y : Fin (n + 1) → Ω → State D)
    (hm : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (hlaw : ∀ i, Measure.map (Y i) P = μ.measure) :
    (∫ ω, wasserstein (empiricalLaw κ (Nat.succ_pos n) (fun i => Y i ω)) μ ∂P) =
      ∫ ω, wasserstein (sampleLaw κ (fun i (ω : ℕ → State D) => ω i) n ω) μ ∂canonicalLaw μ :=
  (error_identDistrib P μ n Y hm hind hlaw).integral_eq

theorem integral_error_le (μ : MomentLaw κ D) (n : ℕ) (Y : Fin (n + 1) → Ω → State D)
    (hm : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (hlaw : ∀ i, Measure.map (Y i) P = μ.measure) :
    (∫ ω, wasserstein (empiricalLaw κ (Nat.succ_pos n) (fun i => Y i ω)) μ ∂P) ≤ 2 * moment μ := by
  rw [integral_error_eq P μ n Y hm hind hlaw]
  exact integral_sampleError_le (canonicalLaw μ) μ (fun i ω => ω i)
    (fun i => measurable_pi_apply i) (canonical_coordinate_map μ) n

end Vector

/-- The expected-error limit transfers to arbitrary N-dependent iid rows, even
when the probability spaces of different rows differ. There is no independence
assumption between rows and no compatibility assumption across N. -/
theorem integral_arrayError_tendsto_zero
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : MomentLaw κ D) (Ψ : State D → ℝ)
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (hΨ : Integrable Ψ μ.measure)
    (Y : ∀ n, Fin (n + 1) → Ω n → State D)
    (hm : ∀ n i, Measurable (Y n i)) (hind : ∀ n, iIndepFun (Y n) (P n))
    (hlaw : ∀ n i, Measure.map (Y n i) (P n) = μ.measure) :
    Tendsto (fun n => ∫ ω,
      wasserstein (empiricalLaw κ (Nat.succ_pos n) (fun i => Y n i ω)) μ ∂P n) atTop (𝓝 0) := by
  have hc := integral_sampleError_tendsto_zero (canonicalLaw μ) μ Ψ hdom hsuper hΨ
    (fun i ω => ω i) (fun i => measurable_pi_apply i)
    (fun i j hij => (canonical_independent μ).indepFun hij) (canonical_coordinate_map μ)
  have he (n : ℕ) := integral_error_eq (P n) μ n (Y n) (hm n) (hind n) (hlaw n)
  simp_rw [he]
  exact hc

section Time
variable {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]

/-- The finite-row transport error is jointly measurable for a continuous
target-law curve and jointly measurable particle coordinates. -/
theorem measurable_joint_error {Ω : Type*} [MeasurableSpace Ω]
    (ν : T → MomentLaw κ D) (hν : Continuous ν) (n : ℕ)
    (Y : Fin (n + 1) → T → Ω → State D)
    (hm : ∀ i, Measurable (Function.uncurry (Y i))) :
    Measurable (fun p : T × Ω =>
      wasserstein (empiricalLaw κ (Nat.succ_pos n) (fun i => Y i p.1 p.2)) (ν p.1)) := by
  have hF : Measurable (fun p : T × (Fin (n + 1) → State D) =>
      wasserstein (empiricalLaw κ (Nat.succ_pos n) p.2) (ν p.1)) := by
    apply measurable_from_prod_countable
    intro z
    change Measurable (fun t => dist (empiricalLaw κ (Nat.succ_pos n) z) (ν t))
    have hc : Continuous (fun t : T => dist (empiricalLaw κ (Nat.succ_pos n) z) (ν t)) :=
      (continuous_const : Continuous (fun _ : T => empiricalLaw κ (Nat.succ_pos n) z)).dist hν
    exact hc.measurable
  have hz : Measurable (fun p : T × Ω => (fun i : Fin (n + 1) => Y i p.1 p.2)) :=
    measurable_pi_lambda _ hm
  have hconf := (measurable_fst : Measurable (fun p : T × Ω => p.1)).prodMk hz
  simpa only [Function.comp_def] using hF.comp hconf

/-- Integrated independent empirical error for N-dependent arrays. Both samples
and probability spaces may change with N; independence is required only within
each finite row at each fixed time. The finite-dimensional law transfer proves
pointwise expected-error convergence before time dominated convergence is used. -/
theorem integral_time_arrayError_tendsto_zero
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (τ : Measure T) [IsFiniteMeasure τ]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ν : T → MomentLaw κ D) (hν : Continuous ν) (Ψ : State D → ℝ)
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (hΨ : ∀ t, Integrable Ψ (ν t).measure)
    (C : ℝ) (hbound : ∀ t, (∫ x, Ψ x ∂(ν t).measure) ≤ C)
    (Y : ∀ n, Fin (n + 1) → T → Ω n → State D)
    (hm : ∀ n i, Measurable (Function.uncurry (Y n i)))
    (hind : ∀ n t, iIndepFun (fun i => Y n i t) (P n))
    (hlaw : ∀ n t i, Measure.map (Y n i t) (P n) = (ν t).measure) :
    Tendsto (fun n => ∫ t, (∫ ω,
      wasserstein (empiricalLaw κ (Nat.succ_pos n) (fun i => Y n i t ω)) (ν t) ∂P n) ∂τ)
      atTop (𝓝 0) := by
  have hYm (n : ℕ) (t : T) (i : Fin (n + 1)) : Measurable (Y n i t) :=
    (hm n i).comp (measurable_const.prodMk measurable_id)
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun t => ∫ ω,
      wasserstein (empiricalLaw κ (Nat.succ_pos n) (fun i => Y n i t ω)) (ν t) ∂P n) τ :=
    (measurable_joint_error ν hν n (Y n) (hm n)).stronglyMeasurable.integral_prod_right.aestronglyMeasurable
  have hpoint (t : T) := integral_arrayError_tendsto_zero P (ν t) Ψ hdom hsuper (hΨ t)
    (fun n i => Y n i t) (fun n => hYm n t) (fun n => hind n t) (fun n => hlaw n t)
  have hmajor (n : ℕ) (t : T) :
      ‖∫ ω, wasserstein (empiricalLaw κ (Nat.succ_pos n) (fun i => Y n i t ω)) (ν t) ∂P n‖ ≤ 2 * C := by
    rw [Real.norm_of_nonneg (integral_nonneg (fun ω => wasserstein_nonneg _ _))]
    have hκ : moment (ν t) ≤ ∫ x, Ψ x ∂(ν t).measure := by
      apply integral_mono (ν t).integrable_weight (hΨ t)
      intro x
      linarith [hdom x]
    have he := integral_error_le (P n) (ν t) n (fun i => Y n i t) (hYm n t) (hind n t) (hlaw n t)
    linarith [hbound t]
  have hh := tendsto_integral_of_dominated_convergence (fun _ : T => 2 * C)
    hmeas (integrable_const (2 * C)) (fun n => Eventually.of_forall (hmajor n))
    (Eventually.of_forall hpoint)
  simpa only [integral_zero] using hh

end Time

end CarryingCapacity.EmpiricalArrayError
