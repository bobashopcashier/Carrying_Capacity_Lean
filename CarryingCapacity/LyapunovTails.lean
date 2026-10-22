import CarryingCapacity.Framework
import CarryingCapacity.EmpiricalMeasure

/-!
# Superlinear Lyapunov control and uniform moment tails

The superlinear assumption is used with its actual population-size filter.
It gives uniform integral tail estimates for families of genuine measures whose
Lyapunov integrals are bounded. Finite population sublevels turn population
cutoffs into cutoffs on the generalized moment itself.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace CarryingCapacity.LyapunovTails

variable {D : ℕ} {κ : MomentScale} {Ψ : State D → ℝ}

/-- Population-size sublevels are finite, independently of the moment scale. -/
theorem finite_population_sublevel (R : ℝ) :
    {x : State D | populationSize x ≤ R}.Finite := by
  simpa [momentWeight, populationSize, MomentScale.linear] using
    (finite_moment_sublevel (D := D) MomentScale.linear R)

/-- The superlinear ratio gives a uniform pointwise estimate outside a natural cutoff. -/
theorem exists_population_cutoff
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ x : State D, (K : ℝ) < populationSize x →
      1 + momentWeight κ x ≤ ε * Ψ x := by
  have hevent := hsuper.eventually (eventually_ge_atTop ε⁻¹)
  rw [eventually_comap, eventually_atTop] at hevent
  obtain ⟨R, hR⟩ := hevent
  refine ⟨Nat.ceil R, ?_⟩
  intro x hx
  have hratio := hR (populationSize x) ((Nat.le_ceil R).trans hx.le) x rfl
  have hden : 0 < 1 + momentWeight κ x := by
    linarith [momentWeight_nonneg κ x]
  have hmul := mul_le_mul_of_nonneg_left ((le_div_iff₀ hden).mp hratio) hε.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul] using hmul

/-- The weight retained only outside a population-size cutoff. -/
def populationTail (κ : MomentScale) (K : ℕ) (x : State D) : ℝ :=
  {y : State D | (K : ℝ) < populationSize y}.indicator
    (fun y => 1 + momentWeight κ y) x

theorem populationTail_nonneg (K : ℕ) (x : State D) :
    0 ≤ populationTail κ K x := by
  by_cases hx : (K : ℝ) < populationSize x
  · simp [populationTail, hx, add_nonneg zero_le_one (momentWeight_nonneg κ x)]
  · simp [populationTail, hx]

/-- This is the pointwise indicator estimate needed before integrating a tail. -/
theorem exists_populationTail_le
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ L : ℕ, K ≤ L → ∀ x, populationTail κ L x ≤ ε * Ψ x := by
  obtain ⟨K, hK⟩ := exists_population_cutoff hsuper hε
  refine ⟨K, ?_⟩
  intro L hKL x
  have hΨ : 0 ≤ Ψ x := (by linarith [momentWeight_nonneg κ x, hdom x])
  by_cases hx : (L : ℝ) < populationSize x
  · simpa [populationTail, hx] using
      hK x (lt_of_le_of_lt (by exact_mod_cast hKL) hx)
  · simp [populationTail, hx, mul_nonneg hε.le hΨ]

/-- A Lyapunov-integrable measure also integrates the moment tail. -/
theorem integrable_populationTail (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (μ : Measure (State D)) (hΨ : Integrable Ψ μ) (K : ℕ) :
    Integrable (populationTail κ K) μ := by
  apply hΨ.mono' (measurable_of_countable _).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (populationTail_nonneg K x)]
    by_cases hx : (K : ℝ) < populationSize x
    · simpa [populationTail, hx] using hdom x
    · have hnonneg : 0 ≤ Ψ x := by linarith [momentWeight_nonneg κ x, hdom x]
      simpa [populationTail, hx] using hnonneg

/-- Pointwise tail control integrates against the actual measure. -/
theorem integral_populationTail_le (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (μ : Measure (State D)) (hΨ : Integrable Ψ μ)
    (K : ℕ) (ε : ℝ) (hbound : ∀ x, populationTail κ K x ≤ ε * Ψ x) :
    (∫ x, populationTail κ K x ∂μ) ≤ ε * ∫ x, Ψ x ∂μ := by
  calc
    (∫ x, populationTail κ K x ∂μ) ≤ ∫ x, ε * Ψ x ∂μ :=
      integral_mono (integrable_populationTail hdom μ hΨ K) (hΨ.const_mul ε) hbound
    _ = ε * ∫ x, Ψ x ∂μ := integral_const_mul ε Ψ

/-- Uniform Lyapunov-integral bounds give uniform moment tails. No common
underlying probability space is required; the measures themselves may vary. -/
theorem uniform_population_integral_tails {I : Type*}
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (μ : I → Measure (State D)) (hΨ : ∀ i, Integrable Ψ (μ i))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ i, (∫ x, Ψ x ∂μ i) ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ L : ℕ, K ≤ L → ∀ i,
      (∫ x, populationTail κ L x ∂μ i) < ε := by
  have hδ : 0 < ε / (C + 1) := div_pos hε (by linarith)
  obtain ⟨K, hK⟩ := exists_populationTail_le hdom hsuper hδ
  refine ⟨K, ?_⟩
  intro L hKL i
  calc
    (∫ x, populationTail κ L x ∂μ i) ≤ ε / (C + 1) * ∫ x, Ψ x ∂μ i :=
      integral_populationTail_le hdom (μ i) (hΨ i) L _ (hK L hKL)
    _ ≤ ε / (C + 1) * C := mul_le_mul_of_nonneg_left (hbound i) hδ.le
    _ < ε := by
      rw [div_mul_eq_mul_div]
      exact (div_lt_iff₀ (by linarith : 0 < C + 1)).mpr (by nlinarith)

/-- Finite population sublevels convert the superlinear estimate into a
threshold on the moment weight itself. This is the uniform-integrability cutoff. -/
theorem exists_weight_cutoff
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : State D, B ≤ 1 + momentWeight κ x →
      1 + momentWeight κ x ≤ ε * Ψ x := by
  obtain ⟨K, hK⟩ := exists_population_cutoff hsuper hε
  obtain ⟨A, hA⟩ := ((finite_population_sublevel (D := D) K).image
    (fun x => 1 + momentWeight κ x)).bddAbove
  refine ⟨max A 0 + 1, by positivity, ?_⟩
  intro x hx
  apply hK x
  by_contra hnot
  have hm := hA (Set.mem_image_of_mem _ (le_of_not_gt hnot))
  have hmax : A ≤ max A 0 := le_max_left _ _
  linarith

/-- A global affine bound is available with an arbitrarily small Lyapunov coefficient. -/
theorem exists_affine_weight_bound
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, momentWeight κ x ≤ B + δ * Ψ x := by
  obtain ⟨B, hB, htail⟩ := exists_weight_cutoff hsuper hδ
  refine ⟨B, hB, ?_⟩
  intro x
  by_cases hx : B ≤ 1 + momentWeight κ x
  · have h := htail x hx
    linarith
  · have hnonneg : 0 ≤ Ψ x := by linarith [hdom x, momentWeight_nonneg κ x]
    have hprod := mul_nonneg hδ.le hnonneg
    linarith

/-- Averaging preserves an affine bound, with no assumptions on individual coordinates. -/
theorem empiricalMean_le_constant_add {α : Type*} {N : ℕ} (hN : 0 < N)
    (f ψ : α → ℝ) (B δ : ℝ) (z : Fin N → α)
    (hbound : ∀ x, f x ≤ B + δ * ψ x) :
    FiniteGenerator.empiricalMean f z ≤ B + δ * FiniteGenerator.empiricalMean ψ z := by
  classical
  unfold FiniteGenerator.empiricalMean
  calc
    (N : ℝ)⁻¹ * ∑ i, f (z i) ≤ (N : ℝ)⁻¹ * ∑ i, (B + δ * ψ (z i)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hbound (z i))
        (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ = B + δ * ((N : ℝ)⁻¹ * ∑ i, ψ (z i)) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      field_simp [hNr]
      ring

section RandomVariables

variable {Ω I : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- A nonnegative integrable function has first Lp seminorm equal to its integral. -/
theorem eLpNorm_one_eq_ofReal_integral {f : Ω → ℝ}
    (hf : Integrable f P) (hnonneg : ∀ ω, 0 ≤ f ω) :
    eLpNorm f 1 P = ENNReal.ofReal (∫ ω, f ω ∂P) := by
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hf]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => Real.norm_of_nonneg (hnonneg ω))

variable [IsFiniteMeasure P]

/-- Uniformly bounded expected envelopes suffice for uniform integrability.
The envelope coefficient must be arbitrarily small; the additive bound may depend
on that coefficient. Neither independence nor per-coordinate moment bounds occur. -/
theorem uniformIntegrable_of_affine_envelope
    (g G : I → Ω → ℝ) (hg : ∀ i, AEStronglyMeasurable (g i) P)
    (hG : ∀ i, Integrable (G i) P) (hGnonneg : ∀ i ω, 0 ≤ G i ω)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ i, (∫ ω, G i ω ∂P) ≤ C)
    (henvelope : ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 0 ≤ B ∧
      ∀ i ω, ‖g i ω‖ ≤ B + δ * G i ω) :
    UniformIntegrable g 1 P := by
  apply uniformIntegrable_of (by norm_num) (by norm_num) hg
  intro ε hε
  have hδ : 0 < ε / (C + 1) := div_pos hε (by linarith)
  obtain ⟨B, hB, henv⟩ := henvelope (ε / (C + 1) / 2) (half_pos hδ)
  have hcutoff : 0 ≤ 2 * B + 1 := by linarith
  refine ⟨⟨2 * B + 1, hcutoff⟩, ?_⟩
  intro i
  have htail : ∀ ω,
      ‖{ω | (⟨2 * B + 1, hcutoff⟩ : ℝ≥0) ≤ ‖g i ω‖₊}.indicator (g i) ω‖ ≤
        ε / (C + 1) * G i ω := by
    intro ω
    by_cases hω : (⟨2 * B + 1, hcutoff⟩ : ℝ≥0) ≤ ‖g i ω‖₊
    · simp only [Set.indicator_apply, Set.mem_setOf_eq, if_pos hω]
      have hnorm : 2 * B + 1 ≤ ‖g i ω‖ := by exact_mod_cast hω
      have henvω := henv i ω
      nlinarith
    · simp only [Set.indicator_apply, Set.mem_setOf_eq, if_neg hω, norm_zero]
      exact mul_nonneg hδ.le (hGnonneg i ω)
  calc
    eLpNorm ({ω | (⟨2 * B + 1, hcutoff⟩ : ℝ≥0) ≤ ‖g i ω‖₊}.indicator (g i)) 1 P ≤
        eLpNorm (fun ω => ε / (C + 1) * G i ω) 1 P := eLpNorm_mono_real htail
    _ = ENNReal.ofReal (ε / (C + 1) * ∫ ω, G i ω ∂P) := by
      rw [eLpNorm_one_eq_ofReal_integral P ((hG i).const_mul _)
        (fun ω => mul_nonneg hδ.le (hGnonneg i ω)), integral_const_mul]
    _ ≤ ENNReal.ofReal ε := by
      apply ENNReal.ofReal_le_ofReal
      calc
        ε / (C + 1) * (∫ ω, G i ω ∂P) ≤ ε / (C + 1) * C :=
          mul_le_mul_of_nonneg_left (hbound i) hδ.le
        _ ≤ ε := by
          rw [div_mul_eq_mul_div]
          apply (div_le_iff₀ (by linarith : 0 < C + 1)).mpr
          nlinarith

/-- Expected absolute errors vanish under genuine uniform integrability and
convergence in measure. This is the measure-theoretic Vitali step. -/
theorem integral_abs_tendsto_zero_of_uniformIntegrable (g : ℕ → Ω → ℝ)
    (hui : UniformIntegrable g 1 P) (hconv : TendstoInMeasure P g atTop 0) :
    Tendsto (fun n => ∫ ω, |g n ω| ∂P) atTop (𝓝 0) := by
  have hlp := tendsto_Lp_finite_of_tendstoInMeasure (by norm_num : (1 : ℝ≥0∞) ≤ 1)
    (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hui.aestronglyMeasurable
    (MemLp.zero : MemLp (0 : Ω → ℝ) 1 P) hui.unifIntegrable hconv
  have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hlp
  convert hreal using 1
  funext n
  simp only [Function.comp_apply, sub_zero, eLpNorm_one_eq_lintegral_enorm]
  simpa only [Real.norm_eq_abs] using integral_norm_eq_lintegral_enorm (hui.aestronglyMeasurable n)

/-- The Lyapunov condition yields mathlib's actual uniform-integrability property
for every measurable real family dominated by the generalized state weight.
The random states need no independence or identical-distribution assumption. -/
theorem uniformIntegrable_of_weight_domination
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (X : I → Ω → State D) (g : I → Ω → ℝ)
    (hg : ∀ i, AEStronglyMeasurable (g i) P)
    (hweight : ∀ i ω, ‖g i ω‖ ≤ 1 + momentWeight κ (X i ω))
    (hΨ : ∀ i, Integrable (fun ω => Ψ (X i ω)) P)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ i, (∫ ω, Ψ (X i ω) ∂P) ≤ C) :
    UniformIntegrable g 1 P := by
  apply uniformIntegrable_of (by norm_num) (by norm_num) hg
  intro ε hε
  have hδ : 0 < ε / (C + 1) := div_pos hε (by linarith)
  obtain ⟨B, hBnonneg, hB⟩ := exists_weight_cutoff hsuper hδ
  refine ⟨⟨B, hBnonneg⟩, ?_⟩
  intro i
  have hΨnonneg : ∀ ω, 0 ≤ Ψ (X i ω) := by
    intro ω
    linarith [momentWeight_nonneg κ (X i ω), hdom (X i ω)]
  have htail : ∀ ω,
      ‖{ω | (⟨B, hBnonneg⟩ : ℝ≥0) ≤ ‖g i ω‖₊}.indicator (g i) ω‖ ≤
        ε / (C + 1) * Ψ (X i ω) := by
    intro ω
    by_cases hω : (⟨B, hBnonneg⟩ : ℝ≥0) ≤ ‖g i ω‖₊
    · simp only [Set.indicator_apply, Set.mem_setOf_eq, if_pos hω]
      apply (hweight i ω).trans (hB (X i ω) ?_)
      have hnorm : B ≤ ‖g i ω‖ := by exact_mod_cast hω
      exact hnorm.trans (hweight i ω)
    · simp only [Set.indicator_apply, Set.mem_setOf_eq, if_neg hω, norm_zero]
      exact mul_nonneg hδ.le (hΨnonneg ω)
  calc
    eLpNorm ({ω | (⟨B, hBnonneg⟩ : ℝ≥0) ≤ ‖g i ω‖₊}.indicator (g i)) 1 P ≤
        eLpNorm (fun ω => ε / (C + 1) * Ψ (X i ω)) 1 P :=
      eLpNorm_mono_real htail
    _ = ENNReal.ofReal (ε / (C + 1) * ∫ ω, Ψ (X i ω) ∂P) := by
      rw [eLpNorm_one_eq_ofReal_integral P ((hΨ i).const_mul _)
        (fun ω => mul_nonneg hδ.le (hΨnonneg ω)), integral_const_mul]
    _ ≤ ENNReal.ofReal ε := by
      apply ENNReal.ofReal_le_ofReal
      calc
        ε / (C + 1) * (∫ ω, Ψ (X i ω) ∂P) ≤ ε / (C + 1) * C :=
          mul_le_mul_of_nonneg_left (hbound i) hδ.le
        _ ≤ ε := by
          rw [div_mul_eq_mul_div]
          apply (div_le_iff₀ (by linarith : 0 < C + 1)).mpr
          nlinarith

/-- Convergence in probability of weight-dominated errors upgrades to convergence
of their actual expected absolute values. Uniform integrability is derived from
the superlinear Lyapunov hypothesis, rather than assumed. -/
theorem integral_abs_tendsto_zero_of_inMeasure
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (X : ℕ → Ω → State D) (g : ℕ → Ω → ℝ)
    (hg : ∀ n, AEStronglyMeasurable (g n) P)
    (hweight : ∀ n ω, ‖g n ω‖ ≤ 1 + momentWeight κ (X n ω))
    (hΨ : ∀ n, Integrable (fun ω => Ψ (X n ω)) P)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, (∫ ω, Ψ (X n ω) ∂P) ≤ C)
    (hconv : TendstoInMeasure P g atTop 0) :
    Tendsto (fun n => ∫ ω, |g n ω| ∂P) atTop (𝓝 0) := by
  have hui := uniformIntegrable_of_weight_domination P hdom hsuper X g hg hweight hΨ C hC hbound
  have hlp := tendsto_Lp_finite_of_tendstoInMeasure (by norm_num : (1 : ℝ≥0∞) ≤ 1)
    (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hg (MemLp.zero : MemLp (0 : Ω → ℝ) 1 P)
    hui.unifIntegrable hconv
  have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hlp
  convert hreal using 1
  funext n
  simp only [Function.comp_apply, sub_zero, eLpNorm_one_eq_lintegral_enorm]
  simpa only [Real.norm_eq_abs] using integral_norm_eq_lintegral_enorm (hg n)

/-- Empirical moment errors are uniformly integrable under the manuscript's
expected-average Lyapunov bound. No bound on each coordinate separately is assumed. -/
theorem uniformIntegrable_empirical_errors
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (X : ∀ i, Ω → Fin (N i) → State D)
    (g : I → Ω → ℝ) (hg : ∀ i, AEStronglyMeasurable (g i) P)
    (M : ℝ) (hM : 0 ≤ M)
    (herror : ∀ i ω, ‖g i ω‖ ≤ M + FiniteGenerator.empiricalMean (momentWeight κ) (X i ω))
    (hΨ : ∀ i, Integrable (fun ω => FiniteGenerator.empiricalMean Ψ (X i ω)) P)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ i, (∫ ω, FiniteGenerator.empiricalMean Ψ (X i ω) ∂P) ≤ C) :
    UniformIntegrable g 1 P := by
  apply uniformIntegrable_of_affine_envelope P g
    (fun i ω => FiniteGenerator.empiricalMean Ψ (X i ω)) hg hΨ _ C hC hbound
  · intro δ hδ
    obtain ⟨B, hB, hweight⟩ := exists_affine_weight_bound hdom hsuper hδ
    refine ⟨M + B, add_nonneg hM hB, ?_⟩
    intro i ω
    have havg := empiricalMean_le_constant_add (hN i) (momentWeight κ) Ψ B δ (X i ω) hweight
    linarith [herror i ω]
  · intro i ω
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg (N i)))
    apply Finset.sum_nonneg
    intro j _
    linarith [hdom (X i ω j), momentWeight_nonneg κ (X i ω j)]

/-- The actual empirical transport error is uniformly integrable under bounded
expected empirical Lyapunov averages, for any fixed finite-moment target law. -/
theorem uniformIntegrable_empirical_transport
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (X : ∀ i, Ω → Fin (N i) → State D)
    (μ : MomentLaw κ D)
    (hmeas : ∀ i, AEStronglyMeasurable
      (fun ω => wasserstein (empiricalLaw κ (hN i) (X i ω)) μ) P)
    (hΨ : ∀ i, Integrable (fun ω => FiniteGenerator.empiricalMean Ψ (X i ω)) P)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ i, (∫ ω, FiniteGenerator.empiricalMean Ψ (X i ω) ∂P) ≤ C) :
    UniformIntegrable (fun i ω => wasserstein (empiricalLaw κ (hN i) (X i ω)) μ) 1 P := by
  apply uniformIntegrable_empirical_errors P hdom hsuper N hN X _ hmeas
    (moment μ) (moment_nonneg μ) _ hΨ C hC hbound
  intro i ω
  rw [Real.norm_eq_abs, abs_of_nonneg (wasserstein_nonneg _ _)]
  have h := wasserstein_le_moments (empiricalLaw κ (hN i) (X i ω)) μ
  rw [moment_empiricalLaw] at h
  linarith

/-- Initial empirical transport convergence in probability upgrades to expected
transport convergence under exactly an expected empirical Lyapunov bound.
The probability convergence is an input, not an asserted law of large numbers. -/
theorem integral_empirical_transport_tendsto_zero
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) (X : ∀ n, Ω → Fin (N n) → State D)
    (μ : MomentLaw κ D)
    (hmeas : ∀ n, AEStronglyMeasurable
      (fun ω => wasserstein (empiricalLaw κ (hN n) (X n ω)) μ) P)
    (hΨ : ∀ n, Integrable (fun ω => FiniteGenerator.empiricalMean Ψ (X n ω)) P)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n, (∫ ω, FiniteGenerator.empiricalMean Ψ (X n ω) ∂P) ≤ C)
    (hconv : TendstoInMeasure P
      (fun n ω => wasserstein (empiricalLaw κ (hN n) (X n ω)) μ) atTop 0) :
    Tendsto (fun n => ∫ ω, wasserstein (empiricalLaw κ (hN n) (X n ω)) μ ∂P)
      atTop (𝓝 0) := by
  have hui := uniformIntegrable_empirical_transport P hdom hsuper N hN X μ hmeas hΨ C hC hbound
  have h := integral_abs_tendsto_zero_of_uniformIntegrable P _ hui hconv
  simpa only [abs_of_nonneg (wasserstein_nonneg _ _)] using h

end RandomVariables

end CarryingCapacity.LyapunovTails
