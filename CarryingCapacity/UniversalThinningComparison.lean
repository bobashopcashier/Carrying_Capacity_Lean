import CarryingCapacity.UniversalFrozenNoise
import CarryingCapacity.FiniteHorizonCountingUniqueness

/-!
# Arbitrary finite-state solutions compared on the same actual noise

The coefficients and proposed paths are quantified after one full noise event.
Their separate coordinate thinning equations, genuine left limits, and a local
finite-state rate bound identify each path with its actual frozen recursion.
The paired positive-increment inequality is consequently derived from those
separate equations, rather than assumed for the pair.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology ENNReal

namespace CarryingCapacity.UniversalThinningComparison
open MarkedNoise ChronologicalEvents TimeDependentFrozenProcess TimeDependentJumpIdentity
  FiniteHorizonCountingUniqueness

variable {E J I : Type*} [DecidableEq E] [Fintype J]
  [TopologicalSpace E] [DiscreteTopology E]

/-- An auxiliary threshold: outside the active set it lies strictly below
all actual nonnegative marks. It is used only to invoke deterministic
coordinate-equation uniqueness, and is not asserted to be a jump rate. -/
def cappedThreshold (G : Finset E) (rate : J → ℝ → E → ℝ) (C : ℝ)
    (j : J) (t : ℝ) (x : E) : ℝ := if x ∈ G then min C (rate j t x) else -1

omit [TopologicalSpace E] [DiscreteTopology E] [Fintype J] in
theorem increment_eq_capped (G : Finset E) (jump : J → E → E)
    (rate : J → ℝ → E → ℝ) (C : ℝ) (x : E) (ω : Sample J)
    (f : E → ℝ) (j : J) (T : ℝ) (z : ℝ × ℝ) (hz : 0 ≤ z.2) :
    UniversalFrozenNoise.increment G jump rate C x ω f j T z =
      TimeDependentEquationUniqueness.increment jump (cappedThreshold G rate C)
        (leftProcess G jump rate C x ω) f j T z := by
  unfold UniversalFrozenNoise.increment TimeDependentEquationUniqueness.increment cappedThreshold
  by_cases hG : leftProcess G jump rate C x ω z.1 ∈ G
  · simp only [hG, if_true, true_and, le_min_iff, and_assoc]
  · have hn : ¬ z.2 ≤ -1 := by linarith
    simp only [hG, if_false, false_and, and_false, hn]

/-- Arbitrary coefficients and proposed solutions share a single noise event.
Only the finite separating family of actual coordinate equations is needed. -/
theorem ae_candidate_eq_frozen (test : I → E → ℝ)
    (hsep : ∀ x y : E, (∀ i, test i x = test i y) → x = y) :
    ∀ᵐ ω ∂law J, ∀ (G : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)
      (C T : ℝ) (X pre : ℝ → E),
      (∀ t ∈ Ico 0 T, ContinuousWithinAt X (Ici t) t) →
      (∀ t ∈ Ioc 0 T, Tendsto X (𝓝[<] t) (𝓝 (pre t))) →
      (∀ t ∈ Ioc 0 T, pre t ∈ G) →
      (∀ t ∈ Ioc 0 T, ∀ j, rate j t (pre t) ≤ C) →
      (∀ i t, t ∈ Icc 0 T → test i (X t) - test i (X 0) =
        ∑ j : J, ∫ z, TimeDependentEquationUniqueness.increment jump rate pre
          (test i) j t z ∂countingMeasure j ω) →
      EqOn X (process G jump rate C (X 0) ω) (Icc 0 T) := by
  filter_upwards [UniversalFrozenNoise.ae_counting_identity (E := E) (J := J),
    UniversalFrozenNoise.ae_zero (E := E) (J := J),
    UniversalFrozenNoise.ae_right_continuous (E := E) (J := J),
    UniversalFrozenNoise.ae_tendsto_left (E := E) (J := J),
    MarkedNoise.ae_positive_points (J := J)] with ω heq hzero hright hleft hheight
  intro G jump rate C T X pre hX hpre hG hC hEq
  apply eqOn_of_separating_counting_equations test hsep jump (cappedThreshold G rate C)
    (fun j => countingMeasure j ω) X (process G jump rate C (X 0) ω)
    pre (leftProcess G jump rate C (X 0) ω) T hX
    (fun t _ => hright G jump rate C (X 0) t) hpre
    (fun t _ => hleft G jump rate C (X 0) t) (hzero G jump rate C (X 0)).symm
  · intro i t ht
    rw [hEq i t ht]
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => by
      by_cases hz : z.1 ∈ Ioc 0 t
      · have hzT : z.1 ∈ Ioc 0 T := ⟨hz.1,hz.2.trans ht.2⟩
        simp only [TimeDependentEquationUniqueness.increment, hz, true_and,
          cappedThreshold, hG z.1 hzT, if_true, min_eq_right (hC z.1 hzT j)]
      · simp only [TimeDependentEquationUniqueness.increment, hz, false_and, if_false])
  · intro i t _
    rw [hzero G jump rate C (X 0), heq G jump rate C (X 0) t (test i)]
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    change ∀ᵐ z ∂Measure.sum (fun n => Measure.dirac (point j ω n)), _
    rw [Measure.ae_sum_iff]
    intro n
    rw [ae_dirac_eq]
    exact increment_eq_capped G jump rate C (X 0) ω (test i) j t (point j ω n) (hheight j n).2

omit [DecidableEq E] [Fintype J] [DiscreteTopology E] in
/-- Equality of paths on a finite interval identifies all genuine left states
through its terminal time. -/
theorem left_eq_of_eqOn [T2Space E] (X Y preX preY : ℝ → E) (T : ℝ)
    (hX : ∀ t ∈ Ioc 0 T, Tendsto X (𝓝[<] t) (𝓝 (preX t)))
    (hY : ∀ t ∈ Ioc 0 T, Tendsto Y (𝓝[<] t) (𝓝 (preY t)))
    (heq : EqOn X Y (Icc 0 T)) : EqOn preX preY (Ioc 0 T) := by
  intro t ht
  apply tendsto_nhds_unique (hX t ht)
  apply (hY t ht).congr'
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ht.1)] with s hs hs0
  exact (heq ⟨hs0.le,hs.le.trans ht.2⟩).symm

/-- The positive increment field of arbitrary candidate paths, on an actual
finite box. It uses the candidates' own genuine left states. -/
def positiveBox (jump : J → E → E) (rateX rateY : J → ℝ → E → ℝ)
    (preX preY : ℝ → E) (ρ : E → E → ℝ) (C T : ℝ) (j : J) (z : ℝ × ℝ) : ℝ :=
  (Ioc 0 T ×ˢ Iic C).indicator (fun z => SynchronousPositiveIncrement.positiveIncrement
    ρ jump j (rateX j z.1 (preX z.1)) (rateY j z.1 (preY z.1)) (preX z.1) (preY z.1) z.2) z

/-- The actual paired terminal comparison follows from the two separate
coordinate equations. The rates may be chosen from the same random sample. -/
theorem ae_distance_le_positiveBox (test : I → E → ℝ)
    (hsep : ∀ x y : E, (∀ i, test i x = test i y) → x = y) :
    ∀ᵐ ω ∂law J, ∀ (G H : Finset E) (jump : J → E → E)
      (rateX rateY : J → ℝ → E → ℝ) (C T : ℝ) (X Y preX preY : ℝ → E)
      (ρ : E → E → ℝ), 0 ≤ T →
      (∀ t ∈ Ico 0 T, ContinuousWithinAt X (Ici t) t) →
      (∀ t ∈ Ico 0 T, ContinuousWithinAt Y (Ici t) t) →
      (∀ t ∈ Ioc 0 T, Tendsto X (𝓝[<] t) (𝓝 (preX t))) →
      (∀ t ∈ Ioc 0 T, Tendsto Y (𝓝[<] t) (𝓝 (preY t))) →
      (∀ t ∈ Ioc 0 T, preX t ∈ G) →
      (∀ t ∈ Ioc 0 T, preY t ∈ H) →
      (∀ t ∈ Ioc 0 T, ∀ j, rateX j t (preX t) ≤ C) →
      (∀ t ∈ Ioc 0 T, ∀ j, rateY j t (preY t) ≤ C) →
      (∀ i t, t ∈ Icc 0 T → test i (X t) - test i (X 0) =
        ∑ j : J, ∫ z, TimeDependentEquationUniqueness.increment jump rateX preX
          (test i) j t z ∂countingMeasure j ω) →
      (∀ i t, t ∈ Icc 0 T → test i (Y t) - test i (Y 0) =
        ∑ j : J, ∫ z, TimeDependentEquationUniqueness.increment jump rateY preY
          (test i) j t z ∂countingMeasure j ω) →
      ρ (X T) (Y T) ≤ ρ (X 0) (Y 0) + ∑ j : J, ∫ z,
        positiveBox jump rateX rateY preX preY ρ C T j z ∂countingMeasure j ω := by
  filter_upwards [ae_candidate_eq_frozen (J := J) test hsep,
    UniversalFrozenNoise.ae_paired_distance_le_integral (E := E) (J := J),
    UniversalFrozenNoise.ae_tendsto_left (E := E) (J := J),
    MarkedNoise.ae_positive_points (J := J)] with ω heq hpair hleft hpos
  intro G H jump rateX rateY C T X Y preX preY ρ hT hX hY hx hy hG hH hCX hCY heqX heqY
  have hxeq := heq G jump rateX C T X preX hX hx hG hCX heqX
  have hyeq := heq H jump rateY C T Y preY hY hy hH hCY heqY
  have hxp := left_eq_of_eqOn X (process G jump rateX C (X 0) ω) preX
    (leftProcess G jump rateX C (X 0) ω) T hx (fun t _ => hleft G jump rateX C (X 0) t) hxeq
  have hyp := left_eq_of_eqOn Y (process H jump rateY C (Y 0) ω) preY
    (leftProcess H jump rateY C (Y 0) ω) T hy (fun t _ => hleft H jump rateY C (Y 0) t) hyeq
  rw [hxeq ⟨hT,le_rfl⟩,hyeq ⟨hT,le_rfl⟩]
  have hp := hpair G H jump rateX rateY ρ C (X 0) (Y 0) T
    (fun t ht => (hxp ht) ▸ hG t ht) (fun t ht => (hyp ht) ▸ hH t ht)
  refine hp.trans_eq ?_
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  change ∀ᵐ z ∂Measure.sum (fun n => Measure.dirac (point j ω n)), _
  rw [Measure.ae_sum_iff]
  intro n
  rw [ae_dirac_eq]
  change SynchronousFrozenCounting.boxField G H jump rateX rateY ρ C (X 0) (Y 0) ω j T (point j ω n) =
    positiveBox jump rateX rateY preX preY ρ C T j (point j ω n)
  have hz : 0 < (point j ω n).1 := (hpos j n).1
  by_cases ht : (point j ω n).1 ∈ Ioc 0 T
  · simp only [SynchronousFrozenCounting.boxField, SynchronousFrozenCounting.field,
      positiveBox, Set.indicator_apply, mem_prod, mem_Iic, ht, true_and,
      ht.2, ← hxp ht, ← hyp ht]
  · have hn : ¬ (point j ω n).1 ≤ T := fun h => ht ⟨hz,h⟩
    simp only [SynchronousFrozenCounting.boxField, positiveBox, Set.indicator_apply,
      mem_prod, mem_Iic, hn, ht, false_and, if_false]

end CarryingCapacity.UniversalThinningComparison
