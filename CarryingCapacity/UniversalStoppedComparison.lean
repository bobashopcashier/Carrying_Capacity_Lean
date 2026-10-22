import CarryingCapacity.UniversalThinningComparison
import CarryingCapacity.SynchronousStoppedRunningSupremum
import CarryingCapacity.CadlagCompactBounds

/-!
# Arbitrary candidate equations imply a stopped running-supremum bound

This is a pathwise assertion on one universal full-noise event. All paths,
coefficients, finite active sets, and stopping horizons are chosen afterward.
The conclusion is derived from the two separate coordinate equations. It
keeps the atom at the stopping time and then removes the auxiliary height
cutoff by monotonicity, without a stochastic comparison hypothesis.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical Topology ENNReal BigOperators NNReal

namespace CarryingCapacity.UniversalStoppedComparison
open MarkedNoise UniversalThinningComparison SynchronousPositiveIncrement
  SynchronousRunningSupremum SynchronousStoppedRunningSupremum CommonFrozenExit

variable {E J I : Type*} [DecidableEq E] [Fintype J]
  [TopologicalSpace E] [DiscreteTopology E]

/-- The original positive thinning field, with an inclusive common stop and
no rate-height cutoff. -/
def stoppedField (jump : J → E → E) (rateX rateY : J → ℝ → E → ℝ)
    (preX preY : ℝ → E) (ρ : E → E → ℝ) (σ : ℝ≥0∞) (T : ℝ) (j : J)
    (z : ℝ × ℝ) : ℝ≥0∞ :=
  if z.1 ∈ Ioc 0 T ∧ ENNReal.ofReal z.1 ≤ σ then
    ENNReal.ofReal (positiveIncrement ρ jump j (rateX j z.1 (preX z.1))
      (rateY j z.1 (preY z.1)) (preX z.1) (preY z.1) z.2)
  else 0

omit [TopologicalSpace E] [DiscreteTopology E] [DecidableEq E] [Fintype J] in
theorem positiveBox_nonnegative (jump : J → E → E) (rateX rateY : J → ℝ → E → ℝ)
    (preX preY : ℝ → E) (ρ : E → E → ℝ) (C T : ℝ) (j : J) (z : ℝ × ℝ) :
    0 ≤ positiveBox jump rateX rateY preX preY ρ C T j z :=
  Set.indicator_nonneg (fun _ _ => positiveIncrement_nonnegative _ _ _ _ _ _ _ _) _

omit [DecidableEq E] [TopologicalSpace E] [DiscreteTopology E] in
/-- Local finiteness of the actual measure makes every finite-box positive
increment integrable, uniformly over all later coefficient/path choices. -/
theorem ae_integrable_positiveBox : ∀ᵐ ω ∂law J,
    ∀ (jump : J → E → E) (rateX rateY : J → ℝ → E → ℝ)
      (preX preY : ℝ → E) (ρ : E → E → ℝ) (C T : ℝ) (j : J),
      Integrable (positiveBox jump rateX rateY preX preY ρ C T j) (countingMeasure j ω) := by
  filter_upwards [FrozenCountingIdentity.ae_integrable_box_weights (J := J)] with ω hω
  intro jump rateX rateY preX preY ρ C T j
  convert hω T C j (positiveBox jump rateX rateY preX preY ρ C T j) using 1
  funext z
  by_cases hz : z ∈ Iic T ×ˢ Iic C
  · exact (Set.indicator_of_mem hz _).symm
  · have hout : z ∉ Ioc 0 T ×ˢ Iic C := fun h => hz ⟨h.1.2,h.2⟩
    simp only [Set.indicator_of_not_mem hz, positiveBox, Set.indicator_of_not_mem hout]

/-- The stopped running cost through every real observation time follows from
the separate thinning equations through the actual cut horizon. -/
theorem ae_stopped_sup_le (test : I → E → ℝ)
    (hsep : ∀ x y : E, (∀ i, test i x = test i y) → x = y) :
    ∀ᵐ ω ∂law J, ∀ (G H : Finset E) (jump : J → E → E)
      (rateX rateY : J → ℝ → E → ℝ) (C : ℝ) (σ : ℝ≥0∞) (T : ℝ≥0)
      (X Y preX preY : ℝ → E) (ρ : E → E → ℝ),
      (∀ x y, 0 ≤ ρ x y) →
      (∀ t ∈ Ico 0 (cutHorizon σ T : ℝ), ContinuousWithinAt X (Ici t) t) →
      (∀ t ∈ Ico 0 (cutHorizon σ T : ℝ), ContinuousWithinAt Y (Ici t) t) →
      (∀ t ∈ Ioc 0 (cutHorizon σ T : ℝ), Tendsto X (𝓝[<] t) (𝓝 (preX t))) →
      (∀ t ∈ Ioc 0 (cutHorizon σ T : ℝ), Tendsto Y (𝓝[<] t) (𝓝 (preY t))) →
      (∀ t ∈ Ioc 0 (cutHorizon σ T : ℝ), preX t ∈ G) →
      (∀ t ∈ Ioc 0 (cutHorizon σ T : ℝ), preY t ∈ H) →
      (∀ t ∈ Ioc 0 (cutHorizon σ T : ℝ), ∀ j, rateX j t (preX t) ≤ C) →
      (∀ t ∈ Ioc 0 (cutHorizon σ T : ℝ), ∀ j, rateY j t (preY t) ≤ C) →
      (∀ i t, t ∈ Icc 0 (cutHorizon σ T : ℝ) → test i (X t) - test i (X 0) =
        ∑ j : J, ∫ z, TimeDependentEquationUniqueness.increment jump rateX preX
          (test i) j t z ∂countingMeasure j ω) →
      (∀ i t, t ∈ Icc 0 (cutHorizon σ T : ℝ) → test i (Y t) - test i (Y 0) =
        ∑ j : J, ∫ z, TimeDependentEquationUniqueness.increment jump rateY preY
          (test i) j t z ∂countingMeasure j ω) →
      intervalSup (stopped σ (fun t => ENNReal.ofReal (ρ (X t) (Y t)))) T ≤
        ENNReal.ofReal (ρ (X 0) (Y 0)) + ∑ j : J, ∫⁻ z,
          stoppedField jump rateX rateY preX preY ρ σ T j z ∂countingMeasure j ω := by
  filter_upwards [ae_distance_le_positiveBox (J := J) test hsep,
    ae_integrable_positiveBox (E := E) (J := J)] with ω hpair hi
  intro G H jump rateX rateY C σ T X Y preX preY ρ hρ hX hY hx hy hG hH hCX hCY heqX heqY
  rw [intervalSup_stopped]
  apply iSup_le
  intro s
  have hcut : (s : ℝ) ≤ cutHorizon σ T := s.2.2
  have hs : 0 ≤ (s : ℝ) := s.2.1
  have h := hpair G H jump rateX rateY C s X Y preX preY ρ hs
    (fun t ht => hX t ⟨ht.1,ht.2.trans_le hcut⟩)
    (fun t ht => hY t ⟨ht.1,ht.2.trans_le hcut⟩)
    (fun t ht => hx t ⟨ht.1,ht.2.trans hcut⟩)
    (fun t ht => hy t ⟨ht.1,ht.2.trans hcut⟩)
    (fun t ht => hG t ⟨ht.1,ht.2.trans hcut⟩)
    (fun t ht => hH t ⟨ht.1,ht.2.trans hcut⟩)
    (fun t ht => hCX t ⟨ht.1,ht.2.trans hcut⟩)
    (fun t ht => hCY t ⟨ht.1,ht.2.trans hcut⟩)
    (fun i t ht => heqX i t ⟨ht.1,ht.2.trans hcut⟩)
    (fun i t ht => heqY i t ⟨ht.1,ht.2.trans hcut⟩)
  have hn (j : J) : 0 ≤ ∫ z, positiveBox jump rateX rateY preX preY ρ C s j z
      ∂countingMeasure j ω := integral_nonneg (positiveBox_nonnegative _ _ _ _ _ _ _ _ j)
  have he := ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_add (hρ _ _) (Finset.sum_nonneg (fun j _ => hn j)),
    ENNReal.ofReal_sum_of_nonneg (fun j _ => hn j)] at he
  apply he.trans
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro j _
  rw [ofReal_integral_eq_lintegral_ofReal (hi jump rateX rateY preX preY ρ C s j)
    (Eventually.of_forall (positiveBox_nonnegative _ _ _ _ _ _ _ _ j))]
  apply lintegral_mono
  intro z
  by_cases hz : z ∈ Ioc 0 (s : ℝ) ×ˢ Iic C
  · have hzT : z.1 ∈ Ioc 0 (T : ℝ) :=
      ⟨hz.1.1,hz.1.2.trans (hcut.trans (cutHorizon_le σ T))⟩
    have hzσ : ENNReal.ofReal z.1 ≤ σ :=
      (ENNReal.ofReal_le_ofReal (hz.1.2.trans hcut)).trans (by
        simpa only [ENNReal.ofReal_coe_nnreal] using cutHorizon_le_exit σ T)
    simp only [positiveBox, Set.indicator_of_mem hz, stoppedField, hzT, hzσ, and_self, if_true, le_refl]
  · simp only [positiveBox, Set.indicator_of_not_mem hz, ENNReal.ofReal_zero, zero_le]

end CarryingCapacity.UniversalStoppedComparison
