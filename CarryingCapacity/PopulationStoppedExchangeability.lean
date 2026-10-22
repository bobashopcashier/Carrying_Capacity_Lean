import CarryingCapacity.ConfigurationRelabeling
import CarryingCapacity.ParticleRelabeling
import CarryingCapacity.PopulationCouplingTime
import CarryingCapacity.PopulationCouplingInitialization

/-!
# Coordinate symmetry of the actual stopped population coupling

Simultaneous relabeling of the paired initial record and the complete particle
noise preserves their actual product law. The constructed interacting and
prescribed-environment paths transform by the same coordinate permutation.
Consequently their genuine joint Lyapunov exit is unchanged, including the
exit jump, and every coordinate's expected stopped running cost equals the
population-averaged stopped expectation.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal

namespace CarryingCapacity.PopulationStoppedExchangeability
open CommonInitialNoise ConfigurationLocalization PopulationCouplingAlgebra
open PopulationStoppedCoupling PopulationCouplingTime PopulationCouplingInitialization
open Symmetrization CommonFrozenExit SynchronousRunningSupremum

variable {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}

/-- The actual empirical Lyapunov function is invariant under relabeling. -/
theorem lyapunov_relabel (control : LyapunovControl κ q)
    (e : Equiv.Perm (Fin N)) (z : Configuration N D) :
    lyapunov control (relabel e z) = lyapunov control z :=
  Symmetrization.empiricalMean_relabel e control.function z

/-- A deterministic all-time path permutation preserves the genuine joint
exit. Only nonnegative times enter the exit set. -/
theorem exitTime_eq_of_relabel (control : LyapunovControl κ q)
    (e : Equiv.Perm (Fin N))
    (X Y X' Y' : ℝ → Configuration N D)
    (hX : ∀ t, 0 ≤ t → X' t = relabel e (X t))
    (hY : ∀ t, 0 ≤ t → Y' t = relabel e (Y t)) (R : ℝ) :
    exitTime (jointRegion control R) (fun t => (X' t, Y' t)) =
      exitTime (jointRegion control R) (fun t => (X t, Y t)) := by
  have hs : exitSet (jointRegion control R) (fun t => (X' t, Y' t)) =
      exitSet (jointRegion control R) (fun t => (X t, Y t)) := by
    ext t
    simp only [exitSet, mem_setOf_eq]
    by_cases ht : 0 ≤ t
    · simp only [ht, true_and, jointRegion, mem_setOf_eq, hX t ht, hY t ht,
        lyapunov_relabel]
    · simp only [ht, false_and]
  simp only [exitTime, hs]

/-- Stopping at the same extended time commutes with coordinate relabeling,
including a finite exit's endpoint value. -/
theorem intervalSup_stopped_coordinate_eq_of_relabel (e : Equiv.Perm (Fin N))
    (X Y X' Y' : ℝ → Configuration N D)
    (hX : ∀ t, 0 ≤ t → X' t = relabel e (X t))
    (hY : ∀ t, 0 ≤ t → Y' t = relabel e (Y t))
    (σ : ℝ≥0∞) (i : Fin N) (S : ℝ) :
    intervalSup (stopped σ (fun t => ENNReal.ofReal (coordinateCost κ i (X' t) (Y' t)))) S =
      intervalSup (stopped σ (fun t => ENNReal.ofReal (coordinateCost κ (e i) (X t) (Y t)))) S := by
  unfold intervalSup
  apply iSup_congr
  intro t
  by_cases hσ : σ = ⊤
  · simp only [stopped, if_pos hσ, hX t t.property.1, hY t t.property.1,
      coordinateCost, relabel_apply]
  · have ht : 0 ≤ min (t : ℝ) σ.toReal := le_min t.property.1 ENNReal.toReal_nonneg
    simp only [stopped, if_neg hσ, hX _ ht, hY _ ht, coordinateCost, relabel_apply]

/-- Finite normalization preserves a common extended expectation, even if
that expectation is infinite. The coefficient is genuinely nonzero. -/
private theorem lintegral_normalized_sum_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (hN : 0 < N) (f : Fin N → Ω → ℝ≥0∞)
    (hf : ∀ i, AEMeasurable (f i) μ) (i : Fin N)
    (he : ∀ j, (∫⁻ ω, f j ω ∂μ) = ∫⁻ ω, f i ω ∂μ) :
    (∫⁻ ω, ENNReal.ofReal (N : ℝ)⁻¹ * ∑ j, f j ω ∂μ) =
      ∫⁻ ω, f i ω ∂μ := by
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_finset_sum' _ (fun j _ => hf j)]
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hN), ENNReal.ofReal_natCast,
    ← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast Nat.ne_of_gt hN)
      (ENNReal.natCast_ne_top N), one_mul]

section Actual
variable (control : LyapunovControl κ q) (hN : 0 < N)
  (hActivity : MomentActivityBound κ q)
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))
  (γ : Measure (Record N D)) [IsProbabilityMeasure γ]
  (hex : ExchangeableMatching.ExchangeableLaw γ)
  (hCoupling : MomentCouplingBound κ q) (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ s ∈ Icc 0 T,
    LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
  (hInitialX : Integrable (fun a => lyapunov control (left a)) γ)
  (hInitialY : Integrable (fun a => lyapunov control (right a)) γ)
include hex hCoupling hB hEnv hInitialX hInitialY

local notation "X" => ConfigurationTimeDependent.process control hN (left (N := N) (D := D))
local notation "Y" => DeterministicEnvironmentConfiguration.process control hN hActivity v T hT hv (right (N := N) (D := D))

/-- The actual joint exit is invariant under relabeling on one event for
all thresholds. Path symmetry is derived from the actual counting equations. -/
theorem ae_pairExit_relabel (e : Equiv.Perm (Fin N)) :
    ∀ᵐ p ∂law γ (Label N D), ∀ R : ℝ,
      pairExit control hN hActivity v T hT hv left right R (ParticleRelabeling.sampleRelabel e p) =
        pairExit control hN hActivity v T hT hv left right R p := by
  filter_upwards [ConfigurationRelabeling.ae_interacting_relabel control hN γ hex hInitialX e,
    ConfigurationRelabeling.ae_environment_relabel control hN hActivity v T hT hv γ hex
      hCoupling B hB hEnv hInitialY e] with p hx hy
  intro R
  exact exitTime_eq_of_relabel control e (X p) (Y p)
    (X (ParticleRelabeling.sampleRelabel e p)) (Y (ParticleRelabeling.sampleRelabel e p)) hx hy R

/-- Every actual coordinate stopped supremum has the correct permutation
orientation, simultaneously for all coordinates, thresholds and horizons.
A finite exit's endpoint is retained. -/
theorem ae_coordinateStoppedCost_relabel (e : Equiv.Perm (Fin N)) :
    ∀ᵐ p ∂law γ (Label N D), ∀ (R : ℝ) (i : Fin N) (S : ℝ),
      coordinateStoppedCost control hN hActivity v T hT hv left right R i S
        (ParticleRelabeling.sampleRelabel e p) =
      coordinateStoppedCost control hN hActivity v T hT hv left right R (e i) S p := by
  filter_upwards [ConfigurationRelabeling.ae_interacting_relabel control hN γ hex hInitialX e,
    ConfigurationRelabeling.ae_environment_relabel control hN hActivity v T hT hv γ hex
      hCoupling B hB hEnv hInitialY e,
    ae_pairExit_relabel control hN hActivity v T hT hv γ hex hCoupling B hB hEnv hInitialX hInitialY e]
    with p hx hy he
  intro R i S
  change intervalSup (stopped
    (pairExit control hN hActivity v T hT hv left right R (ParticleRelabeling.sampleRelabel e p))
    (fun t => ENNReal.ofReal (coordinateCost κ i
      (X (ParticleRelabeling.sampleRelabel e p) t) (Y (ParticleRelabeling.sampleRelabel e p) t)))) S =
    intervalSup (stopped (pairExit control hN hActivity v T hT hv left right R p)
      (fun t => ENNReal.ofReal (coordinateCost κ (e i) (X p t) (Y p t)))) S
  rw [he R]
  exact intervalSup_stopped_coordinate_eq_of_relabel e (X p) (Y p)
    (X (ParticleRelabeling.sampleRelabel e p)) (Y (ParticleRelabeling.sampleRelabel e p)) hx hy _ i S

/-- Measure preservation of the full initial/noise law transfers the actual
path identity to equality of extended stopped expectations. -/
theorem lintegral_coordinateStoppedCost_relabel (e : Equiv.Perm (Fin N))
    (R : ℝ) (i : Fin N) (S : ℝ≥0) :
    (∫⁻ p, coordinateStoppedCost control hN hActivity v T hT hv left right R i S p
      ∂law γ (Label N D)) =
    ∫⁻ p, coordinateStoppedCost control hN hActivity v T hT hv left right R (e i) S p
      ∂law γ (Label N D) := by
  have hp := ParticleRelabeling.sampleRelabel_preserving (J := Jump D) e γ hex
  have hm := aemeasurable_coordinateStoppedCost control hN hActivity v T hT hv left right γ
    hCoupling measurable_left measurable_right B hB hEnv hInitialX hInitialY R i S
  have hm' : AEMeasurable
      (coordinateStoppedCost control hN hActivity v T hT hv left right R i S)
      ((law γ (Label N D)).map (ParticleRelabeling.sampleRelabel e)) := by
    rw [hp.map_eq]
    exact hm
  have hh := lintegral_map' hm' hp.measurable.aemeasurable
  rw [hp.map_eq] at hh
  apply hh.trans
  apply lintegral_congr_ae
  filter_upwards [ae_coordinateStoppedCost_relabel control hN hActivity v T hT hv γ hex
    hCoupling B hB hEnv hInitialX hInitialY e] with p he
  exact he R i S

/-- Any two coordinates have exactly equal actual stopped expectations. -/
theorem lintegral_coordinateStoppedCost_eq (R : ℝ) (i j : Fin N) (S : ℝ≥0) :
    (∫⁻ p, coordinateStoppedCost control hN hActivity v T hT hv left right R i S p
      ∂law γ (Label N D)) =
    ∫⁻ p, coordinateStoppedCost control hN hActivity v T hT hv left right R j S p
      ∂law γ (Label N D) := by
  simpa only [Equiv.swap_apply_left] using
    lintegral_coordinateStoppedCost_relabel control hN hActivity v T hT hv γ hex
      hCoupling B hB hEnv hInitialX hInitialY (Equiv.swap i j) R i S

/-- The expected stopped cost of each coordinate equals the expected
population average. Actual AE measurability justifies exchanging the finite
sum and the integral, without a finite-expectation premise. -/
theorem lintegral_coordinateStoppedCost_eq_expectedStoppedCost (R : ℝ) (i : Fin N) (S : ℝ≥0) :
    (∫⁻ p, coordinateStoppedCost control hN hActivity v T hT hv left right R i S p
      ∂law γ (Label N D)) =
    expectedStoppedCost control hN hActivity v T hT hv left right γ R S := by
  symm
  refine lintegral_normalized_sum_eq (law γ (Label N D)) hN
    (fun j => coordinateStoppedCost control hN hActivity v T hT hv left right R j S) ?_ i ?_
  · intro j
    exact aemeasurable_coordinateStoppedCost control hN hActivity v T hT hv left right γ
      hCoupling measurable_left measurable_right B hB hEnv hInitialX hInitialY R j S
  · intro j
    exact lintegral_coordinateStoppedCost_eq control hN hActivity v T hT hv γ hex
      hCoupling B hB hEnv hInitialX hInitialY R j i S

end Actual
end CarryingCapacity.PopulationStoppedExchangeability
