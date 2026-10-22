import CarryingCapacity.UniversalStoppedComparison
import CarryingCapacity.CadlagFiniteRange

/-!
# Pathwise synchronous comparison for arbitrary càdlàg environments

The actual two coordinate equations imply the stopped running-supremum
bound on one common canonical-noise event. All paths and coefficients may
be selected after that event. Their finite state ranges and finite rate caps
on each horizon are derived from càdlàg regularity and statewise continuity.
No activity estimate, finite-state premise, or stochastic inequality is
assumed. The common stopping time is an arbitrary extended time pathwise.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical Topology ENNReal BigOperators NNReal

namespace CarryingCapacity.RandomEnvironmentPathwise
open MarkedNoise UniversalStoppedComparison RandomEnvironmentCompensation
  SynchronousRunningSupremum SynchronousStoppedRunningSupremum CommonFrozenExit

variable {E J I M : Type*} [DecidableEq E] [Fintype J]
  [TopologicalSpace E] [DiscreteTopology E] [TopologicalSpace M]

/-- A single event supports all sample-dependent paths and environments.
Finite ranges and height caps are proved internally from their càdlàg paths. -/
theorem ae_stopped_sup_le_of_cadlag (test : I → E → ℝ)
    (hsep : ∀ x y : E, (∀ i, test i x = test i y) → x = y) :
    ∀ᵐ ω ∂law J, ∀ (jump : J → E → E) (q : J → E → M → ℝ),
      (∀ j x, Continuous (q j x)) →
      ∀ (X Y preX preY : ℝ → E) (U W preU preW : ℝ → M)
        (σ : ℝ≥0∞) (T : ℝ≥0) (ρ : E → E → ℝ),
      (∀ x y, 0 ≤ ρ x y) →
      CadlagNonnegative X → CadlagNonnegative Y →
      CadlagNonnegative U → CadlagNonnegative W →
      (∀ t : ℝ, 0 < t → Tendsto X (𝓝[<] t) (𝓝 (preX t))) →
      (∀ t : ℝ, 0 < t → Tendsto Y (𝓝[<] t) (𝓝 (preY t))) →
      (∀ t : ℝ, 0 < t → Tendsto U (𝓝[<] t) (𝓝 (preU t))) →
      (∀ t : ℝ, 0 < t → Tendsto W (𝓝[<] t) (𝓝 (preW t))) →
      (∀ i t, t ∈ Icc 0 (cutHorizon σ T : ℝ) → test i (X t) - test i (X 0) =
        ∑ j : J, ∫ z, TimeDependentEquationUniqueness.increment jump
          (fun j s x => q j x (preU s)) preX (test i) j t z ∂countingMeasure j ω) →
      (∀ i t, t ∈ Icc 0 (cutHorizon σ T : ℝ) → test i (Y t) - test i (Y 0) =
        ∑ j : J, ∫ z, TimeDependentEquationUniqueness.increment jump
          (fun j s x => q j x (preW s)) preY (test i) j t z ∂countingMeasure j ω) →
      intervalSup (stopped σ (fun t => ENNReal.ofReal (ρ (X t) (Y t)))) T ≤
        ENNReal.ofReal (ρ (X 0) (Y 0)) + ∑ j : J, ∫⁻ z,
          stoppedField jump (fun j s x => q j x (preU s))
            (fun j s x => q j x (preW s)) preX preY ρ σ T j z ∂countingMeasure j ω := by
  filter_upwards [UniversalStoppedComparison.ae_stopped_sup_le (J := J) test hsep] with ω hω
  intro jump q hq X Y preX preY U W preU preW σ T ρ hρ hX hY hU hW hx hy hu hw heqX heqY
  obtain ⟨G,_,hG⟩ := CadlagFiniteRange.exists_finite_range_with_left X preX hX hx T
  obtain ⟨H,_,hH⟩ := CadlagFiniteRange.exists_finite_range_with_left Y preY hY hy T
  obtain ⟨CX,_,hCX⟩ := CadlagCompactBounds.exists_finite_observable_bound U preU hU hu
    (fun p : J × {x // x ∈ G} => q p.1 p.2.1) (fun p => hq p.1 p.2.1) T
  obtain ⟨CY,_,hCY⟩ := CadlagCompactBounds.exists_finite_observable_bound W preW hW hw
    (fun p : J × {x // x ∈ H} => q p.1 p.2.1) (fun p => hq p.1 p.2.1) T
  have hsub (s : ℝ) (hs : s ∈ Ioc 0 (cutHorizon σ T : ℝ)) : s ∈ Ioc 0 (T : ℝ) :=
    ⟨hs.1,hs.2.trans (cutHorizon_le σ T)⟩
  exact hω G H jump (fun j s x => q j x (preU s)) (fun j s x => q j x (preW s))
    (max CX CY) σ T X Y preX preY ρ hρ
    (fun t ht => hX.1 t ht.1) (fun t ht => hY.1 t ht.1)
    (fun t ht => hx t ht.1) (fun t ht => hy t ht.1)
    (fun t ht => hG t (hsub t ht)) (fun t ht => hH t (hsub t ht))
    (fun t ht j => (hCX (j,⟨preX t,hG t (hsub t ht)⟩) t (hsub t ht)).trans (le_max_left _ _))
    (fun t ht j => (hCY (j,⟨preY t,hH t (hsub t ht)⟩) t (hsub t ht)).trans (le_max_right _ _))
    heqX heqY

end CarryingCapacity.RandomEnvironmentPathwise
