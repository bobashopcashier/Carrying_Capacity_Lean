import CarryingCapacity.TimeDependentJumpIdentity
import CarryingCapacity.TimeDependentPredictable
import CarryingCapacity.FrozenCountingIdentity

/-!
# The actual counting equation for time-dependent frozen rates

Chronological telescoping at the constructed strict-past state agrees with
integration against the actual common counting measures. Finite box support
proves pathwise Bochner integrability; no counting equation is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal

namespace CarryingCapacity.TimeDependentCountingIdentity
open MarkedNoise ChronologicalEvents TimeDependentJumpIdentity
open FrozenCountingIdentity (ae_integrable_box_weights ae_integral_box_eq_sum)
variable {J : Type*} [Fintype J]

open TimeDependentFrozenProcess TimeDependentPredictable

variable {E : Type*} [DecidableEq E] [TopologicalSpace E] [PolishSpace E]
  (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)

/-- The predictable pre-state agrees with the explicit chronological left
state at every positive time on one event of probability one. -/
theorem ae_preState_eq_leftProcess : ∀ᵐ ω ∂law J,
    ∀ C x t, 0 < t → preState active jump rate C x ω t =
      leftProcess active jump rate C x ω t := by
  filter_upwards [ae_process_eq_leftProcess_on_left active jump rate] with ω hω
  intro C x t ht
  obtain ⟨b, hb, hy⟩ := hω C x t
  exact preState_eq_of_left_constant active jump rate C x ω t ht b hb _ hy

omit [Fintype J] [PolishSpace E] in
/-- The predictable jump integrand already vanishes at nonpositive times and
above the construction's height cutoff. -/
theorem jumpIncrement_box_indicator (C : ℝ) (x : E) (V : E → ℝ)
    (j : J) (ω : Sample J) (T : ℝ) :
    (Iic T ×ˢ Iic C).indicator (fun p => jumpIncrement active jump rate C x V j (ω,p)) =
      (Ioc 0 T ×ˢ univ).indicator (fun p => jumpIncrement active jump rate C x V j (ω,p)) := by
  funext p
  simp only [Set.indicator_apply, Set.mem_prod, Set.mem_Iic, Set.mem_Ioc, Set.mem_univ, and_true]
  by_cases hT : p.1 ≤ T <;> by_cases hC : p.2 ≤ C <;> by_cases hp : 0 < p.1 <;>
    simp [jumpIncrement, hT, hC, hp]

omit [PolishSpace E] in
/-- Actual pathwise Bochner integrability is a consequence of finite event
support, not an integrability hypothesis imposed on the jump equation. -/
theorem ae_integrable_jumpIncrement : ∀ᵐ ω ∂law J,
    ∀ C x T (V : E → ℝ) (j : J),
      IntegrableOn (fun p => jumpIncrement active jump rate C x V j (ω,p))
        (Ioc 0 T ×ˢ univ) (countingMeasure j ω) := by
  filter_upwards [ae_integrable_box_weights (J := J)] with ω hω
  intro C x T V j
  rw [← integrable_indicator_iff (measurableSet_Ioc.prod MeasurableSet.univ),
    ← jumpIncrement_box_indicator active jump rate C x V j ω T]
  exact hω T C j _

/-- The actual frozen path solves the test-function jump equation with the
proved predictable pre-state and the original common counting measures. -/
theorem ae_testFunction_counting_identity (V : E → ℝ) : ∀ᵐ ω ∂law J,
    ∀ C x T,
      V (process active jump rate C x ω T) - V (process active jump rate C x ω 0) =
        ∑ j : J, ∫ p in Ioc 0 T ×ˢ univ,
          jumpIncrement active jump rate C x V j (ω,p) ∂countingMeasure j ω := by
  filter_upwards [ae_process_telescope_left active jump rate V,
    ae_preState_eq_leftProcess active jump rate, ae_integral_box_eq_sum (J := J),
    ae_boxedList_mem (J := J), MarkedNoise.ae_positive_points (J := J)]
      with ω htel hpre hint hmem hpos
  intro C x T
  rw [htel C x T]
  calc
    _ = ∑ n : Fin (boxedList (ω,T,C)).length,
        let e := (boxedList (ω,T,C)).get n
        jumpIncrement active jump rate C x V e.1 (ω, point e.1 ω e.2) := by
      apply Finset.sum_congr rfl
      intro n _
      let e := (boxedList (ω,T,C)).get n
      have he : e ∈ boxedList (ω,T,C) := List.get_mem _ n
      have heC : (point e.1 ω e.2).2 ≤ C := ((hmem T C e).mp he).2
      have hepos := (hpos e.1 e.2).1
      change acceptedIncrement active jump rate V ω
        (leftProcess active jump rate C x ω (point e.1 ω e.2).1) e =
          jumpIncrement active jump rate C x V e.1 (ω, point e.1 ω e.2)
      simp only [jumpIncrement, hpre C x _ hepos, hepos, heC, true_and]
      rfl
    _ = ∑ j : J, ∫ p, (Iic T ×ˢ Iic C).indicator
        (fun p => jumpIncrement active jump rate C x V j (ω,p)) p ∂countingMeasure j ω :=
      (hint T C (fun j p => jumpIncrement active jump rate C x V j (ω,p))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [jumpIncrement_box_indicator, integral_indicator (measurableSet_Ioc.prod MeasurableSet.univ)]

end CarryingCapacity.TimeDependentCountingIdentity
