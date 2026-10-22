import CarryingCapacity.NonlinearHorizonConsistency
import CarryingCapacity.TimeDependentLocalUniqueness

/-!
# Pathwise consistency of nonlinear realizations across horizons

The existing nonlinear laws agree on overlapping intervals. On the common
initial-state/noise space, the actual counting equations therefore have the
same coefficients there. Local pathwise uniqueness proves agreement of the
realized paths, including the smaller terminal time. A countable intersection
gives simultaneous compatibility of every pair of integer horizons.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace CarryingCapacity.NonlinearPathConsistency
open CommonInitialNoise NonlinearFixedPoint

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)

/-- Actual canonical paths, not only their laws, agree throughout the overlap. -/
theorem ae_process_eq_on_overlap (S T : ℝ) (hS : 0 ≤ S) (hT : 0 ≤ T) (hST : S ≤ T) :
    ∀ᵐ p ∂law ν.measure (Jump D),
      EqOn (process control hActivity ν S hS hCoupling hMoment p)
        (process control hActivity ν T hT hCoupling hMoment p) (Icc 0 S) := by
  let X := process control hActivity ν S hS hCoupling hMoment
  let Y := process control hActivity ν T hT hCoupling hMoment
  let xp := preState control hActivity ν S hS hCoupling hMoment
  let yp := preState control hActivity ν T hT hCoupling hMoment
  let v := environment control hActivity ν S hS hCoupling hMoment
  let w := environment control hActivity ν T hT hCoupling hMoment
  have hzS : ∀ᵐ p ∂law ν.measure (Jump D), X p 0 = p.1 :=
    DeterministicEnvironmentProcess.ae_initial control hActivity v S hS
      (continuous_environment control hActivity ν S hS hCoupling hMoment).continuousOn id ν.measure
  have hzT : ∀ᵐ p ∂law ν.measure (Jump D), Y p 0 = p.1 :=
    DeterministicEnvironmentProcess.ae_initial control hActivity w T hT
      (continuous_environment control hActivity ν T hT hCoupling hMoment).continuousOn id ν.measure
  have hqS := ae_all_iff.mpr (fun i : Fin D =>
    ae_counting_identity control hActivity ν S hS hCoupling hMoment (fun x => (x i : ℝ)))
  have hqT := ae_all_iff.mpr (fun i : Fin D =>
    ae_counting_identity control hActivity ν T hT hCoupling hMoment (fun x => (x i : ℝ)))
  filter_upwards [hzS, hzT, hqS, hqT,
    ae_process_cadlag control hActivity ν S hS hCoupling hMoment,
    ae_process_cadlag control hActivity ν T hT hCoupling hMoment,
    ae_preState_eq_leftLim control hActivity ν S hS hCoupling hMoment,
    ae_preState_eq_leftLim control hActivity ν T hT hCoupling hMoment]
    with p hzS hzT hqS hqT hcS hcT hpS hpT
  have hx : ∀ t : ℝ, 0 < t → Tendsto (X p) (𝓝[<] t) (𝓝 (xp p t)) := by
    intro t ht
    obtain ⟨y, hy⟩ := hcS.2 t ht
    change Tendsto _ _ (𝓝 (preState control hActivity ν S hS hCoupling hMoment p t))
    rw [hpS t ht, leftLim_eq_of_tendsto (neBot_iff.mp inferInstance) hy]
    exact hy
  have hy : ∀ t : ℝ, 0 < t → Tendsto (Y p) (𝓝[<] t) (𝓝 (yp p t)) := by
    intro t ht
    obtain ⟨y, hy⟩ := hcT.2 t ht
    change Tendsto _ _ (𝓝 (preState control hActivity ν T hT hCoupling hMoment p t))
    rw [hpT t ht, leftLim_eq_of_tendsto (neBot_iff.mp inferInstance) hy]
    exact hy
  apply TimeDependentLocalUniqueness.eqOn_of_separating_counting_equations
    (fun i : Fin D => fun x : State D => (x i : ℝ))
    (fun x y h => by
      funext i
      have hi : (x i : ℝ) = (y i : ℝ) := h i
      exact_mod_cast hi) Jump.advance
    (fun j t x => q.rate j x (v t)) (fun j t x => q.rate j x (w t))
    (fun j => MarkedNoise.countingMeasure j p.2) (X p) (Y p) (xp p) (yp p) S
    (fun j t x ht => congrArg (q.rate j x)
      (NonlinearHorizonConsistency.environment_eq_on_overlap control ν S T hS hT hST
        hActivity hCoupling hMoment ht)) hcS.1 hcT.1 hx hy (hzS.trans hzT.symm)
  · intro i t ht
    rw [hzS]
    exact hqS i ⟨t,ht.1⟩ ht.2
  · intro i t ht
    rw [hzT]
    exact hqT i ⟨t,ht.1⟩ (ht.2.trans hST)

/-- All integer-horizon realizations are compatible on one common event. -/
theorem ae_integer_compatible : ∀ᵐ p ∂law ν.measure (Jump D), ∀ m n : ℕ,
    m ≤ n → EqOn
      (process control hActivity ν (m : ℝ) (Nat.cast_nonneg m) hCoupling hMoment p)
      (process control hActivity ν (n : ℝ) (Nat.cast_nonneg n) hCoupling hMoment p)
      (Icc 0 (m : ℝ)) := by
  apply ae_all_iff.mpr
  intro m
  apply ae_all_iff.mpr
  intro n
  by_cases hmn : m ≤ n
  · filter_upwards [ae_process_eq_on_overlap control hActivity ν hCoupling hMoment
      m n (Nat.cast_nonneg m) (Nat.cast_nonneg n) (by exact_mod_cast hmn)] with p hp
    exact fun _ => hp
  · exact Eventually.of_forall (fun _ h => False.elim (hmn h))

end CarryingCapacity.NonlinearPathConsistency
