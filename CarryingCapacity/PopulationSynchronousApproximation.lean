import CarryingCapacity.PopulationCouplingConvergence
import CarryingCapacity.PopulationEmpiricalCoupling

/-!
# Synchronous population approximation under the manuscript initialization

The actual initial-coupling theorem supplies the paired laws and every initial
moment and error limit needed by the stochastic comparison. The constructed
same-noise finite systems then have vanishing averaged path discrepancy and
uniform empirical transport discrepancy in probability. Both are genuine
uncountable time suprema. The fixed-focal conclusion still requires paired-path
exchangeability, and convergence of the independent empirical process to the
nonlinear law uniformly in time is a separate Section 6 result.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.PopulationSynchronousApproximation
open CommonInitialNoise ConfigurationLocalization PopulationCouplingInitialization
open PopulationCouplingRemoval PopulationEmpiricalCoupling PopulationCouplingTime

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)

local notation "v" => NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment
local notation "hv" => Continuous.continuousOn (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment)

/-- Average of the actual coordinate running suprema on the paired record
space supplied by the manuscript initialization theorem. -/
def pathDiscrepancy (n : ℕ) (S : ℝ) (p : Sample (Record (n + 1) D) (Label (n + 1) D)) : ℝ≥0∞ :=
  averagedRunningCost control (Nat.succ_pos n) hActivity v T hT hv left right S p

/-- Uniform transport distance between the two actual empirical processes. -/
def empiricalPathDiscrepancy (n : ℕ) (S : ℝ)
    (p : Sample (Record (n + 1) D) (Label (n + 1) D)) : ℝ≥0∞ :=
  empiricalRunningCost control (Nat.succ_pos n) hActivity v T hT hv left right S p

/-- The initialization assumptions of the manuscript imply both population
and empirical synchronous approximation. No convergence of expected initial
distances, stopped errors, or independent empirical errors is an input. -/
theorem exists_synchronous_approximation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (z : ∀ n, Ω → Configuration (n + 1) D) (hz : ∀ n, Measurable (z n))
    (hex : ∀ n, ExchangeableMatching.ExchangeableLaw (P.map (z n)))
    (hΨ : ∀ n, Integrable (fun ω => lyapunov control (z n ω)) P)
    (C : ℝ) (hbound : ∀ n, (∫ ω, lyapunov control (z n ω) ∂P) ≤ C)
    (hconv : TendstoInMeasure P
      (fun n ω => wasserstein (empiricalLaw κ (Nat.succ_pos n) (z n ω)) ν) atTop 0) :
    ∃ γ : ∀ n, Measure (Record (n + 1) D),
      (∀ n, IsProbabilityMeasure (γ n)) ∧
      (∀ n, ExchangeableMatching.ExchangeableLaw (γ n)) ∧
      (∀ n, (γ n).map left = P.map (z n)) ∧
      (∀ n, (γ n).map right = Measure.pi (fun _ : Fin (n + 1) => ν.measure)) ∧
      (∀ R : ℝ, 0 ≤ R → Tendsto (fun n =>
        expectedStoppedCost control (Nat.succ_pos n) hActivity v T hT hv left right (γ n) R T)
        atTop (𝓝 0)) ∧
      (∀ ε : ℝ, 0 < ε → Tendsto (fun n => (law (γ n) (Label (n + 1) D)).real
        {p | ENNReal.ofReal ε < pathDiscrepancy control hActivity ν T hT hCoupling hMoment n T p})
        atTop (𝓝 0)) ∧
      (∀ ε : ℝ, 0 < ε → Tendsto (fun n => (law (γ n) (Label (n + 1) D)).real
        {p | ENNReal.ofReal ε < empiricalPathDiscrepancy control hActivity ν T hT hCoupling hMoment n T p})
        atTop (𝓝 0)) := by
  obtain ⟨γ, hp, he, hl, hr, hIX, _hIY, hMX, _hMY, ha⟩ :=
    exists_initialization control P ν hMoment z hz hex hΨ C hbound hconv
  letI : ∀ n, IsProbabilityMeasure (γ n) := hp
  let initialX := fun n : ℕ => left (N := n + 1) (D := D)
  let initialY := fun n : ℕ => right (N := n + 1) (D := D)
  have hprob (ε : ℝ) (hε : 0 < ε) : Tendsto (fun n => (law (γ n) (Label (n + 1) D)).real
      {p | ENNReal.ofReal ε < pathDiscrepancy control hActivity ν T hT hCoupling hMoment n T p})
      atTop (𝓝 0) :=
    PopulationCouplingConvergence.probability_runningCost_tendsto_zero
      control hActivity ν T hT hCoupling hMoment initialX initialY γ
      (fun _ => measurable_left) (fun _ => measurable_right) hr hIX ha
      (max C (∫ x, control.function x ∂ν.measure)) hMX ε hε
  refine ⟨γ, hp, he, hl, hr, ?_, hprob, ?_⟩
  · intro R hR
    exact PopulationCouplingConvergence.expectedStoppedCost_tendsto_zero
      control hActivity ν T hT hCoupling hMoment initialX initialY γ
      (fun _ => measurable_left) (fun _ => measurable_right) hr hIX ha R hR
  · intro ε hε
    apply squeeze_zero (fun _ => measureReal_nonneg) _ (hprob ε hε)
    intro n
    exact probability_empiricalRunningCost_le control (Nat.succ_pos n) hActivity v T hT hv
      left right (γ n) T ε

end CarryingCapacity.PopulationSynchronousApproximation
