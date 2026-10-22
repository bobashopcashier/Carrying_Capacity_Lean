import CarryingCapacity.PopulationFocalConvergence
import CarryingCapacity.PopulationSynchronousApproximation

/-!
# All three synchronous approximation conclusions

The manuscript initialization supplies one family of paired initial laws with
the exact prescribed vector marginals. The actual common-noise configurations
on those laws satisfy averaged-path, paired-empirical, and every fixed-focal
approximation simultaneously. In particular, no expected initial-error limit,
path exchangeability, or stopped-coordinate estimate is assumed here.

This finishes the three canonical comparison conclusions of Theorem 5.4.
Uniform empirical convergence to the deterministic nonlinear law and path-space
propagation of chaos require the independent-process argument of Section 6.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.PopulationFocalApproximation
open CommonInitialNoise ConfigurationLocalization PopulationCouplingInitialization
open PopulationCouplingTime PopulationSynchronousApproximation PopulationFocalProbability

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)

local notation "v" => NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment
local notation "hv" => Continuous.continuousOn (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment)

/-- Maximum path discrepancy among the first k existing particles. For each
fixed k this is the manuscript statistic once the population size is at least k. -/
def focalPathDiscrepancy (n k : ℕ) (S : ℝ)
    (p : Sample (Record (n + 1) D) (Label (n + 1) D)) : ℝ≥0∞ :=
  focalRunningCost control (Nat.succ_pos n) hActivity v T hT hv left right
    (focalIndices (n + 1) k) S p

/-- Once the population contains k particles, the threshold event is exactly
the event that one of the first k actual coordinate running costs exceeds it. -/
theorem lt_focalPathDiscrepancy_iff (n k : ℕ) (hkn : k ≤ n + 1) (S : ℝ)
    (p : Sample (Record (n + 1) D) (Label (n + 1) D)) (ε : ℝ≥0∞) :
    ε < focalPathDiscrepancy control hActivity ν T hT hCoupling hMoment n k S p ↔
      ∃ i : Fin k, ε < PopulationCouplingRemoval.coordinateRunningCost
        control (Nat.succ_pos n) hActivity v T hT hv left right (Fin.castLE hkn i) S p := by
  rw [focalPathDiscrepancy, lt_focalRunningCost_iff]
  constructor
  · rintro ⟨i, hi, hc⟩
    let j : Fin k := ⟨i.val, (mem_focalIndices i).mp hi⟩
    have he : Fin.castLE hkn j = i := Fin.ext rfl
    exact ⟨j, by simpa only [he] using hc⟩
  · rintro ⟨i, hi⟩
    exact ⟨Fin.castLE hkn i, (mem_focalIndices _).mpr i.isLt, hi⟩

/-- The actual coupled systems satisfy all three conclusions of synchronous
approximation under precisely the manuscript initialization hypotheses. -/
theorem exists_full_synchronous_approximation {Ω : Type*} [MeasurableSpace Ω]
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
        atTop (𝓝 0)) ∧
      (∀ k : ℕ, ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (law (γ n) (Label (n + 1) D)).real
        {p | ENNReal.ofReal ε < focalPathDiscrepancy control hActivity ν T hT hCoupling hMoment n k T p})
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
  refine ⟨γ, hp, he, hl, hr, ?_, hprob, ?_, ?_⟩
  · intro R hR
    exact PopulationCouplingConvergence.expectedStoppedCost_tendsto_zero
      control hActivity ν T hT hCoupling hMoment initialX initialY γ
      (fun _ => measurable_left) (fun _ => measurable_right) hr hIX ha R hR
  · intro ε hε
    apply squeeze_zero (fun _ => measureReal_nonneg) _ (hprob ε hε)
    intro n
    exact PopulationEmpiricalCoupling.probability_empiricalRunningCost_le
      control (Nat.succ_pos n) hActivity v T hT hv left right (γ n) T ε
  · intro k ε hε
    exact PopulationFocalConvergence.probability_focalRunningCost_tendsto_zero
      control hActivity ν T hT hCoupling hMoment γ he hr hIX ha
      (max C (∫ x, control.function x ∂ν.measure)) hMX k ε hε

end CarryingCapacity.PopulationFocalApproximation
