import CarryingCapacity.LinearCarryingCapacityHypotheses
import CarryingCapacity.PopulationCoordinateMoments
import CarryingCapacity.PopulationEmpiricalLimit
import CarryingCapacity.NonlinearForwardUniqueness
import CarryingCapacity.PopulationPathChaos
import CarryingCapacity.PopulationSkorokhodLimit

/-!
# The untruncated multitype carrying-capacity application

All dynamic assumptions are proved for actual vector-mean mortality, fixed
mutations and every real Lyapunov exponent greater than one. This specializes
Corollary 7.4 to the canonical systems, including genuine J1 empirical and focal
path-space conclusions. The vector-mean convergence part of Proposition 7.5 is
also included; the closed mean ODE is a separate unbounded-test argument.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.LinearCarryingCapacityApplication
open ConfigurationLocalization CommonInitialNoise LinearCarryingCapacity

variable {D : ℕ} (c : Coefficients D) (r : ℝ) (hr : 1 < r)

local notation "control" => LinearCarryingCapacity.lyapunovControl c r hr
local notation "hActivity" => LinearCarryingCapacityHypotheses.activityBound c
local notation "hCoupling" => LinearCarryingCapacityHypotheses.couplingBound c

/-- The empirical Lyapunov average is exactly the prescribed real `r` moment. -/
theorem empirical_lyapunov_eq {N : ℕ} (z : Configuration N D) :
    ConfigurationLocalization.lyapunov control z = (N : ℝ)⁻¹ * ∑ i, (1 + populationSize (z i) ^ r) := rfl

/-- The actual multitype carrying-capacity finite system has exhausting localization
exits, for every finite positive population and every integrable initial Ψ average. -/
theorem ae_nonexplosive {A : Type*} [MeasurableSpace A] {N : ℕ} (hN : 0 < N)
    (initial : A → Configuration N D) (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial)
    (hV : Integrable (fun z => (N : ℝ)⁻¹ * ∑ i, (1 + populationSize (initial z i) ^ r)) μ) :
    ∀ᵐ p ∂law μ (Label N D), ∀ S : ℝ≥0, ∃ n : ℕ,
      (S : ℝ≥0∞) < ConfigurationTimeDependent.exit control hN initial n p :=
  ConfigurationTimeDependent.ae_exhaustive control hN initial μ hinit hV

variable (ν : MomentLaw MomentScale.linear D) (T : ℝ) (hT : 0 ≤ T)
  (hMoment : Integrable (fun x : State D => 1 + populationSize x ^ r) ν.measure)

/-- The actual nonlinear law curve for these untruncated first-moment rates. -/
def environment : ℝ → MomentLaw MomentScale.linear D :=
  NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment

/-- The constructed nonlinear curve solves the equation in the stated moment class. -/
theorem environment_isSolution : NonlinearForwardUniqueness.IsMomentBoundedSolution
    (fun x : State D => 1 + populationSize x ^ r) (LinearCarryingCapacity.rates c) ν T
    (environment c r hr ν T hT hMoment) :=
  NonlinearForwardUniqueness.environment_isSolution control hActivity ν T hT hCoupling hMoment

/-- Every other probability weak solution with a genuine bounded real-r
Lyapunov moment agrees on the entire horizon, without assumed continuity. -/
theorem solution_unique (v : ℝ → MomentLaw MomentScale.linear D)
    (hv : NonlinearForwardUniqueness.IsMomentBoundedSolution
      (fun x : State D => 1 + populationSize x ^ r) (LinearCarryingCapacity.rates c) ν T v) :
    EqOn v (environment c r hr ν T hT hMoment) (Icc 0 T) :=
  NonlinearForwardUniqueness.solution_unique control hActivity ν T hT hCoupling hMoment
    v (environment c r hr ν T hT hMoment) hv
    (environment_isSolution c r hr ν T hT hMoment)

/-- Actual all-real-time empirical transport error on the fixed horizon. -/
def runningTransportError (n : ℕ)
    (p : Sample (Configuration (n + 1) D) (Label (n + 1) D)) : ℝ≥0∞ :=
  PopulationEmpiricalLimit.runningError control hActivity ν T hT hCoupling hMoment n id p

/-- Actual all-real-time absolute first-moment error on the fixed horizon. -/
def runningPopulationError (n : ℕ)
    (p : Sample (Configuration (n + 1) D) (Label (n + 1) D)) : ℝ≥0∞ :=
  PopulationEmpiricalLimit.runningMomentError control hActivity ν T hT hCoupling hMoment n id p

section ManuscriptInitialization
variable {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (z : ∀ n, Ω → Configuration (n + 1) D) (hz : ∀ n, Measurable (z n))
  (hex : ∀ n, ExchangeableMatching.ExchangeableLaw (P.map (z n)))
  (hΨ : ∀ n : ℕ, Integrable (fun ω => (n + 1 : ℝ)⁻¹ *
    ∑ i : Fin (n + 1), (1 + populationSize (z n ω i) ^ r)) P)
  (C : ℝ) (hbound : ∀ n : ℕ, (∫ ω, (n + 1 : ℝ)⁻¹ *
    ∑ i : Fin (n + 1), (1 + populationSize (z n ω i) ^ r) ∂P) ≤ C)
  (hconv : TendstoInMeasure P (fun n ω =>
    wasserstein (empiricalLaw MomentScale.linear (Nat.succ_pos n) (z n ω)) ν) atTop 0)

include hz hex hΨ hbound hconv

/-- Corollary 7.4's uniform empirical transport limit, with every dynamic
hypothesis proved for the exact model and every real `r > 1`. -/
theorem transport_limit (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (P.map (z n)) (Label (n + 1) D))
      {p | ENNReal.ofReal ε < runningTransportError c r hr ν T hT hMoment n p})
      atTop (𝓝 0) := by
  exact PopulationEmpiricalLimit.measure_runningError_gt_tendsto_zero
    control hActivity ν T hT hCoupling hMoment P z hz hex
    (by simpa only [empirical_lyapunov_eq, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hΨ) C
    (by simpa only [empirical_lyapunov_eq, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hbound) hconv ε hε

/-- Corollary 7.4's uniform first-moment feedback limit. -/
theorem populationMoment_limit (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (P.map (z n)) (Label (n + 1) D))
      {p | ENNReal.ofReal ε < runningPopulationError c r hr ν T hT hMoment n p})
      atTop (𝓝 0) := by
  exact PopulationEmpiricalLimit.measure_runningMomentError_gt_tendsto_zero
    control hActivity ν T hT hCoupling hMoment P z hz hex
    (by simpa only [empirical_lyapunov_eq, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hΨ) C
    (by simpa only [empirical_lyapunov_eq, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hbound) hconv ε hε

/-- The actual empirical trajectory also converges in probability in the
manuscript's genuine transport-valued J1 path metric. -/
theorem empirical_J1_limit (S : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (P.map (z n)) (Label (n + 1) D)).real
      {p | ε < dist
        (PopulationSkorokhodLimit.empiricalPath control S (Nat.succ_pos n) id p)
        (PopulationSkorokhodLimit.limitPath control S hActivity ν hCoupling hMoment)})
      atTop (𝓝 0) :=
  PopulationSkorokhodLimit.probability_distance_gt_tendsto_zero
    control S hActivity ν hCoupling hMoment P z hz hex
    (by simpa only [empirical_lyapunov_eq, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hΨ) C
    (by simpa only [empirical_lyapunov_eq, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hbound) hconv ε hε

/-- Focal path-space chaos in the single vector-valued J1 space carrying
the maximum linear adapted distance, for every fixed number of particles. -/
theorem focal_path_laws_tendsto (S : ℝ≥0) (k : ℕ) :
    Tendsto (fun n => PopulationPathChaos.canonicalLaw control (Nat.succ_pos n)
      P (z n) (hz n)
      (by simpa only [empirical_lyapunov_eq, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hΨ n) S k)
      atTop (𝓝 (NonlinearSkorokhodArray.pathLaw control hActivity ν S hCoupling hMoment k)) :=
  PopulationPathChaos.canonical_laws_tendsto control hActivity ν S hCoupling hMoment
    P z hz hex
    (by simpa only [empirical_lyapunov_eq, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hΨ) C
    (by simpa only [empirical_lyapunov_eq, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hbound) hconv k

/-- Proposition 7.5's convergence of all type means in l1, uniformly over
all real times on the horizon. This conclusion does not assume or assert the
separate closed ODE identification. -/
theorem vectorMean_limit (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (P.map (z n)) (Label (n + 1) D))
      {p | ENNReal.ofReal ε < PopulationCoordinateMoments.runningVectorError
        control hActivity ν T hT hCoupling hMoment n id p}) atTop (𝓝 0) :=
  PopulationCoordinateMoments.measure_runningVectorError_gt_tendsto_zero
    control hActivity ν T hT hCoupling hMoment P z hz hex
    (by simpa only [empirical_lyapunov_eq, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hΨ) C
    (by simpa only [empirical_lyapunov_eq, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hbound) hconv ε hε

end ManuscriptInitialization
end CarryingCapacity.LinearCarryingCapacityApplication
