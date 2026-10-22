import CarryingCapacity.QuadraticRealLyapunov
import CarryingCapacity.PopulationEmpiricalLimit
import CarryingCapacity.NonlinearForwardUniqueness
import CarryingCapacity.PopulationPathChaos
import CarryingCapacity.PopulationSkorokhodLimit

/-!
# The second-moment feedback application

For every real `r > 2`, the actual model hypotheses are discharged by
`QuadraticRealLyapunov`. The canonical finite systems are nonexplosive; the
nonlinear flow exists uniquely in the genuine bounded-Ψ moment class; and the
manuscript initialization implies uniform empirical transport and second-moment
convergence. These are actual canonical constructions, not statements about
arbitrary externally supplied Poisson realizations.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.QuadraticFeedbackApplication
open ConfigurationLocalization CommonInitialNoise

variable (birth : ℝ) (hbirth : 0 ≤ birth) (a : MomentMortality) (r : ℝ) (hr : 2 < r)

local notation "control" => QuadraticRealLyapunov.lyapunovControl birth hbirth a r hr
local notation "hActivity" => QuadraticModel.activityBound birth hbirth a
local notation "hCoupling" => QuadraticModel.couplingBound birth hbirth a

/-- The empirical Lyapunov average is exactly the prescribed real `r` moment. -/
theorem empirical_lyapunov_eq {N : ℕ} (z : Configuration N 1) :
    lyapunov control z = (N : ℝ)⁻¹ * ∑ i, (1 + (z i 0 : ℝ) ^ r) := rfl

/-- The actual quadratic-feedback finite system has exhausting localization
exits, for every finite positive population and every integrable initial Ψ average. -/
theorem ae_nonexplosive {A : Type*} [MeasurableSpace A] {N : ℕ} (hN : 0 < N)
    (initial : A → Configuration N 1) (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial)
    (hV : Integrable (fun z => (N : ℝ)⁻¹ * ∑ i, (1 + (initial z i 0 : ℝ) ^ r)) μ) :
    ∀ᵐ p ∂law μ (Label N 1), ∀ S : ℝ≥0, ∃ n : ℕ,
      (S : ℝ≥0∞) < ConfigurationTimeDependent.exit control hN initial n p :=
  ConfigurationTimeDependent.ae_exhaustive control hN initial μ hinit hV

variable (ν : MomentLaw MomentScale.quadratic 1) (T : ℝ) (hT : 0 ≤ T)
  (hMoment : Integrable (fun x : State 1 => 1 + (x 0 : ℝ) ^ r) ν.measure)

/-- The actual nonlinear law curve for these untruncated second-moment rates. -/
def environment : ℝ → MomentLaw MomentScale.quadratic 1 :=
  NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment

/-- The constructed nonlinear curve solves the equation in the stated moment class. -/
theorem environment_isSolution : NonlinearForwardUniqueness.IsMomentBoundedSolution
    (fun x : State 1 => 1 + (x 0 : ℝ) ^ r) (QuadraticModel.rates birth hbirth a) ν T
    (environment birth hbirth a r hr ν T hT hMoment) :=
  NonlinearForwardUniqueness.environment_isSolution control hActivity ν T hT hCoupling hMoment

/-- Every other probability weak solution with a genuine bounded real-r
Lyapunov moment agrees on the entire horizon, without assumed continuity. -/
theorem solution_unique (v : ℝ → MomentLaw MomentScale.quadratic 1)
    (hv : NonlinearForwardUniqueness.IsMomentBoundedSolution
      (fun x : State 1 => 1 + (x 0 : ℝ) ^ r) (QuadraticModel.rates birth hbirth a) ν T v) :
    EqOn v (environment birth hbirth a r hr ν T hT hMoment) (Icc 0 T) :=
  NonlinearForwardUniqueness.solution_unique control hActivity ν T hT hCoupling hMoment
    v (environment birth hbirth a r hr ν T hT hMoment) hv
    (environment_isSolution birth hbirth a r hr ν T hT hMoment)

/-- Actual all-real-time empirical transport error on the fixed horizon. -/
def runningTransportError (n : ℕ)
    (p : Sample (Configuration (n + 1) 1) (Label (n + 1) 1)) : ℝ≥0∞ :=
  PopulationEmpiricalLimit.runningError control hActivity ν T hT hCoupling hMoment n id p

/-- Actual all-real-time absolute second-moment error on the fixed horizon. -/
def runningSecondMomentError (n : ℕ)
    (p : Sample (Configuration (n + 1) 1) (Label (n + 1) 1)) : ℝ≥0∞ :=
  PopulationEmpiricalLimit.runningMomentError control hActivity ν T hT hCoupling hMoment n id p

/-- The moment error really uses empirical squares and the nonlinear law's
second moment, not an auxiliary control moment. -/
theorem runningSecondMomentError_eq (n : ℕ)
    (p : Sample (Configuration (n + 1) 1) (Label (n + 1) 1)) :
    runningSecondMomentError birth hbirth a r hr ν T hT hMoment n p =
      SynchronousRunningSupremum.intervalSup (fun t => ENNReal.ofReal
        |(n + 1 : ℝ)⁻¹ * ∑ i : Fin (n + 1),
            ((ConfigurationTimeDependent.process control (Nat.succ_pos n) id p t) i 0 : ℝ)^2 -
          ∫ x : State 1, (x 0 : ℝ)^2 ∂(environment birth hbirth a r hr ν T hT hMoment t).measure|) T := by
  simp only [runningSecondMomentError, PopulationEmpiricalLimit.runningMomentError,
    quadratic_one_moment, integral_empiricalLaw, environment,
    FiniteGenerator.empiricalMean, Nat.cast_add, Nat.cast_one, Nat.cast_succ]

section ManuscriptInitialization
variable {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (z : ∀ n, Ω → Configuration (n + 1) 1) (hz : ∀ n, Measurable (z n))
  (hex : ∀ n, ExchangeableMatching.ExchangeableLaw (P.map (z n)))
  (hΨ : ∀ n : ℕ, Integrable (fun ω => (n + 1 : ℝ)⁻¹ *
    ∑ i : Fin (n + 1), (1 + (z n ω i 0 : ℝ) ^ r)) P)
  (C : ℝ) (hbound : ∀ n : ℕ, (∫ ω, (n + 1 : ℝ)⁻¹ *
    ∑ i : Fin (n + 1), (1 + (z n ω i 0 : ℝ) ^ r) ∂P) ≤ C)
  (hconv : TendstoInMeasure P (fun n ω =>
    wasserstein (empiricalLaw MomentScale.quadratic (Nat.succ_pos n) (z n ω)) ν) atTop 0)

include hz hex hΨ hbound hconv

/-- Corollary 7.8's uniform empirical transport limit, with every dynamic
hypothesis proved for the exact model and every real `r > 2`. -/
theorem transport_limit (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (P.map (z n)) (Label (n + 1) 1))
      {p | ENNReal.ofReal ε < runningTransportError birth hbirth a r hr ν T hT hMoment n p})
      atTop (𝓝 0) := by
  exact PopulationEmpiricalLimit.measure_runningError_gt_tendsto_zero
    control hActivity ν T hT hCoupling hMoment P z hz hex
    (by simpa only [empirical_lyapunov_eq, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hΨ) C
    (by simpa only [empirical_lyapunov_eq, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hbound) hconv ε hε

/-- Corollary 7.8's uniform second-moment feedback limit. -/
theorem secondMoment_limit (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (P.map (z n)) (Label (n + 1) 1))
      {p | ENNReal.ofReal ε < runningSecondMomentError birth hbirth a r hr ν T hT hMoment n p})
      atTop (𝓝 0) := by
  exact PopulationEmpiricalLimit.measure_runningMomentError_gt_tendsto_zero
    control hActivity ν T hT hCoupling hMoment P z hz hex
    (by simpa only [empirical_lyapunov_eq, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hΨ) C
    (by simpa only [empirical_lyapunov_eq, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hbound) hconv ε hε

/-- The actual empirical trajectory also converges in probability in the
manuscript's genuine transport-valued J1 path metric. -/
theorem empirical_J1_limit (S : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (P.map (z n)) (Label (n + 1) 1)).real
      {p | ε < dist
        (PopulationSkorokhodLimit.empiricalPath control S (Nat.succ_pos n) id p)
        (PopulationSkorokhodLimit.limitPath control S hActivity ν hCoupling hMoment)})
      atTop (𝓝 0) :=
  PopulationSkorokhodLimit.probability_distance_gt_tendsto_zero
    control S hActivity ν hCoupling hMoment P z hz hex
    (by simpa only [empirical_lyapunov_eq, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hΨ) C
    (by simpa only [empirical_lyapunov_eq, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hbound) hconv ε hε

/-- Focal path-space chaos in the single vector-valued J1 space carrying
the maximum quadratic adapted distance, for every fixed number of particles. -/
theorem focal_path_laws_tendsto (S : ℝ≥0) (k : ℕ) :
    Tendsto (fun n => PopulationPathChaos.canonicalLaw control (Nat.succ_pos n)
      P (z n) (hz n)
      (by simpa only [empirical_lyapunov_eq, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hΨ n) S k)
      atTop (𝓝 (NonlinearSkorokhodArray.pathLaw control hActivity ν S hCoupling hMoment k)) :=
  PopulationPathChaos.canonical_laws_tendsto control hActivity ν S hCoupling hMoment
    P z hz hex
    (by simpa only [empirical_lyapunov_eq, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hΨ) C
    (by simpa only [empirical_lyapunov_eq, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hbound) hconv k

end ManuscriptInitialization
end CarryingCapacity.QuadraticFeedbackApplication
