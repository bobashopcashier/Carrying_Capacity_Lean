import CarryingCapacity.LinearCarryingCapacityApplication
import CarryingCapacity.QuadraticFeedbackApplication
import CarryingCapacity.PrescribedConfigurationProcess
import CarryingCapacity.PrescribedPopulationLimits
import CarryingCapacity.MainTheorem

/-!
# The assembled carrying-capacity model corollaries

The model hypotheses are verified for arbitrary real Lyapunov exponents,
`p > 1` for vector-mean feedback and `r > 2` for quadratic feedback. The
conclusions below concern the actual processes on the supplied Poisson space.
The quadratic feedback error is explicitly the empirical average of squares,
not the higher Lyapunov moment used to control the process.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.ModelCorollaries
open ConfigurationLocalization

section LinearFeedback

variable {D : ℕ} (c : LinearCarryingCapacity.Coefficients D)
  (p : ℝ) (hp : 1 < p) (ν : MomentLaw MomentScale.linear D) (T : ℝ≥0)
  (hMoment : Integrable (fun x : State D => 1 + populationSize x ^ p) ν.measure)
  {Ω : Type*} [MeasurableSpace Ω]
  (M : ∀ n, Label (n + 1) D → Ω → Measure (ℝ × ℝ))
  (z : ∀ n, Ω → Configuration (n + 1) D)
  (P : Measure Ω) [IsProbabilityMeasure P]
  (hM : ∀ n j, Measurable (M n j))
  (hPoisson : ∀ n, PoissonObservationLaw.HasDisjointLaws P (Label (n + 1) D) (M n))
  (hz : ∀ n, Measurable (z n))
  (hIndependent : ∀ n, IndepFun (z n) (fun ω j => M n j ω) P)
  (hΨ : ∀ n : ℕ, Integrable (fun ω => (n + 1 : ℝ)⁻¹ *
    ∑ i : Fin (n + 1), (1 + populationSize (z n ω i) ^ p)) P)
  (hex : ∀ n, ExchangeableMatching.ExchangeableLaw (P.map (z n)))
  (C : ℝ) (hbound : ∀ n : ℕ, (∫ ω, (n + 1 : ℝ)⁻¹ *
    ∑ i : Fin (n + 1), (1 + populationSize (z n ω i) ^ p) ∂P) ≤ C)
  (hconv : TendstoInMeasure P (fun n ω =>
    wasserstein (empiricalLaw MomentScale.linear (Nat.succ_pos n) (z n ω)) ν) atTop 0)

local notation "control" => LinearCarryingCapacity.lyapunovControl c p hp
local notation "hActivity" => LinearCarryingCapacityHypotheses.activityBound c
local notation "hCoupling" => LinearCarryingCapacityHypotheses.couplingBound c

include hex hbound hconv

/-- Corollary 7.4, with all four clauses assembled on the supplied Poisson
space. The conclusion includes actual strong nonexplosive finite systems,
the unique continuous nonlinear forward solution in its Lyapunov class,
uniform empirical convergence and empirical J1 convergence, and focal vector
J1 path chaos with independent nonlinear limit coordinates. Every dynamic
hypothesis is discharged for the exact model and the arbitrary real `p > 1`. -/
theorem corollary_7_4 :
    MainTheorem.Conclusions control hActivity ν T hCoupling hMoment M z P
      hM hPoisson hz hIndependent
      (by simpa only [LinearCarryingCapacityApplication.empirical_lyapunov_eq,
        Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hΨ) := by
  apply MainTheorem.main_theorem control hActivity ν T hCoupling hMoment
    M z P hM hPoisson hz hIndependent _ hex C _ hconv
  simpa only [LinearCarryingCapacityApplication.empirical_lyapunov_eq,
    Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hbound

end LinearFeedback

section QuadraticFeedback

variable (birth : ℝ) (hbirth : 0 ≤ birth) (a : MomentMortality)
  (r : ℝ) (hr : 2 < r) (ν : MomentLaw MomentScale.quadratic 1) (T : ℝ≥0)
  (hMoment : Integrable (fun x : State 1 => 1 + (x 0 : ℝ) ^ r) ν.measure)
  {Ω : Type*} [MeasurableSpace Ω]
  (M : ∀ n, Label (n + 1) 1 → Ω → Measure (ℝ × ℝ))
  (z : ∀ n, Ω → Configuration (n + 1) 1)

local notation "control" => QuadraticRealLyapunov.lyapunovControl birth hbirth a r hr
local notation "hActivity" => QuadraticModel.activityBound birth hbirth a
local notation "hCoupling" => QuadraticModel.couplingBound birth hbirth a

/-- The exact all-real-time second-moment error in Corollary 7.8, on the
original probability space carrying the supplied initial vectors and PRMs. -/
def quadraticSecondMomentError (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  SynchronousRunningSupremum.intervalSup (fun t => ENNReal.ofReal
    |(n + 1 : ℝ)⁻¹ * ∑ i : Fin (n + 1),
        ((PrescribedConfigurationProcess.process control (Nat.succ_pos n) id
          (M n) (z n) ω t) i 0 : ℝ) ^ 2 -
      ∫ x : State 1, (x 0 : ℝ) ^ 2
        ∂(QuadraticFeedbackApplication.environment birth hbirth a r hr
          ν T T.coe_nonneg hMoment t).measure|) T

omit [MeasurableSpace Ω] in
/-- The explicit squares error is precisely the generalized-moment error
whose uniform convergence has already been proved for supplied inputs. -/
theorem quadraticSecondMomentError_eq (n : ℕ) (ω : Ω) :
    quadraticSecondMomentError birth hbirth a r hr ν T hMoment M z n ω =
      PrescribedPopulationLimits.runningMomentError control hActivity ν T T.coe_nonneg
        hCoupling hMoment M z n ω := by
  exact (QuadraticFeedbackApplication.runningSecondMomentError_eq
    birth hbirth a r hr ν T T.coe_nonneg hMoment n
    (PrescribedPoissonRealization.record (Label (n + 1) 1) (M n) (z n) ω)).symm

variable (P : Measure Ω) [IsProbabilityMeasure P]
  (hM : ∀ n j, Measurable (M n j))
  (hPoisson : ∀ n, PoissonObservationLaw.HasDisjointLaws P (Label (n + 1) 1) (M n))
  (hz : ∀ n, Measurable (z n))
  (hIndependent : ∀ n, IndepFun (z n) (fun ω j => M n j ω) P)
  (hΨ : ∀ n : ℕ, Integrable (fun ω => (n + 1 : ℝ)⁻¹ *
    ∑ i : Fin (n + 1), (1 + (z n ω i 0 : ℝ) ^ r)) P)
  (hex : ∀ n, ExchangeableMatching.ExchangeableLaw (P.map (z n)))
  (C : ℝ) (hbound : ∀ n : ℕ, (∫ ω, (n + 1 : ℝ)⁻¹ *
    ∑ i : Fin (n + 1), (1 + (z n ω i 0 : ℝ) ^ r) ∂P) ≤ C)
  (hconv : TendstoInMeasure P (fun n ω =>
    wasserstein (empiricalLaw MomentScale.quadratic (Nat.succ_pos n) (z n ω)) ν) atTop 0)

include hM hPoisson hz hIndependent hΨ hex hbound hconv

/-- Corollary 7.8, assembled for every real `r > 2`: all conclusions of
Theorem 2.7 hold on the supplied probability space, and the actual empirical
second-moment feedback converges uniformly over all times in `[0,T]`. -/
theorem corollary_7_8 :
    MainTheorem.Conclusions control hActivity ν T hCoupling hMoment M z P
      hM hPoisson hz hIndependent
      (by simpa only [QuadraticFeedbackApplication.empirical_lyapunov_eq,
        Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hΨ) ∧
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n => P {ω | ENNReal.ofReal ε <
      quadraticSecondMomentError birth hbirth a r hr ν T hMoment M z n ω})
      atTop (𝓝 0) := by
  have hΨ' : ∀ n, Integrable (fun ω => lyapunov control (z n ω)) P := by
    simpa only [QuadraticFeedbackApplication.empirical_lyapunov_eq,
      Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hΨ
  have hbound' : ∀ n, (∫ ω, lyapunov control (z n ω) ∂P) ≤ C := by
    simpa only [QuadraticFeedbackApplication.empirical_lyapunov_eq,
      Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hbound
  refine ⟨MainTheorem.main_theorem control hActivity ν T hCoupling hMoment
    M z P hM hPoisson hz hIndependent hΨ' hex C hbound' hconv, ?_⟩
  intro ε hε
  simpa only [quadraticSecondMomentError_eq] using
    PrescribedPopulationLimits.measure_runningMomentError_gt_tendsto_zero
      control hActivity ν T T.coe_nonneg hCoupling hMoment
      M z P hM hPoisson hz hIndependent hΨ' hex C hbound' hconv ε hε

end QuadraticFeedback
end CarryingCapacity.ModelCorollaries
