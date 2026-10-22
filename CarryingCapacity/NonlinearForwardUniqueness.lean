import CarryingCapacity.AtomicTransportContinuity
import CarryingCapacity.DeterministicEnvironmentGeneralCoupling
import CarryingCapacity.IntegralGronwall

/-!
# Nonlinear forward uniqueness in the full moment-bounded class

A candidate supplies only its finite-support weak equation, genuine tested
time integrability, and a uniform genuine Lyapunov bound. Atomic continuity
and uniform truncation tails derive transport continuity. Linear uniqueness
then identifies the candidate with the actual prescribed-environment process.
The two actual processes can be synchronously coupled, so Gronwall proves
uniqueness without first assuming the sharper invariant envelope. Equality
with the constructed fixed curve subsequently proves that exact envelope.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace CarryingCapacity.NonlinearForwardUniqueness
open LyapunovFlowSpace DeterministicEnvironmentLyapunov
open DeterministicEnvironmentGeneralCoupling

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}

/-- The paper's broad candidate class. Continuity and the specific
exponential envelope are conclusions, not fields of this definition. -/
def IsMomentBoundedSolution (Ψ : State D → ℝ) (q : Rates D (MomentLaw κ D))
    (ν : MomentLaw κ D) (T : ℝ) (v : ℝ → MomentLaw κ D) : Prop :=
  FiniteJumpForward.IsSolution Jump.advance (fun j s x => q.rate j x (v s))
    ν.measure (fun s => (v s).measure) T ∧
  ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Icc 0 T, lyapunovIntegral Ψ (v s) ≤ ENNReal.ofReal B

variable (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hInitial : Integrable control.function ν.measure)

omit hActivity hCoupling hInitial in
include hT in
/-- Transport continuity is forced by the defining weak equation and
uniform genuine superlinear moments, with no coefficient regularity premise. -/
theorem continuousOn_solution (v : ℝ → MomentLaw κ D)
    (hv : IsMomentBoundedSolution control.function q ν T v) : ContinuousOn v (Icc 0 T) := by
  obtain ⟨B, hB, hb⟩ := hv.2
  exact AtomicTransportContinuity.continuousOn_of_isSolution control.function control.dominates
    control.superlinear q ν v T hT B hB hb hv.1

include hActivity hCoupling hInitial hT

/-- Every two moment-bounded probability weak solutions coincide on the
whole horizon. Their continuity, actual realizations and coupling estimate
are all derived before applying Gronwall. -/
theorem solution_unique (v w : ℝ → MomentLaw κ D)
    (hv : IsMomentBoundedSolution control.function q ν T v)
    (hw : IsMomentBoundedSolution control.function q ν T w) : EqOn v w (Icc 0 T) := by
  obtain ⟨Bv, hBv, hEnvV⟩ := hv.2
  obtain ⟨Bw, _hBw, hEnvW⟩ := hw.2
  let B := max Bv Bw
  have hB : 0 ≤ B := hBv.trans (le_max_left _ _)
  have hEV (s : ℝ) (hs : s ∈ Icc 0 T) :
      lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B :=
    (hEnvV s hs).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hEW (s : ℝ) (hs : s ∈ Icc 0 T) :
      lyapunovIntegral control.function (w s) ≤ ENNReal.ofReal B :=
    (hEnvW s hs).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  have hvc := continuousOn_solution control ν T hT v hv
  have hwc := continuousOn_solution control ν T hT w hw
  let U := meanDistance control hActivity ν v w T hT hvc hwc
  let A := coefficient hCoupling B
  have hA : 0 ≤ A := coefficient_nonnegative hCoupling B hB
  have hU : ContinuousOn U (Icc 0 T) :=
    continuousOn_meanDistance control hActivity ν v w T hT hvc hwc hCoupling B hB
      hEV hEW hInitial hv.1 hw.1
  have hd : ContinuousOn (fun s => wasserstein (v s) (w s)) (Icc 0 T) := by
    simpa only [momentLaw_dist] using continuous_dist.comp_continuousOn (hvc.prodMk hwc)
  have hdist (s : ℝ) (hs : s ∈ Icc 0 T) : wasserstein (v s) (w s) ≤ U s :=
    input_distance_le control hActivity ν v w T hT hvc hwc hCoupling B hB
      hEV hEW hInitial hv.1 hw.1 s hs
  have hi (t : ℝ) (ht : t ∈ Icc 0 T) :
      U t ≤ 0 + (2 * A) * ∫ s in Ioc 0 t, U s := by
    have huInt : IntegrableOn U (Ioc 0 t) :=
      (hU.integrableOn_Icc (μ := volume)).mono_set
        (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2))
    have hdInt : IntegrableOn (fun s => wasserstein (v s) (w s)) (Ioc 0 t) :=
      (hd.integrableOn_Icc (μ := volume)).mono_set
        (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2))
    have hmono : (∫ s in Ioc 0 t, U s + wasserstein (v s) (w s)) ≤
        ∫ s in Ioc 0 t, 2 * U s :=
      integral_mono_ae (huInt.add hdInt) (huInt.const_mul 2) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        have hh := hdist s ⟨hs.1.le, hs.2.trans ht.2⟩
        linarith)
    have hst := meanDistance_integral_inequality control hActivity ν v w T hT hvc hwc
      hCoupling B hB hEV hEW hInitial hv.1 hw.1 t ht
    calc
      U t ≤ A * ∫ s in Ioc 0 t, U s + wasserstein (v s) (w s) := hst
      _ ≤ A * ∫ s in Ioc 0 t, 2 * U s := mul_le_mul_of_nonneg_left hmono hA
      _ = _ := by rw [integral_const_mul]; ring
  have hz := IntegralGronwall.le_exp_mul_of_setIntegral hT hU
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA) hi
  intro t ht
  apply (wasserstein_eq_zero_iff (v t) (w t)).mp
  apply le_antisymm _ (wasserstein_nonneg _ _)
  have hu0 := hz t ht
  simp only [zero_mul] at hu0
  exact (hdist t ht).trans hu0

/-- The already constructed canonical environment belongs to the broad
candidate class and supplies actual existence. -/
theorem environment_isSolution : IsMomentBoundedSolution control.function q ν T
    (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hInitial) := by
  refine ⟨DeterministicEnvironmentForward.nonlinear_isSolution control hActivity ν T hT
    hCoupling hInitial, manuscriptBound control ν (driftConstant control) T, ?_, ?_⟩
  · exact manuscriptBound_nonnegative control ν (driftConstant control) T
      (driftConstant_nonnegative control) hT
  · intro s _
    exact manuscriptExtension_bound control ν (driftConstant control) T
      (driftConstant_nonnegative control) hT
      (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hInitial) s

/-- Identification of every broad weak solution with the actual canonical
fixed law, with no continuity or envelope premise on that solution. -/
theorem solution_eq_environment (v : ℝ → MomentLaw κ D)
    (hv : IsMomentBoundedSolution control.function q ν T v) :
    EqOn v (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hInitial) (Icc 0 T) :=
  solution_unique control hActivity ν T hT hCoupling hInitial v _ hv
    (environment_isSolution control hActivity ν T hT hCoupling hInitial)

/-- The manuscript's exact exponential Lyapunov envelope is now a
consequence for every moment-bounded weak solution. -/
theorem solution_envelope (v : ℝ → MomentLaw κ D)
    (hv : IsMomentBoundedSolution control.function q ν T v)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    lyapunovIntegral control.function (v t) ≤
      ENNReal.ofReal (exponentialEnvelope (∫ x, control.function x ∂ν.measure)
        (driftConstant control) t) := by
  rw [solution_eq_environment control hActivity ν T hT hCoupling hInitial v hv ht]
  unfold NonlinearFixedPoint.environment
  rw [manuscriptExtension_eq control ν (driftConstant control) T hT _ ⟨t, ht⟩]
  exact (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hInitial).property.2 ⟨t, ht⟩

/-- Existence and uniqueness on the specified interval for the full
moment-bounded weak-solution class. Real-line extensions outside the interval
are intentionally not identified. -/
theorem exists_solution_and_unique :
    ∃ v : ℝ → MomentLaw κ D, IsMomentBoundedSolution control.function q ν T v ∧
      ∀ w : ℝ → MomentLaw κ D, IsMomentBoundedSolution control.function q ν T w →
        EqOn w v (Icc 0 T) :=
  ⟨NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hInitial,
    environment_isSolution control hActivity ν T hT hCoupling hInitial,
    fun w hw => solution_eq_environment control hActivity ν T hT hCoupling hInitial w hw⟩

/-- On the actual interval domain, existence and uniqueness are an exact
unique-existence statement. The quantified candidates are arbitrary law
functions; their transport continuity and sharp moment envelope are derived. -/
theorem existsUnique_interval_solution :
    ∃! v : Icc (0 : ℝ) T → MomentLaw κ D,
      IsMomentBoundedSolution control.function q ν T (fun s => v (clampPoint T hT s)) := by
  refine ⟨fun t => (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hInitial).val t,
    environment_isSolution control hActivity ν T hT hCoupling hInitial, ?_⟩
  intro w hw
  funext t
  have he := solution_eq_environment control hActivity ν T hT hCoupling hInitial
    (fun s => w (clampPoint T hT s)) hw t.property
  have hc : clampPoint T hT t = t := by
    apply Subtype.ext
    exact (congrArg (max 0) (min_eq_left t.property.2)).trans (max_eq_right t.property.1)
  change w (clampPoint T hT t) = _ at he
  rw [hc] at he
  exact he.trans (manuscriptExtension_eq control ν (driftConstant control) T hT
    (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hInitial) t)

end CarryingCapacity.NonlinearForwardUniqueness
