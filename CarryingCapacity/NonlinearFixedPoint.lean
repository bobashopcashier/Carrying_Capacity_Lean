import CarryingCapacity.DeterministicEnvironmentVolterra
import CarryingCapacity.BieleckiFlowSpace

/-!
# The actual nonlinear fixed curve and its common-noise realization

The previously constructed evolution satisfies the proved synchronous Volterra
estimate. With Bielecki weight `2*A+1` it therefore has exactly one fixed curve
in the manuscript's complete Lyapunov curve space. The only initialization
assumption is a genuine finite Lyapunov moment.

The canonical realization is the existing strong prescribed-environment
construction evaluated at this fixed curve. Its marginals equal that curve on
the construction interval. After that interval the environment is held at its
endpoint; self-consistency is claimed only on `[0,T]`. The subsequent
`NonlinearForwardUniqueness` and population-limit modules prove the full
forward uniqueness and mean-field conclusions; `MainTheorem` assembles them.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace CarryingCapacity.NonlinearFixedPoint
open CommonInitialNoise LyapunovFlowSpace BieleckiFlowSpace
open DeterministicEnvironmentLyapunov DeterministicEnvironmentCoupling

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)

/-- A concrete Bielecki weight strictly larger than twice the proved
synchronous coefficient, including the zero-coefficient case. -/
def bieleckiWeight : ℝ≥0 :=
  ⟨2 * coefficient control ν T hCoupling + 1, by
    have h := coefficient_nonnegative control ν T hT hCoupling
    linarith⟩

theorem twice_coefficient_lt_weight :
    2 * coefficient control ν T hCoupling <
      (bieleckiWeight control ν T hT hCoupling : ℝ) := by
  change 2 * coefficient control ν T hCoupling < 2 * coefficient control ν T hCoupling + 1
  linarith

/-- The actual stochastic evolution, equipped with the Bielecki metric. -/
def bieleckiEvolution :
    BieleckiCurves control.function ν (driftConstant control) T hT (bieleckiWeight control ν T hT hCoupling) →
    BieleckiCurves control.function ν (driftConstant control) T hT (bieleckiWeight control ν T hT hCoupling) :=
  fun v => ⟨DeterministicEnvironmentEvolution.evolution control hActivity ν T hT v.toCurve hCoupling⟩

omit hActivity hCoupling in
/-- The two continuous endpoint extensions have the same distance on the
original interval, which is all the Volterra integral uses. -/
theorem inputDistance_eq_extended
    (v w : ManuscriptCurves control.function ν (driftConstant control) T hT)
    (s : ℝ) (hs : s ∈ Icc 0 T) :
    inputDistance control ν T hT v w s =
      wasserstein (extendedCurve v s) (extendedCurve w s) := by
  have hv := manuscriptExtension_eq control ν (driftConstant control) T hT v ⟨s, hs⟩
  have hw := manuscriptExtension_eq control ν (driftConstant control) T hT w ⟨s, hs⟩
  have hv' := extendedCurve_on_interval v ⟨s, hs⟩
  have hw' := extendedCurve_on_interval w ⟨s, hs⟩
  change wasserstein (manuscriptExtension control ν (driftConstant control) T hT v s)
    (manuscriptExtension control ν (driftConstant control) T hT w s) = _
  rw [hv, hw, hv', hw']

/-- The actual evolution satisfies the precise hypothesis of the checked
Bielecki contraction theorem. The stochastic Volterra estimate is proved,
not supplied as a new assumption. -/
theorem bieleckiEvolution_volterra
    (v w : BieleckiCurves control.function ν (driftConstant control) T hT
      (bieleckiWeight control ν T hT hCoupling)) (t : Icc (0 : ℝ) T) :
    wasserstein ((bieleckiEvolution control hActivity ν T hT hCoupling v).toCurve.val t)
      ((bieleckiEvolution control hActivity ν T hT hCoupling w).toCurve.val t) ≤
      coefficient control ν T hCoupling *
        ∫ s in (0 : ℝ)..t.val, Real.exp (coefficient control ν T hCoupling * (t.val - s)) *
          wasserstein (extendedCurve v.toCurve s) (extendedCurve w.toCurve s) := by
  have h := DeterministicEnvironmentVolterra.output_distance_le_volterra
    control hActivity ν T hT v.toCurve w.toCurve hCoupling t
  have he : (∫ s in (0 : ℝ)..t.val,
      Real.exp (coefficient control ν T hCoupling * (t.val - s)) *
        inputDistance control ν T hT v.toCurve w.toCurve s) =
      ∫ s in (0 : ℝ)..t.val, Real.exp (coefficient control ν T hCoupling * (t.val - s)) *
        wasserstein (extendedCurve v.toCurve s) (extendedCurve w.toCurve s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.property.1] at hs
    dsimp only
    rw [inputDistance_eq_extended control ν T hT v.toCurve w.toCurve s
      ⟨hs.1, hs.2.trans t.property.2⟩]
  exact h.trans_eq (congrArg (fun z => coefficient control ν T hCoupling * z) he)

/-- The constructed evolution has exactly one fixed curve under the paper's
rate assumptions and original genuine finite-Lyapunov-moment initialization. -/
theorem existsUnique_fixedCurve (hInitial : Integrable control.function ν.measure) :
    ∃! v : ManuscriptCurves control.function ν (driftConstant control) T hT,
      DeterministicEnvironmentEvolution.evolution control hActivity ν T hT v hCoupling = v := by
  obtain ⟨v, hv, hunique⟩ := existsUnique_fixedPoint_of_volterra
    (bieleckiWeight control ν T hT hCoupling) (function_nonnegative control) hInitial
    (driftConstant_nonnegative control) (coefficient_nonnegative control ν T hT hCoupling)
    (twice_coefficient_lt_weight control ν T hT hCoupling)
    (bieleckiEvolution control hActivity ν T hT hCoupling)
    (bieleckiEvolution_volterra control hActivity ν T hT hCoupling)
  refine ⟨v.toCurve, congrArg BieleckiCurves.toCurve hv, ?_⟩
  intro w hw
  have hw' : bieleckiEvolution control hActivity ν T hT hCoupling ⟨w⟩ = ⟨w⟩ :=
    BieleckiCurves.ext hw
  exact congrArg BieleckiCurves.toCurve (hunique ⟨w⟩ hw')

variable (hInitial : Integrable control.function ν.measure)

/-- The canonical fixed curve, selected from the proved existence theorem. -/
def fixedCurve : ManuscriptCurves control.function ν (driftConstant control) T hT :=
  Classical.choose (existsUnique_fixedCurve control hActivity ν T hT hCoupling hInitial)

theorem fixedCurve_fixed :
    DeterministicEnvironmentEvolution.evolution control hActivity ν T hT
      (fixedCurve control hActivity ν T hT hCoupling hInitial) hCoupling =
      fixedCurve control hActivity ν T hT hCoupling hInitial :=
  (Classical.choose_spec (existsUnique_fixedCurve control hActivity ν T hT hCoupling hInitial)).1

theorem fixedCurve_unique
    (v : ManuscriptCurves control.function ν (driftConstant control) T hT)
    (hv : DeterministicEnvironmentEvolution.evolution control hActivity ν T hT v hCoupling = v) :
    v = fixedCurve control hActivity ν T hT hCoupling hInitial :=
  (Classical.choose_spec (existsUnique_fixedCurve control hActivity ν T hT hCoupling hInitial)).2 v hv

/-- The strong common-noise realization at the actual fixed environment. -/
def process (p : Sample (State D) (Jump D)) (t : ℝ) : State D :=
  DeterministicEnvironmentProcess.manuscriptProcess control hActivity ν T hT
    (fixedCurve control hActivity ν T hT hCoupling hInitial) p t

/-- Exact self-consistency: the fixed law curve is the actual marginal of
the constructed process, at every time in the original interval. -/
theorem process_marginal (t : Icc (0 : ℝ) T) :
    (law ν.measure (Jump D)).map (fun p => process control hActivity ν T hT hCoupling hInitial p t) =
      ((fixedCurve control hActivity ν T hT hCoupling hInitial).val t).measure := by
  have h := DeterministicEnvironmentEvolution.evolution_measure control hActivity ν T hT
    (fixedCurve control hActivity ν T hT hCoupling hInitial) hCoupling t
  rw [fixedCurve_fixed] at h
  exact h.symm

theorem measurable_process : Measurable
    (fun p : Sample (State D) (Jump D) × ℝ => process control hActivity ν T hT hCoupling hInitial p.1 p.2) :=
  DeterministicEnvironmentProcess.measurable_manuscriptProcess control hActivity ν T hT
    (fixedCurve control hActivity ν T hT hCoupling hInitial) hCoupling

/-- The canonical process retains the prescribed initial law exactly. -/
theorem process_initial_law :
    (law ν.measure (Jump D)).map (fun p => process control hActivity ν T hT hCoupling hInitial p 0) = ν.measure :=
  DeterministicEnvironmentProcess.manuscript_initial_law control hActivity ν T hT
    (fixedCurve control hActivity ν T hT hCoupling hInitial)

/-- The canonical realization has a genuine finite Lyapunov moment and
the manuscript's exact deterministic envelope throughout `[0,T]`. -/
theorem process_moment_bounds (t : ℝ) (ht : t ∈ Icc 0 T) :
    Integrable (fun p => control.function (process control hActivity ν T hT hCoupling hInitial p t))
      (law ν.measure (Jump D)) ∧
    (∫ p, control.function (process control hActivity ν T hT hCoupling hInitial p t)
      ∂law ν.measure (Jump D)) ≤
      exponentialEnvelope (∫ x, control.function x ∂ν.measure) (driftConstant control) t ∧
    (∫⁻ p, ENNReal.ofReal (control.function (process control hActivity ν T hT hCoupling hInitial p t))
      ∂law ν.measure (Jump D)) ≤
      ENNReal.ofReal (exponentialEnvelope (∫ x, control.function x ∂ν.measure)
        (driftConstant control) t) :=
  DeterministicEnvironmentEnvelope.manuscript_moment_bounds control hActivity ν T hT
    (fixedCurve control hActivity ν T hT hCoupling hInitial) hCoupling t ht

/-- The realized process is càdlàg; this property comes from genuine spatial
localization exhaustion, not from the abstract fixed-point theorem alone. -/
theorem ae_process_cadlag : ∀ᵐ p ∂law ν.measure (Jump D),
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt
      (process control hActivity ν T hT hCoupling hInitial p) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : State D, Tendsto
      (process control hActivity ν T hT hCoupling hInitial p) (𝓝[<] t) (𝓝 y)) :=
  DeterministicEnvironmentProcess.manuscript_cadlag control hActivity ν T hT
    (fixedCurve control hActivity ν T hT hCoupling hInitial) hCoupling

/-- The deterministic environment is the fixed curve on `[0,T]` and is
held at the nearest endpoint outside the interval. -/
def environment (t : ℝ) : MomentLaw κ D :=
  manuscriptExtension control ν (driftConstant control) T hT
    (fixedCurve control hActivity ν T hT hCoupling hInitial) t

theorem continuous_environment : Continuous (environment control hActivity ν T hT hCoupling hInitial) :=
  continuous_manuscriptExtension control ν (driftConstant control) T hT
    (fixedCurve control hActivity ν T hT hCoupling hInitial)

/-- In the original interval the environment used in the rate threshold is
the actual current marginal measure of this same realized process. -/
theorem environment_measure_eq_marginal (t : Icc (0 : ℝ) T) :
    (environment control hActivity ν T hT hCoupling hInitial t).measure =
      (law ν.measure (Jump D)).map (fun p => process control hActivity ν T hT hCoupling hInitial p t) := by
  unfold environment
  rw [manuscriptExtension_eq]
  exact (process_marginal control hActivity ν T hT hCoupling hInitial t).symm

/-- The canonical realization is adapted to its actual initial-plus-noise
filtration and uses no additional random input. -/
theorem adapted_process : Adapted (filtration (State D) (Jump D))
    (fun t p => process control hActivity ν T hT hCoupling hInitial p t) :=
  DeterministicEnvironmentProcess.adapted_process control hActivity
    (environment control hActivity ν T hT hCoupling hInitial) T hT
    (continuous_environment control hActivity ν T hT hCoupling hInitial).continuousOn
    id hCoupling measurable_id

/-- Genuine canonical exits of the realized nonlinear curve process. -/
def exit (n : ℕ) (p : Sample (State D) (Jump D)) : ℝ≥0∞ :=
  DeterministicEnvironmentProcess.manuscriptExit control hActivity ν T hT
    (fixedCurve control hActivity ν T hT hCoupling hInitial) n p

/-- The realization is genuinely nonexplosive on every finite horizon,
with its chosen fixed environment kept constant after `T`. -/
theorem ae_exhaustive : ∀ᵐ p ∂law ν.measure (Jump D), ∀ S : ℝ≥0, ∃ n,
    (S : ℝ≥0∞) < exit control hActivity ν T hT hCoupling hInitial n p :=
  DeterministicEnvironmentProcess.manuscript_exhaustive control hActivity ν T hT
    (fixedCurve control hActivity ν T hT hCoupling hInitial) hCoupling

/-- The actual predictable strict-past state used by the counting equation. -/
def preState (p : Sample (State D) (Jump D)) (t : ℝ) : State D :=
  DeterministicEnvironmentProcess.preState control hActivity
    (environment control hActivity ν T hT hCoupling hInitial) T hT
    (continuous_environment control hActivity ν T hT hCoupling hInitial).continuousOn id p t

/-- This predictable state is the realized path's actual left limit, on one
event simultaneously for every positive time. -/
theorem ae_preState_eq_leftLim : ∀ᵐ p ∂law ν.measure (Jump D), ∀ t : ℝ, 0 < t →
    preState control hActivity ν T hT hCoupling hInitial p t =
      Function.leftLim (process control hActivity ν T hT hCoupling hInitial p) t := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact DeterministicEnvironmentProcess.ae_preState_eq_leftLim control hActivity
    (environment control hActivity ν T hT hCoupling hInitial) T hT
    (continuous_environment control hActivity ν T hT hCoupling hInitial).continuousOn id ν.measure
    hCoupling measurable_id (manuscriptBound control ν (driftConstant control) T)
    (manuscriptBound_nonnegative control ν (driftConstant control) T (driftConstant_nonnegative control) hT)
    (fun s _ => manuscriptExtension_bound control ν (driftConstant control) T
      (driftConstant_nonnegative control) hT (fixedCurve control hActivity ν T hT hCoupling hInitial) s)
    hInitial

/-- The realized process solves the actual no-cutoff counting equation with
its own marginal environment on the construction interval. The previous
theorem identifies its predictable state with the actual path left limit. -/
theorem ae_counting_identity (f : State D → ℝ) : ∀ᵐ p ∂law ν.measure (Jump D),
    ∀ S : ℝ≥0, (S : ℝ) ≤ T →
      f (process control hActivity ν T hT hCoupling hInitial p S) - f p.1 =
        ∑ j, ∫ z : ℝ × ℝ,
          (if z.1 ∈ Ioc 0 (S : ℝ) ∧ z.2 ≤ q.rate j
              (preState control hActivity ν T hT hCoupling hInitial p z.1)
              (environment control hActivity ν T hT hCoupling hInitial z.1)
          then f (Jump.advance j (preState control hActivity ν T hT hCoupling hInitial p z.1)) -
            f (preState control hActivity ν T hT hCoupling hInitial p z.1) else 0)
          ∂MarkedNoise.countingMeasure j p.2 := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact DeterministicEnvironmentProcess.ae_counting_identity_on_horizon control hActivity
    (environment control hActivity ν T hT hCoupling hInitial) T hT
    (continuous_environment control hActivity ν T hT hCoupling hInitial).continuousOn id ν.measure
    hCoupling measurable_id (manuscriptBound control ν (driftConstant control) T)
    (manuscriptBound_nonnegative control ν (driftConstant control) T (driftConstant_nonnegative control) hT)
    (fun s _ => manuscriptExtension_bound control ν (driftConstant control) T
      (driftConstant_nonnegative control) hT (fixedCurve control hActivity ν T hT hCoupling hInitial) s)
    hInitial f

end CarryingCapacity.NonlinearFixedPoint
