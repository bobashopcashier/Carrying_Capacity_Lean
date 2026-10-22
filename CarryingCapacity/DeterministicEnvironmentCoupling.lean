import CarryingCapacity.CouplingExpectation
import CarryingCapacity.DeterministicEnvironmentEvolution
import CarryingCapacity.CoupledDistanceContinuity

/-!
# Moment bounds for the actual same-noise environment coupling

Two prescribed environments use the same initial record and marked noises in
the existing construction. Their actual expected distance and coupling
activity are finite. The exact manuscript hypotheses bound the latter by the
coefficient needed for the stochastic Volterra estimate.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace CarryingCapacity.DeterministicEnvironmentCoupling
open CommonInitialNoise LyapunovFlowSpace DeterministicEnvironmentLyapunov
open DeterministicEnvironmentProcess DeterministicEnvironmentLaw DeterministicEnvironmentRates

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T)
  (v w : ManuscriptCurves control.function ν (driftConstant control) T hT)

/-- Expected distance between the actual processes on their common sample space. -/
def meanDistance (s : ℝ) : ℝ :=
  ∫ p, adaptedDistance κ (manuscriptProcess control hActivity ν T hT v p s)
    (manuscriptProcess control hActivity ν T hT w p s) ∂law ν.measure (Jump D)

/-- The exact distance between the endpoint-extended input environments. -/
def inputDistance (s : ℝ) : ℝ :=
  wasserstein (manuscriptExtension control ν (driftConstant control) T hT v s)
    (manuscriptExtension control ν (driftConstant control) T hT w s)

/-- Expected positive-increment coupling activity at the actual current states. -/
def meanActivity (s : ℝ) : ℝ :=
  ∫ p, couplingActivity κ q (manuscriptProcess control hActivity ν T hT v p s)
    (manuscriptProcess control hActivity ν T hT w p s)
    (manuscriptExtension control ν (driftConstant control) T hT v s)
    (manuscriptExtension control ν (driftConstant control) T hT w s) ∂law ν.measure (Jump D)

omit hActivity w in
/-- Lyapunov domination controls every moment of the input environment. -/
theorem input_moment_le (s : ℝ) :
    moment (manuscriptExtension control ν (driftConstant control) T hT v s) ≤
      manuscriptBound control ν (driftConstant control) T := by
  obtain ⟨hi, hb⟩ := manuscriptExtension_integrable_and_bound control ν
    (driftConstant control) T (driftConstant_nonnegative control) hT v s
  apply le_trans _ hb
  exact integral_mono (manuscriptExtension control ν (driftConstant control) T hT v s).integrable_weight
    hi (fun x => by linarith [control.dominates x])

omit hActivity in
theorem continuous_inputDistance : Continuous (inputDistance control ν T hT v w) := by
  have h := (continuous_manuscriptExtension control ν (driftConstant control) T hT v).dist
    (continuous_manuscriptExtension control ν (driftConstant control) T hT w)
  simpa only [inputDistance, momentLaw_dist] using h

theorem meanDistance_nonnegative (s : ℝ) : 0 ≤ meanDistance control hActivity ν T hT v w s :=
  integral_nonneg (fun _ => adaptedDistance_nonneg κ _ _)

variable (hCoupling : MomentCouplingBound κ q)

/-- The exact finite-horizon scalar coefficient from the manuscript. -/
def coefficient : ℝ :=
  couplingConstant κ q hCoupling * (1 + 2 * manuscriptBound control ν (driftConstant control) T)

include hT in
omit hActivity v w in
theorem coefficient_nonnegative : 0 ≤ coefficient control ν T hCoupling :=
  mul_nonneg (couplingConstant_nonnegative κ q hCoupling)
    (by have h := manuscriptBound_nonnegative control ν (driftConstant control) T
          (driftConstant_nonnegative control) hT
        linarith)

include hCoupling

omit w in
/-- The actual expected state weight is bounded by the terminal envelope. -/
theorem mean_weight_le (s : ℝ) (hs : s ∈ Icc 0 T) :
    (∫ p, momentWeight κ (manuscriptProcess control hActivity ν T hT v p s)
      ∂law ν.measure (Jump D)) ≤ manuscriptBound control ν (driftConstant control) T := by
  have h := DeterministicEnvironmentEvolution.uniform_integral_lyapunov_bound
    control hActivity ν T hT v hCoupling ⟨s, hs⟩
  apply le_trans _ h
  exact integral_mono (integrable_weight_at control hActivity ν T hT v hCoupling s hs.1)
    (manuscript_integrable_lyapunov control hActivity ν T hT v hCoupling s hs.1)
    (fun p => by linarith [control.dominates (manuscriptProcess control hActivity ν T hT v p s)])

theorem integrable_distance_at (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun p => adaptedDistance κ (manuscriptProcess control hActivity ν T hT v p s)
      (manuscriptProcess control hActivity ν T hT w p s)) (law ν.measure (Jump D)) :=
  CouplingExpectation.integrable_distance κ (law ν.measure (Jump D)) _ _
    (measurable_at control hActivity ν T hT v hCoupling s)
    (measurable_at control hActivity ν T hT w hCoupling s)
    (integrable_weight_at control hActivity ν T hT v hCoupling s hs)
    (integrable_weight_at control hActivity ν T hT w hCoupling s hs)

/-- The expected distance is uniformly finite before any coupling estimate is used. -/
theorem meanDistance_le (s : ℝ) (hs : s ∈ Icc 0 T) :
    meanDistance control hActivity ν T hT v w s ≤
      2 * manuscriptBound control ν (driftConstant control) T := by
  have hv := integrable_weight_at control hActivity ν T hT v hCoupling s hs.1
  have hw := integrable_weight_at control hActivity ν T hT w hCoupling s hs.1
  calc
    _ ≤ ∫ p, momentWeight κ (manuscriptProcess control hActivity ν T hT v p s) +
        momentWeight κ (manuscriptProcess control hActivity ν T hT w p s) ∂law ν.measure (Jump D) :=
      integral_mono (integrable_distance_at control hActivity ν T hT v w hCoupling s hs.1)
        (hv.add hw) (fun p => adaptedDistance_le_weights _ _)
    _ ≤ _ := by
      rw [integral_add hv hw]
      linarith [mean_weight_le control hActivity ν T hT v hCoupling s hs,
        mean_weight_le control hActivity ν T hT w hCoupling s hs]

/-- The current-state activity has a genuine finite expectation. -/
theorem integrable_activity_at (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun p => couplingActivity κ q (manuscriptProcess control hActivity ν T hT v p s)
      (manuscriptProcess control hActivity ν T hT w p s)
      (manuscriptExtension control ν (driftConstant control) T hT v s)
      (manuscriptExtension control ν (driftConstant control) T hT w s)) (law ν.measure (Jump D)) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact CouplingExpectation.integrable_activity κ q hCoupling (law ν.measure (Jump D)) _ _
    (measurable_at control hActivity ν T hT v hCoupling s)
    (measurable_at control hActivity ν T hT w hCoupling s)
    (integrable_weight_at control hActivity ν T hT v hCoupling s hs)
    (integrable_weight_at control hActivity ν T hT w hCoupling s hs) _ _

/-- The stated pointwise coupling assumption yields the exact expected
activity bound using the proved input and output moment envelopes. -/
theorem meanActivity_le (s : ℝ) (hs : s ∈ Icc 0 T) :
    meanActivity control hActivity ν T hT v w s ≤ coefficient control ν T hCoupling *
      (meanDistance control hActivity ν T hT v w s + inputDistance control ν T hT v w s) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact CouplingExpectation.integral_activity_le_uniform κ q hCoupling (law ν.measure (Jump D)) _ _
    (measurable_at control hActivity ν T hT v hCoupling s)
    (measurable_at control hActivity ν T hT w hCoupling s)
    (integrable_weight_at control hActivity ν T hT v hCoupling s hs.1)
    (integrable_weight_at control hActivity ν T hT w hCoupling s hs.1) _ _
    (manuscriptBound control ν (driftConstant control) T)
    (input_moment_le control ν T hT v s) (input_moment_le control ν T hT w s)
    (mean_weight_le control hActivity ν T hT v hCoupling s hs)
    (mean_weight_le control hActivity ν T hT w hCoupling s hs)

/-- The two existing global constructions give an actual common-space
coupling of the output laws, so their expected distance bounds transport. -/
theorem output_distance_le (t : Icc (0 : ℝ) T) :
    wasserstein
      ((DeterministicEnvironmentEvolution.evolution control hActivity ν T hT v hCoupling).val t)
      ((DeterministicEnvironmentEvolution.evolution control hActivity ν T hT w hCoupling).val t) ≤
      meanDistance control hActivity ν T hT v w t := by
  exact LawCurveContinuity.wasserstein_le_integral_distance (law ν.measure (Jump D)) _ _
    (measurable_at control hActivity ν T hT v hCoupling t)
    (measurable_at control hActivity ν T hT w hCoupling t) _ _ rfl rfl

/-- Actual expected distance is continuous, by endpoint stochastic continuity
and superlinear uniform integrability. No continuity of sample paths at all
times simultaneously is asserted or needed. -/
theorem continuousOn_meanDistance :
    ContinuousOn (meanDistance control hActivity ν T hT v w) (Icc 0 T) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  apply continuousOn_iff_continuous_restrict.mpr
  exact CoupledDistanceContinuity.continuous_expected_distance (law ν.measure (Jump D))
    control.function control.dominates control.superlinear
    (fun (s : Icc (0 : ℝ) T) p => manuscriptProcess control hActivity ν T hT v p s)
    (fun (s : Icc (0 : ℝ) T) p => manuscriptProcess control hActivity ν T hT w p s)
    (fun s => measurable_at control hActivity ν T hT v hCoupling s)
    (fun s => measurable_at control hActivity ν T hT w hCoupling s)
    (fun s => manuscript_integrable_lyapunov control hActivity ν T hT v hCoupling s s.property.1)
    (fun s => manuscript_integrable_lyapunov control hActivity ν T hT w hCoupling s s.property.1)
    (manuscriptBound control ν (driftConstant control) T)
    (manuscriptBound_nonnegative control ν (driftConstant control) T (driftConstant_nonnegative control) hT)
    (DeterministicEnvironmentEvolution.uniform_integral_lyapunov_bound control hActivity ν T hT v hCoupling)
    (DeterministicEnvironmentEvolution.uniform_integral_lyapunov_bound control hActivity ν T hT w hCoupling)
    (DeterministicEnvironmentEvolution.ae_continuousAt_intervalProcess control hActivity ν T hT v hCoupling)
    (DeterministicEnvironmentEvolution.ae_continuousAt_intervalProcess control hActivity ν T hT w hCoupling)

end CarryingCapacity.DeterministicEnvironmentCoupling
