import CarryingCapacity.NonlinearParticleArray

/-!
# Counting equations for the endpoint-held nonlinear particle array

The canonical process is defined on all nonnegative times, with its environment
held at the selected horizon's endpoint. These are genuine all-horizon counting
equations for that continuation. Self-consistency with the evolving marginal
is asserted only on the original interval, in `NonlinearParticleArray`.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace CarryingCapacity.NonlinearParticleContinuation
open CommonInitialNoise NonlinearParticleArray DeterministicEnvironmentLyapunov

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)
  {A I : Type*} [MeasurableSpace A] (initial : A → I → State D)

/-- The actual accepted increment for the endpoint-held environment. -/
def increment (i : I) (f : State D → ℝ) (j : Jump D) (S : ℝ)
    (p : Sample A (I × Jump D) × (ℝ × ℝ)) : ℝ :=
  if p.2.1 ∈ Ioc 0 S ∧ p.2.2 ≤ DeterministicEnvironmentFrozen.timeRate κ q
      (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment) T j p.2.1
      (preState control hActivity ν T hT hCoupling hMoment initial i p.1 p.2.1)
  then f (Jump.advance j (preState control hActivity ν T hT hCoupling hMoment initial i p.1 p.2.1)) -
    f (preState control hActivity ν T hT hCoupling hMoment initial i p.1 p.2.1)
  else 0

omit [MeasurableSpace A] in
/-- Projecting the record changes neither its accepted increment nor its
strict-past state. This is a pointwise identity on all samples. -/
theorem increment_record (i : I) (f : State D → ℝ) (j : Jump D) (S : ℝ)
    (p : Sample A (I × Jump D)) (z : ℝ × ℝ) :
    DeterministicEnvironmentProcess.horizonIncrement control hActivity
      (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment) T hT
      (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment).continuousOn
      id f j S (ParticleInputRecords.record initial i p, z) =
        increment control hActivity ν T hT hCoupling hMoment initial i f j S (p,z) := by
  exact TimeDependentGlobalCounting.horizonIncrement_apply _ _ _ _ _ _ _ _ _ _ _ _

variable [Fintype I] (hInitial : Measurable initial)
  (γ : Measure A) [IsProbabilityMeasure γ]
  (hright : γ.map initial = Measure.pi (fun _ : I => ν.measure))
include hInitial hright

/-- All comparison particles start at the actual extracted initial record. -/
theorem ae_initial : ∀ᵐ p ∂law γ (I × Jump D), ∀ i : I,
    process control hActivity ν T hT hCoupling hMoment initial i p 0 = initial p.1 i := by
  apply ae_all_iff.mpr
  intro i
  exact (record_preserving ν initial hInitial γ hright i).quasiMeasurePreserving.ae
    (DeterministicEnvironmentProcess.ae_initial control hActivity
      (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment) T hT
      (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment).continuousOn
      id ν.measure)

/-- Every test increment is genuinely integrable against the actual original
counting measure on every finite horizon, simultaneously almost surely. -/
theorem ae_integrable_increment : ∀ᵐ p ∂law γ (I × Jump D), ∀ i : I,
    ∀ (S : ℝ≥0) (f : State D → ℝ) (j : Jump D),
      Integrable (fun z => increment control hActivity ν T hT hCoupling hMoment initial i f j S (p,z))
        (MarkedNoise.countingMeasure (i,j) p.2) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  apply ae_all_iff.mpr
  intro i
  have hs := DeterministicEnvironmentProcess.ae_integrable_horizonIncrement control hActivity
    (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment) T hT
    (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment).continuousOn
    id ν.measure hCoupling measurable_id (manuscriptBound control ν (driftConstant control) T)
    (manuscriptBound_nonnegative control ν (driftConstant control) T (driftConstant_nonnegative control) hT)
    (fun s _ => manuscriptExtension_bound control ν (driftConstant control) T
      (driftConstant_nonnegative control) hT
      (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hMoment) s) hMoment
  have h := (record_preserving ν initial hInitial γ hright i).quasiMeasurePreserving.ae hs
  filter_upwards [h] with p hp
  intro S f j
  have hi := hp S f j
  change Integrable _ (MarkedNoise.countingMeasure (i,j) p.2) at hi
  exact hi.congr (Eventually.of_forall
    (increment_record control hActivity ν T hT hCoupling hMoment initial i f j S p))

/-- The equations hold for every nonnegative horizon with the same projected
initial value and original driving measures. The rates remain endpoint-held. -/
theorem ae_counting_identity (f : State D → ℝ) : ∀ᵐ p ∂law γ (I × Jump D),
    ∀ i : I, ∀ S : ℝ≥0,
      f (process control hActivity ν T hT hCoupling hMoment initial i p S) - f (initial p.1 i) =
        ∑ j, ∫ z, increment control hActivity ν T hT hCoupling hMoment initial i f j S (p,z)
          ∂MarkedNoise.countingMeasure (i,j) p.2 := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  apply ae_all_iff.mpr
  intro i
  have hs := DeterministicEnvironmentProcess.ae_counting_identity control hActivity
    (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment) T hT
    (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment).continuousOn
    id ν.measure hCoupling measurable_id (manuscriptBound control ν (driftConstant control) T)
    (manuscriptBound_nonnegative control ν (driftConstant control) T (driftConstant_nonnegative control) hT)
    (fun s _ => manuscriptExtension_bound control ν (driftConstant control) T
      (driftConstant_nonnegative control) hT
      (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hMoment) s) hMoment f
  have h := (record_preserving ν initial hInitial γ hright i).quasiMeasurePreserving.ae hs
  filter_upwards [h] with p hp
  intro S
  calc
    _ = ∑ j, ∫ z,
        DeterministicEnvironmentProcess.horizonIncrement control hActivity
          (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment) T hT
          (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment).continuousOn
          id f j S (ParticleInputRecords.record initial i p,z)
          ∂MarkedNoise.countingMeasure (i,j) p.2 := hp S
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact integral_congr_ae (Eventually.of_forall
        (increment_record control hActivity ν T hT hCoupling hMoment initial i f j S p))

end CarryingCapacity.NonlinearParticleContinuation
