import CarryingCapacity.ParticleInputRecords
import CarryingCapacity.NonlinearFixedPoint
import CarryingCapacity.EmpiricalArrayError

/-!
# Actual independent nonlinear particles on the common particle-noise space

Each particle is the canonical nonlinear process evaluated on its projected
initial/noise record. Independence is proved from the exact joint input law,
and the counting equations retain the original particle-labelled Poisson
measures. The trajectory independence below uses the coordinate sigma algebra
on real-time functions; it does not assert a Skorokhod-space realization.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace CarryingCapacity.NonlinearParticleArray
open CommonInitialNoise

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)

section Array
variable {A I : Type*} [MeasurableSpace A]
  (initial : A → I → State D)

/-- The actual nonlinear comparison particle, using its own coordinates of
the same labelled noise that drives the interacting configuration. -/
def process (i : I) (p : Sample A (I × Jump D)) (t : ℝ) : State D :=
  NonlinearFixedPoint.process control hActivity ν T hT hCoupling hMoment
    (ParticleInputRecords.record initial i p) t

/-- Its actual predictable strict-past state. -/
def preState (i : I) (p : Sample A (I × Jump D)) (t : ℝ) : State D :=
  NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment
    (ParticleInputRecords.record initial i p) t

variable (hInitial : Measurable initial)
include hInitial

theorem measurable_process (i : I) : Measurable
    (fun p : Sample A (I × Jump D) × ℝ =>
      process control hActivity ν T hT hCoupling hMoment initial i p.1 p.2) := by
  unfold process
  have hr : Measurable (fun p : Sample A (I × Jump D) × ℝ =>
      (ParticleInputRecords.record initial i p.1, p.2)) :=
    ((ParticleInputRecords.measurable_record initial hInitial i).comp measurable_fst).prodMk
      measurable_snd
  simpa only [Function.comp_def] using
    (NonlinearFixedPoint.measurable_process control hActivity ν T hT hCoupling hMoment).comp hr

theorem measurable_process_at (i : I) (t : ℝ) : Measurable
    (fun p => process control hActivity ν T hT hCoupling hMoment initial i p t) :=
  (measurable_process control hActivity ν T hT hCoupling hMoment initial hInitial i).of_uncurry_right

/-- Each comparison particle is adapted to the full particle system's raw
initial-plus-noise filtration, by measurable projection of the observed past. -/
theorem adapted_process (i : I) : Adapted (filtration A (I × Jump D))
    (fun t p => process control hActivity ν T hT hCoupling hMoment initial i p t) := by
  intro t
  exact (NonlinearFixedPoint.adapted_process control hActivity ν T hT hCoupling hMoment t).comp_measurable
    (ParticleInputRecords.measurable_record_at initial hInitial i t)

/-- A whole trajectory is measurable for the coordinate sigma algebra. -/
theorem measurable_trajectory (i : I) : Measurable
    (process control hActivity ν T hT hCoupling hMoment initial i) :=
  measurable_pi_lambda _ (measurable_process_at control hActivity ν T hT hCoupling
    hMoment initial hInitial i)

variable [Fintype I] (γ : Measure A) [IsProbabilityMeasure γ]
  (hright : γ.map initial = Measure.pi (fun _ : I => ν.measure))

include hInitial hright

/-- Each projected input is measure preserving for the entire initial/noise
record, allowing arbitrary almost-sure path properties to be transferred. -/
theorem record_preserving (i : I) : MeasurePreserving
    (ParticleInputRecords.record (J := Jump D) initial i)
    (law γ (I × Jump D)) (law ν.measure (Jump D)) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact ⟨ParticleInputRecords.measurable_record initial hInitial i,
    ParticleInputRecords.record_map γ ν.measure initial hInitial hright i⟩

/-- Joint independence of complete coordinate-measurable trajectories, proved
from independence of their complete records. -/
theorem independent_trajectories : iIndepFun
    (process control hActivity ν T hT hCoupling hMoment initial)
    (law γ (I × Jump D)) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  have hm : Measurable (NonlinearFixedPoint.process control hActivity ν T hT hCoupling hMoment) :=
    measurable_pi_lambda _ (fun _ =>
      (NonlinearFixedPoint.measurable_process control hActivity ν T hT hCoupling hMoment).of_uncurry_right)
  exact (ParticleInputRecords.independent_records (J := Jump D)
    γ ν.measure initial hInitial hright).comp
    (fun _ => NonlinearFixedPoint.process control hActivity ν T hT hCoupling hMoment) (fun _ => hm)

theorem independent_at (t : ℝ) : iIndepFun
    (fun i p => process control hActivity ν T hT hCoupling hMoment initial i p t)
    (law γ (I × Jump D)) :=
  (independent_trajectories control hActivity ν T hT hCoupling hMoment initial hInitial γ hright).comp
    (fun _ f => f t) (fun _ => measurable_pi_apply t)

/-- The exact nonlinear law at each time in the construction interval. -/
theorem process_marginal (i : I) (t : Icc (0 : ℝ) T) :
    (law γ (I × Jump D)).map
      (fun p => process control hActivity ν T hT hCoupling hMoment initial i p t) =
      ((NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hMoment).val t).measure := by
  have hm : Measurable (fun p : Sample (State D) (Jump D) =>
      NonlinearFixedPoint.process control hActivity ν T hT hCoupling hMoment p t) :=
    (NonlinearFixedPoint.measurable_process control hActivity ν T hT hCoupling hMoment).of_uncurry_right
  change (law γ (I × Jump D)).map
    ((fun p => NonlinearFixedPoint.process control hActivity ν T hT hCoupling hMoment p t) ∘
      ParticleInputRecords.record initial i) = _
  rw [← Measure.map_map hm (ParticleInputRecords.measurable_record initial hInitial i),
    (record_preserving ν initial hInitial γ hright i).map_eq]
  exact NonlinearFixedPoint.process_marginal control hActivity ν T hT hCoupling hMoment t

/-- The full finite state vector has the product nonlinear marginal law. -/
theorem array_marginal (t : Icc (0 : ℝ) T) :
    (law γ (I × Jump D)).map
      (fun p i => process control hActivity ν T hT hCoupling hMoment initial i p t) =
      Measure.pi (fun _ : I =>
        ((NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hMoment).val t).measure) := by
  rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i =>
    (measurable_process_at control hActivity ν T hT hCoupling hMoment initial hInitial i t).aemeasurable)).mp
      (independent_at control hActivity ν T hT hCoupling hMoment initial hInitial γ hright t)]
  simp_rw [process_marginal control hActivity ν T hT hCoupling hMoment initial hInitial γ hright]

/-- Càdlàg regularity holds for all particles on one probability-one event. -/
theorem ae_cadlag : ∀ᵐ p ∂law γ (I × Jump D), ∀ i : I,
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt
      (process control hActivity ν T hT hCoupling hMoment initial i p) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : State D, Tendsto
      (process control hActivity ν T hT hCoupling hMoment initial i p) (𝓝[<] t) (𝓝 y)) := by
  apply ae_all_iff.mpr
  intro i
  exact (record_preserving ν initial hInitial γ hright i).quasiMeasurePreserving.ae
    (NonlinearFixedPoint.ae_process_cadlag control hActivity ν T hT hCoupling hMoment)

/-- The predictable state is the actual path's left limit for every positive
time and every particle, simultaneously almost surely. -/
theorem ae_preState_eq_leftLim : ∀ᵐ p ∂law γ (I × Jump D), ∀ i : I, ∀ t : ℝ, 0 < t →
    preState control hActivity ν T hT hCoupling hMoment initial i p t =
      Function.leftLim (process control hActivity ν T hT hCoupling hMoment initial i p) t := by
  apply ae_all_iff.mpr
  intro i
  exact (record_preserving ν initial hInitial γ hright i).quasiMeasurePreserving.ae
    (NonlinearFixedPoint.ae_preState_eq_leftLim control hActivity ν T hT hCoupling hMoment)

/-- The cutoff-free equations use exactly the original particle-labelled
counting measures, with no replacement noises or assumed stochastic identity. -/
theorem ae_counting_identity (f : State D → ℝ) :
    ∀ᵐ p ∂law γ (I × Jump D), ∀ i : I, ∀ S : ℝ≥0, (S : ℝ) ≤ T →
      f (process control hActivity ν T hT hCoupling hMoment initial i p S) - f (initial p.1 i) =
        ∑ j, ∫ z : ℝ × ℝ,
          (if z.1 ∈ Ioc 0 (S : ℝ) ∧ z.2 ≤ q.rate j
              (preState control hActivity ν T hT hCoupling hMoment initial i p z.1)
              (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment z.1)
          then f (Jump.advance j (preState control hActivity ν T hT hCoupling hMoment initial i p z.1)) -
            f (preState control hActivity ν T hT hCoupling hMoment initial i p z.1) else 0)
          ∂MarkedNoise.countingMeasure (i, j) p.2 := by
  apply ae_all_iff.mpr
  intro i
  have h := (record_preserving ν initial hInitial γ hright i).quasiMeasurePreserving.ae
    (NonlinearFixedPoint.ae_counting_identity control hActivity ν T hT hCoupling hMoment f)
  filter_upwards [h] with p hp
  simpa only [process, preState, ParticleInputRecords.record,
    ParticleNoiseProjection.countingMeasure_project] using hp

end Array

end CarryingCapacity.NonlinearParticleArray
