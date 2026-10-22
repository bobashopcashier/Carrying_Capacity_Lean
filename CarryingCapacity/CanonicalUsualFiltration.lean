import CarryingCapacity.UsualFiltration
import CarryingCapacity.ConfigurationTimeDependent
import CarryingCapacity.NonlinearGlobalProcess

/-!
# Actual particle and nonlinear paths in the usual augmentation

The constructed processes are adapted to the minimal completed right-continuous
augmentation of their initial-record and labelled-noise histories. Their exact
localization exits are stopping times there, including the value infinity.
Identifying these histories with those of the counting measures on an arbitrary
prescribed probability space remains a separate transfer theorem.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal NNReal

namespace CarryingCapacity.CanonicalUsualFiltration
open CommonInitialNoise

variable {A : Type*} [MeasurableSpace A]

/-- The usual augmentation of the actual initial-record/noise history. -/
def history (μ : Measure A) (J : Type*) :
    Filtration ℝ (CommonInitialStopping.completedSpace μ J) :=
  UsualFiltration.filtration (law μ J) (CommonInitialNoise.filtration A J)

/-- The same history with an infinite terminal time. -/
def extendedHistory (μ : Measure A) (J : Type*) :
    Filtration ℝ≥0∞ (CommonInitialStopping.completedSpace μ J) :=
  UsualFiltration.extendedFiltration (law μ J) (CommonInitialNoise.filtration A J)

theorem history_rightContinuous (μ : Measure A) (J : Type*) :
    UsualFiltration.IsRightContinuous (history μ J) :=
  UsualFiltration.rightContinuous (law μ J) (CommonInitialNoise.filtration A J)

theorem completedHistory_le (μ : Measure A) (J : Type*) (t : ℝ) :
    CommonInitialStopping.completedAt μ J t ≤ history μ J t :=
  UsualFiltration.completedAt_le_usualAt (law μ J) (CommonInitialNoise.filtration A J) t

instance history_complete (μ : Measure A) (J : Type*) (t : ℝ) :
    ((CommonInitialStopping.completedLaw μ J).trim ((history μ J).le t)).IsComplete :=
  UsualFiltration.trimmed_complete (law μ J) (CommonInitialNoise.filtration A J) t

theorem history_minimal (μ : Measure A) (J : Type*)
    (G : Filtration ℝ (CommonInitialStopping.completedSpace μ J))
    (hraw : ∀ t, CommonInitialNoise.filtration A J t ≤ G t)
    (hnull : ∀ t s, law μ J s = 0 → MeasurableSet[G t] s)
    (hright : UsualFiltration.IsRightContinuous G) : history μ J ≤ G :=
  UsualFiltration.minimal (law μ J) (CommonInitialNoise.filtration A J) G hraw hnull hright

/-- No exit-time modification is made when the filtration is augmented. -/
theorem timeDependent_firstExit_stopping {E J : Type*} [DecidableEq E] [Fintype J]
    [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
    (μ : Measure A) (active : Finset E) (jump : J → E → E)
    (rate : J → ℝ → E → ℝ) (initial : A → E)
    (hRate : ∀ j x, Measurable (fun t => rate j t x)) (hinit : Measurable initial) (C : ℝ) :
    IsStoppingTime (extendedHistory μ J)
      (TimeDependentInitialExit.firstExit active jump rate initial C) :=
  UsualFiltration.isStoppingTime_extended (law μ J) (CommonInitialNoise.filtration A J)
    (fun _ ht => TimeDependentInitialExit.measurableSet_firstExit_le
      μ active jump rate initial hRate hinit C ht)

section Particle
open ConfigurationLocalization
variable {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N)
  (μ : Measure A) (initial : A → Configuration N D) (hinit : Measurable initial)
include hinit

/-- The actual global finite-particle process is adapted to the usual history. -/
theorem configuration_adapted : Adapted (history μ (Label N D))
    (fun t p => ConfigurationTimeDependent.process control hN initial p t) :=
  UsualFiltration.adapted (law μ (Label N D)) (CommonInitialNoise.filtration A (Label N D))
    (fun t => (ConfigurationTimeDependent.measurable_process_at control hN initial hinit t).stronglyMeasurable)

/-- Every actual spatial freezing exit is a stopping time in the usual history. -/
theorem configuration_exit_stopping (n : ℕ) :
    IsStoppingTime (extendedHistory μ (Label N D))
      (ConfigurationTimeDependent.exit control hN initial n) := by
  exact timeDependent_firstExit_stopping μ
    (LyapunovLocalization.active (lyapunov control) (finite_sublevel control hN) n)
    jump (ConfigurationTimeDependent.timeRate κ q hN) initial
    (ConfigurationTimeDependent.measurable_timeRate hN) hinit
    (TimeDependentLocalization.rateBound (lyapunov control) (finite_sublevel control hN)
      (ConfigurationTimeDependent.timeRate κ q hN) (ConfigurationTimeDependent.uniform_rate_bounds control hN) n)

end Particle

section Environment
open DeterministicEnvironmentLyapunov DeterministicEnvironmentFrozen
variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))
  (μ : Measure A) (initial : A → State D)
  (hCoupling : MomentCouplingBound κ q) (hinit : Measurable initial)
include hCoupling hinit

/-- The actual driven process retains adaptedness after the usual augmentation. -/
theorem environment_adapted : Adapted (history μ (Jump D))
    (fun t p => DeterministicEnvironmentProcess.process control hActivity v T hT hv initial p t) :=
  UsualFiltration.adapted (law μ (Jump D)) (CommonInitialNoise.filtration A (Jump D))
    (DeterministicEnvironmentProcess.adapted_process control hActivity v T hT hv initial hCoupling hinit)

theorem environment_exit_stopping (n : ℕ) :
    IsStoppingTime (extendedHistory μ (Jump D))
      (DeterministicEnvironmentProcess.exit control hActivity v T hT hv initial n) := by
  exact timeDependent_firstExit_stopping μ
    (LyapunovLocalization.active control.function (finite_sublevels control) n)
    Jump.advance (timeRate κ q v T) initial
    (DeterministicEnvironmentFrozen.measurable_timeRate κ q v T hv hCoupling hT) hinit
    (TimeDependentLocalization.rateBound control.function (finite_sublevels control)
      (timeRate κ q v T) (exists_uniform_rate_bounds control v T hT hActivity hv) n)

end Environment

section Nonlinear
variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)

/-- The single all-time nonlinear realization is adapted to the usual history. -/
theorem nonlinear_adapted : Adapted (history ν.measure (Jump D))
    (fun t p => NonlinearGlobalProcess.process control hActivity ν hCoupling hMoment p t) :=
  UsualFiltration.adapted (law ν.measure (Jump D))
    (CommonInitialNoise.filtration (State D) (Jump D))
    (NonlinearGlobalProcess.adapted_process control hActivity ν hCoupling hMoment)

end Nonlinear
end CarryingCapacity.CanonicalUsualFiltration
