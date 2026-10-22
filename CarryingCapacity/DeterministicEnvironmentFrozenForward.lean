import CarryingCapacity.DeterministicEnvironmentFrozen
import CarryingCapacity.TimeDependentFrozenForward

/-!
# Actual finite frozen forward equations in the manuscript environment

The continuous prescribed moment-law curve supplies all coefficient assumptions.
Singleton masses come from the already constructed common-noise process. Their
finite active-state system retains leakage and has continuous coefficients and
continuous masses. This is preparation for comparison with other forward laws,
not a uniqueness assertion or a postulated forward solution.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace CarryingCapacity.DeterministicEnvironmentFrozenForward
open CommonInitialNoise DeterministicEnvironmentFrozen TimeDependentFrozenForward

variable {D : ℕ} (κ : MomentScale) (q : Rates D (MomentLaw κ D))

/-- The original, unclamped source-to-target generator coefficient. -/
def coefficient (v : ℝ → MomentLaw κ D) (t : ℝ) (y x : State D) : ℝ :=
  matrixEntry Jump.advance (fun j s z => q.rate j z (v s)) t y x

theorem coefficient_nonneg_of_ne (v : ℝ → MomentLaw κ D)
    (t : ℝ) (y x : State D) (hne : y ≠ x) :
    0 ≤ coefficient κ q v t y x :=
  matrixEntry_nonneg_of_ne Jump.advance _ t y x hne (fun j => q.nonnegative j y (v t))

theorem continuousOn_coefficient (hCoupling : MomentCouplingBound κ q)
    (v : ℝ → MomentLaw κ D) (T : ℝ) (hv : ContinuousOn v (Icc 0 T)) (y x : State D) :
    ContinuousOn (fun t => coefficient κ q v t y x) (Icc 0 T) := by
  exact continuousOn_finset_sum Finset.univ (fun j _ =>
    (DeterministicEnvironmentRates.continuousOn_timeRate κ q hCoupling v T hv j y).mul continuousOn_const)

variable (hActivity : MomentActivityBound κ q) (active : Finset (State D))
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hv : ContinuousOn v (Icc 0 T))

/-- The cap already derived from the manuscript activity assumption bounds Q. -/
theorem norm_coefficient_le (t : ℝ) (ht : t ∈ Icc 0 T)
    (y : State D) (hy : y ∈ active) (x : State D) :
    ‖coefficient κ q v t y x‖ ≤
      Fintype.card (Jump D) * rateCap κ q hActivity active v T hv :=
  norm_matrixEntry_le Jump.advance _ _ t y x (fun j => q.nonnegative j y (v t))
    (fun j => rate_le_cap κ q hActivity active v T hv y hy j t ht)

/-- The active rows lose exactly the rate of jumps into the frozen exterior. -/
theorem sum_coefficient (t : ℝ) (y : State D) (hy : y ∈ active) :
    ∑ x ∈ active, coefficient κ q v t y x =
      -∑ j, if Jump.advance j y ∈ active then 0 else q.rate j y (v t) :=
  sum_matrixEntry active Jump.advance _ t y hy

/-- On the chosen horizon, the actual frozen matrix uses the original environment. -/
theorem matrixEntry_timeRate (t : ℝ) (ht : t ∈ Icc 0 T) (y x : State D) :
    matrixEntry Jump.advance (timeRate κ q v T) t y x = coefficient κ q v t y x := by
  simp only [matrixEntry, coefficient, timeRate_eq κ q v T _ t ht]

variable {A : Type*} [MeasurableSpace A] (initial : A → State D)
  (μ : Measure A) [IsProbabilityMeasure μ]

/-- Actual singleton mass of the canonical frozen process. -/
def mass (t : ℝ) (x : State D) : ℝ :=
  TimeDependentFrozenForward.mass active Jump.advance (timeRate κ q v T) initial μ
    (rateCap κ q hActivity active v T hv) t x

omit [IsProbabilityMeasure μ] in
theorem mass_nonneg (t : ℝ) (x : State D) :
    0 ≤ mass κ q hActivity active v T hv initial μ t x :=
  TimeDependentFrozenForward.mass_nonneg active Jump.advance _ initial μ _ t x

theorem mass_zero (x : State D) :
    mass κ q hActivity active v T hv initial μ 0 x =
      ∫ a, atomTest x (initial a) ∂μ :=
  TimeDependentFrozenForward.mass_zero active Jump.advance _ initial μ _ x

variable (hCoupling : MomentCouplingBound κ q) (hT : 0 ≤ T) (hinit : Measurable initial)
include hCoupling hT hinit

theorem mass_le_one (t : ℝ) (x : State D) :
    mass κ q hActivity active v T hv initial μ t x ≤ 1 :=
  TimeDependentFrozenForward.mass_le_one active Jump.advance _ initial μ
    (measurable_timeRate κ q v T hv hCoupling hT) hinit _ t x

/-- Continuous actual probabilities, derived from frozen Dynkin rather than assumed. -/
theorem continuousOn_mass (x : State D) :
    ContinuousOn (fun t => mass κ q hActivity active v T hv initial μ t x) (Ici 0) :=
  TimeDependentFrozenForward.continuousOn_mass active Jump.advance _ initial μ
    (measurable_timeRate κ q v T hv hCoupling hT) hinit _ 0 x
    (fun y _ j s _ => timeRate_nonnegative κ q v T j s y)
    (fun y hy j s _ => timeRate_le_cap κ q hActivity active v T hv hT y hy j s)

/-- The exact active-state forward equation for each actual frozen mass. -/
theorem mass_forward (t : ℝ) (ht : t ≤ T) (x : State D) :
    mass κ q hActivity active v T hv initial μ t x =
      (∫ a, atomTest x (initial a) ∂μ) + ∫ s in Ioc 0 t,
        ∑ y ∈ active, mass κ q hActivity active v T hv initial μ s y * coefficient κ q v s y x := by
  have h := TimeDependentFrozenForward.mass_forward active Jump.advance _ initial μ
    (measurable_timeRate κ q v T hv hCoupling hT) hinit
    (rateCap κ q hActivity active v T hv) 0 x t
    (fun y _ j s _ => timeRate_nonnegative κ q v T j s y)
    (fun y hy j s _ => timeRate_le_cap κ q hActivity active v T hv hT y hy j s)
  unfold mass
  rw [h]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  apply Finset.sum_congr rfl
  intro y _
  rw [matrixEntry_timeRate κ q v T s ⟨hs.1.le, hs.2.trans ht⟩]

/-- The same system indexed by the finite subtype, ready for finite comparison. -/
theorem restricted_mass_forward (t : ℝ) (ht : t ≤ T) (x : active) :
    mass κ q hActivity active v T hv initial μ t x =
      (∫ a, atomTest (x : State D) (initial a) ∂μ) + ∫ s in Ioc 0 t,
        ∑ y : active, mass κ q hActivity active v T hv initial μ s y * coefficient κ q v s y x := by
  rw [mass_forward κ q hActivity active v T hv initial μ hCoupling hT hinit t ht x]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s _
  exact (Finset.sum_attach active (fun y =>
    mass κ q hActivity active v T hv initial μ s y * coefficient κ q v s y x)).symm

end CarryingCapacity.DeterministicEnvironmentFrozenForward
