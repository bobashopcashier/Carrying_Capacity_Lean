import CarryingCapacity.NonlinearFixedPoint
import CarryingCapacity.TimeDependentGlobalPreStateTime
import CarryingCapacity.InitialPredictableCompensation

/-!
# Actual accepted weighted jump variation of the nonlinear process

The variation is the sum of the adapted distances of genuinely accepted jumps,
using the actual predictable pre-state and original common counting measures.
Nonnegative predictable compensation identifies its expectation with the
current-state weighted activity. Finiteness is not assumed here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace CarryingCapacity.NonlinearPathVariation
open CommonInitialNoise MarkedIntensity PredictableSets PredictableTime
open PredictableStepApproximation DeterministicEnvironmentLyapunov

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)

/-- The actual event-time rate, held at the environment endpoints outside the
construction interval. -/
def rate (j : Jump D) (t : ℝ) (x : State D) : ℝ :=
  DeterministicEnvironmentFrozen.timeRate κ q
    (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment) T j t x

/-- The nonnegative adapted-distance weight of an accepted jump in `(s,t]`. -/
def acceptedWeight (j : Jump D) (s t : ℝ)
    (p : Sample (State D) (Jump D) × (ℝ × ℝ)) : ℝ≥0∞ :=
  if p.2.1 ∈ Ioc s t ∧ p.2.2 ≤ rate control hActivity ν T hT hCoupling hMoment j p.2.1
      (NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p.1 p.2.1)
  then ENNReal.ofReal (adaptedDistance κ
    (Jump.advance j (NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p.1 p.2.1))
    (NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p.1 p.2.1))
  else 0

/-- Actual accepted weighted variation, including every jump at the right endpoint. -/
def variation (s t : ℝ) (p : Sample (State D) (Jump D)) : ℝ≥0∞ :=
  ∑ j, ∫⁻ z, acceptedWeight control hActivity ν T hT hCoupling hMoment j s t (p,z)
    ∂MarkedNoise.countingMeasure j p.2

/-- Current-state weighted activity for a single jump label. -/
def currentActivity (j : Jump D) (p : Sample (State D) (Jump D) × ℝ) : ℝ :=
  rate control hActivity ν T hT hCoupling hMoment j p.2
    (NonlinearFixedPoint.process control hActivity ν T hT hCoupling hMoment p.1 p.2) *
  adaptedDistance κ
    (Jump.advance j (NonlinearFixedPoint.process control hActivity ν T hT hCoupling hMoment p.1 p.2))
    (NonlinearFixedPoint.process control hActivity ν T hT hCoupling hMoment p.1 p.2)

theorem acceptedWeight_apply (j : Jump D) (s t : ℝ)
    (p : Sample (State D) (Jump D)) (z : ℝ × ℝ) :
    acceptedWeight control hActivity ν T hT hCoupling hMoment j s t (p,z) =
      if z.1 ∈ Ioc s t ∧ z.2 ≤ rate control hActivity ν T hT hCoupling hMoment j z.1
        (NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p z.1)
      then ENNReal.ofReal (adaptedDistance κ
        (Jump.advance j (NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p z.1))
        (NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p z.1))
      else 0 := rfl

theorem rate_nonnegative (j : Jump D) (t : ℝ) (x : State D) :
    0 ≤ rate control hActivity ν T hT hCoupling hMoment j t x := q.nonnegative _ _ _

theorem rate_eq (j : Jump D) (t : ℝ) (ht : t ∈ Icc 0 T) (x : State D) :
    rate control hActivity ν T hT hCoupling hMoment j t x =
      q.rate j x (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment t) :=
  DeterministicEnvironmentFrozen.timeRate_eq κ q _ T j t ht x

theorem measurable_rate (j : Jump D) (x : State D) :
    Measurable (fun t => rate control hActivity ν T hT hCoupling hMoment j t x) :=
  DeterministicEnvironmentFrozen.measurable_timeRate κ q _ T
    (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment).continuousOn
    hCoupling hT j x

/-- The actual pre-state is predictable in the raw initial-record/noise history. -/
theorem measurable_preState : Measurable[predictable (filtration (State D) (Jump D))]
    (fun p : Sample (State D) (Jump D) × (ℝ × ℝ) =>
      NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p.1 p.2.1) :=
  measurable_pastLimit (filtration (State D) (Jump D)) _
    (fun s _ => (NonlinearFixedPoint.adapted_process control hActivity ν T hT hCoupling hMoment s).measurable) 0

/-- This genuine interval integrand uses only strict-past state information. -/
theorem predictable_acceptedWeight (j : Jump D) (s t : ℝ) (hs : 0 ≤ s) :
    Measurable[predictable (filtration (State D) (Jump D))]
      (acceptedWeight control hActivity ν T hT hCoupling hMoment j s t) := by
  classical
  letI : MeasurableSpace (Sample (State D) (Jump D) × (ℝ × ℝ)) :=
    predictable (filtration (State D) (Jump D))
  have hz := measurable_preState control hActivity ν T hT hCoupling hMoment
  have hr := measurable_evaluation (filtration (State D) (Jump D))
    (rate control hActivity ν T hT hCoupling hMoment j)
    (measurable_rate control hActivity ν T hT hCoupling hMoment j) _ hz
  have hw := ((measurable_of_countable (fun x : State D =>
    adaptedDistance κ (Jump.advance j x) x)).comp hz).ennreal_ofReal
  have ha : Measurable (fun p : Sample (State D) (Jump D) × (ℝ × ℝ) =>
      if positiveHeight p ≤ rate control hActivity ν T hT hCoupling hMoment j (positiveTime p)
        (NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p.1 p.2.1)
      then ENNReal.ofReal (adaptedDistance κ
        (Jump.advance j (NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p.1 p.2.1))
        (NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p.1 p.2.1)) else 0) :=
    hw.ite (measurableSet_le (measurable_positiveHeight (filtration (State D) (Jump D))) hr) measurable_const
  have hm := ha.indicator
    (measurableSet_predictable_rectangle (filtration (State D) (Jump D)) s t hs
      univ MeasurableSet.univ univ MeasurableSet.univ)
  convert hm using 1
  funext p
  by_cases ht : p.2.1 ∈ Ioc s t
  · have hp : 0 < p.2.1 := hs.trans_lt ht.1
    simp [acceptedWeight, rectangle, Set.indicator_apply, ht, positiveTime, positiveHeight, hp]
  · simp [acceptedWeight, rectangle, Set.indicator_apply, ht]

/-- The actual random variation is measurable, before any finite-expectation claim. -/
theorem measurable_variation (s t : ℝ) (hs : 0 ≤ s) :
    Measurable (variation control hActivity ν T hT hCoupling hMoment s t) := by
  apply Finset.measurable_sum
  intro j _
  exact InitialPredictableCompensation.measurable_countingIntegral j _
    ((predictable_acceptedWeight control hActivity ν T hT hCoupling hMoment j s t hs).mono
      (predictable_le _) le_rfl)

theorem variation_mono {s₁ t₁ s₂ t₂ : ℝ} (hs : s₂ ≤ s₁) (ht : t₁ ≤ t₂)
    (p : Sample (State D) (Jump D)) :
    variation control hActivity ν T hT hCoupling hMoment s₁ t₁ p ≤
      variation control hActivity ν T hT hCoupling hMoment s₂ t₂ p := by
  apply Finset.sum_le_sum
  intro j _
  apply lintegral_mono
  intro z
  by_cases hz : z.1 ∈ Ioc s₁ t₁ ∧ z.2 ≤ rate control hActivity ν T hT hCoupling hMoment j z.1
      (NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p z.1)
  · have hz' : z.1 ∈ Ioc s₂ t₂ ∧ z.2 ≤ rate control hActivity ν T hT hCoupling hMoment j z.1
        (NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p z.1) :=
      ⟨⟨hs.trans_lt hz.1.1, hz.1.2.trans ht⟩, hz.2⟩
    simp only [acceptedWeight_apply, hz, hz', if_true, le_refl]
  · simp only [acceptedWeight_apply, hz, if_false, zero_le]

/-- Current activity is genuinely jointly measurable. -/
theorem measurable_currentActivity (j : Jump D) :
    Measurable (currentActivity control hActivity ν T hT hCoupling hMoment j) := by
  have hx := NonlinearFixedPoint.measurable_process control hActivity ν T hT hCoupling hMoment
  exact ((measurable_coefficient (rate control hActivity ν T hT hCoupling hMoment j)
    (measurable_rate control hActivity ν T hT hCoupling hMoment j)).comp
      (measurable_snd.prodMk hx)).mul
    ((measurable_of_countable (fun x : State D => adaptedDistance κ (Jump.advance j x) x)).comp hx)

/-- This is the proved pre/current-state equality for the actual nonexplosive path. -/
theorem ae_preState_eq_process_time : ∀ᵐ p ∂law ν.measure (Jump D),
    NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p =ᵐ[positiveVolume]
      NonlinearFixedPoint.process control hActivity ν T hT hCoupling hMoment p := by
  exact TimeDependentGlobalPreStateTime.ae_preState_eq_process_time control.function
    (finite_sublevels control) Jump.advance
    (DeterministicEnvironmentFrozen.timeRate κ q
      (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment) T)
    (exists_uniform_rate_bounds control
      (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment) T hT hActivity
      (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment).continuousOn)
    id 0 ν.measure (NonlinearFixedPoint.ae_exhaustive control hActivity ν T hT hCoupling hMoment)

/-- Nonnegative predictable compensation for the genuine accepted weight. -/
theorem compensation_acceptedWeight (j : Jump D) (s t : ℝ) (hs : 0 ≤ s) :
    (∫⁻ p, ∫⁻ z, acceptedWeight control hActivity ν T hT hCoupling hMoment j s t (p,z)
      ∂MarkedNoise.countingMeasure j p.2 ∂law ν.measure (Jump D)) =
    ∫⁻ p, ∫⁻ z, acceptedWeight control hActivity ν T hT hCoupling hMoment j s t (p,z)
      ∂positiveVolume.prod positiveVolume ∂law ν.measure (Jump D) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact InitialPredictableCompensation.compensation_nonnegative ν.measure j _
    (predictable_acceptedWeight control hActivity ν T hT hCoupling hMoment j s t hs)

/-- Height integration gives exactly rate times adapted jump distance. -/
theorem intensityIntegral_eq (j : Jump D) (s t : ℝ) (hs : 0 ≤ s)
    (p : Sample (State D) (Jump D)) :
    (∫⁻ z, acceptedWeight control hActivity ν T hT hCoupling hMoment j s t (p,z)
      ∂positiveVolume.prod positiveVolume) =
    ∫⁻ r in Ioc s t, ENNReal.ofReal
      (rate control hActivity ν T hT hCoupling hMoment j r
          (NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p r) *
        adaptedDistance κ
          (Jump.advance j (NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p r))
          (NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p r))
      ∂positiveVolume := by
  have hm := (predictable_acceptedWeight control hActivity ν T hT hCoupling hMoment j s t hs).mono
    (predictable_le _) le_rfl
  have hm' : Measurable (fun z : ℝ × ℝ =>
      acceptedWeight control hActivity ν T hT hCoupling hMoment j s t (p,z)) :=
    hm.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod _ hm'.aemeasurable,
    ← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro r
  by_cases hr : r ∈ Ioc s t
  · simp only [acceptedWeight_apply, hr, true_and, Set.indicator_of_mem hr]
    have he : (fun u : ℝ => if u ≤ rate control hActivity ν T hT hCoupling hMoment j r
        (NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p r)
      then ENNReal.ofReal (adaptedDistance κ
        (Jump.advance j (NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p r))
        (NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p r)) else 0) =
      (Iic (rate control hActivity ν T hT hCoupling hMoment j r
        (NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p r))).indicator
      (fun _ => ENNReal.ofReal (adaptedDistance κ
        (Jump.advance j (NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p r))
        (NonlinearFixedPoint.preState control hActivity ν T hT hCoupling hMoment p r))) := rfl
    rw [he, lintegral_indicator_const measurableSet_Iic, positiveVolume_Iic,
      ENNReal.ofReal_mul (rate_nonnegative control hActivity ν T hT hCoupling hMoment j r _)]
    exact mul_comm _ _
  · simp [acceptedWeight_apply, hr]

/-- The actual expected accepted weight equals the expected current activity;
all values may still be infinite. -/
theorem expected_acceptedWeight_eq (j : Jump D) (s t : ℝ) (hs : 0 ≤ s) :
    (∫⁻ p, ∫⁻ z, acceptedWeight control hActivity ν T hT hCoupling hMoment j s t (p,z)
      ∂MarkedNoise.countingMeasure j p.2 ∂law ν.measure (Jump D)) =
    ∫⁻ r in Ioc s t, ∫⁻ p, ENNReal.ofReal
      (currentActivity control hActivity ν T hT hCoupling hMoment j (p,r))
      ∂law ν.measure (Jump D) ∂positiveVolume := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  rw [compensation_acceptedWeight control hActivity ν T hT hCoupling hMoment j s t hs]
  simp_rw [intensityIntegral_eq control hActivity ν T hT hCoupling hMoment j s t hs]
  calc
    _ = ∫⁻ p, ∫⁻ r in Ioc s t, ENNReal.ofReal
        (currentActivity control hActivity ν T hT hCoupling hMoment j (p,r))
        ∂positiveVolume ∂law ν.measure (Jump D) := by
      apply lintegral_congr_ae
      filter_upwards [ae_preState_eq_process_time control hActivity ν T hT hCoupling hMoment] with p hp
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae hp] with r hr
      simp only [hr, currentActivity]
    _ = _ := lintegral_lintegral_swap
      (measurable_currentActivity control hActivity ν T hT hCoupling hMoment j).ennreal_ofReal.aemeasurable

/-- Full finite-label compensation before restricting the endpoint-held rate
to the original construction interval. -/
theorem expected_variation_eq_clamped (s t : ℝ) (hs : 0 ≤ s) :
    (∫⁻ p, variation control hActivity ν T hT hCoupling hMoment s t p ∂law ν.measure (Jump D)) =
    ∫⁻ r in Ioc s t, ∫⁻ p, ∑ j : Jump D, ENNReal.ofReal
      (currentActivity control hActivity ν T hT hCoupling hMoment j (p,r))
      ∂law ν.measure (Jump D) ∂positiveVolume := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  have hm (j : Jump D) :=
    (measurable_currentActivity control hActivity ν T hT hCoupling hMoment j).ennreal_ofReal
  simp only [variation]
  rw [lintegral_finset_sum Finset.univ (fun j _ =>
    InitialPredictableCompensation.measurable_countingIntegral j _
      ((predictable_acceptedWeight control hActivity ν T hT hCoupling hMoment j s t hs).mono
        (predictable_le _) le_rfl))]
  simp_rw [expected_acceptedWeight_eq control hActivity ν T hT hCoupling hMoment _ s t hs]
  rw [← lintegral_finset_sum Finset.univ (fun j _ => (hm j).lintegral_prod_left')]
  apply lintegral_congr
  intro r
  exact (lintegral_finset_sum Finset.univ (fun j _ =>
    (hm j).comp (measurable_id.prodMk measurable_const))).symm

/-- On the original interval the finite label sum is exactly the paper's
weighted activity at the actual current state and marginal environment. -/
theorem sum_currentActivity (p : Sample (State D) (Jump D)) (r : ℝ) (hr : r ∈ Icc 0 T) :
    (∑ j : Jump D, ENNReal.ofReal (currentActivity control hActivity ν T hT hCoupling hMoment j (p,r))) =
      ENNReal.ofReal (weightedActivity κ q
        (NonlinearFixedPoint.process control hActivity ν T hT hCoupling hMoment p r)
        (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment r)) := by
  unfold currentActivity weightedActivity
  simp_rw [rate_eq control hActivity ν T hT hCoupling hMoment _ r hr]
  exact (ENNReal.ofReal_sum_of_nonneg (fun j _ =>
    mul_nonneg (q.nonnegative _ _ _) (adaptedDistance_nonneg κ _ _))).symm

/-- Exact compensation against ordinary time Lebesgue measure, with the
original rate and actual current marginal on the construction interval. -/
theorem expected_variation_eq (s t : ℝ) (hs : 0 ≤ s) (ht : t ≤ T) :
    (∫⁻ p, variation control hActivity ν T hT hCoupling hMoment s t p ∂law ν.measure (Jump D)) =
    ∫⁻ r in Ioc s t, ∫⁻ p, ENNReal.ofReal (weightedActivity κ q
      (NonlinearFixedPoint.process control hActivity ν T hT hCoupling hMoment p r)
      (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment r))
      ∂law ν.measure (Jump D) := by
  rw [expected_variation_eq_clamped control hActivity ν T hT hCoupling hMoment s t hs]
  have hv : positiveVolume.restrict (Ioc s t) = volume.restrict (Ioc s t) := by
    rw [positiveVolume, Measure.restrict_restrict measurableSet_Ioc]
    have hi : Ioc s t ⊆ Ici (0 : ℝ) := fun r hr => hs.trans hr.1.le
    rw [Set.inter_eq_left.mpr hi]
  rw [hv]
  apply setLIntegral_congr_fun measurableSet_Ioc
  filter_upwards [] with r
  intro hr
  apply lintegral_congr
  intro p
  exact sum_currentActivity control hActivity ν T hT hCoupling hMoment p r
    ⟨hs.trans hr.1.le, hr.2.trans ht⟩

end CarryingCapacity.NonlinearPathVariation
