import CarryingCapacity.PopulationStoppedCoupling

/-!
# Removing the genuine population coupling cutoff

The population discrepancy averages each coordinate's running supremum before
taking expectation. On the event that the joint exit is later than the horizon,
the actual stopped and unstopped discrepancies agree pointwise. A deterministic
event inclusion and Markov's inequality give the cutoff-removal bound for the
actual constructed configurations. Measurability is derived from their genuine
nonexplosion and path regularity, not imposed as a comparison hypothesis.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal

namespace CarryingCapacity.PopulationCouplingRemoval
open CommonInitialNoise ConfigurationLocalization PopulationCouplingAlgebra
open PopulationStoppedCoupling SynchronousRunningSupremum SynchronousStoppedRunningSupremum

variable {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N) (hActivity : MomentActivityBound κ q)
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))
  {A : Type*} [MeasurableSpace A] (initialX initialY : A → Configuration N D)

local notation "VX" => lyapunov control
local notation "hfin" => finite_sublevel control hN
local notation "rX" => ConfigurationTimeDependent.timeRate κ q hN
local notation "bX" => ConfigurationTimeDependent.uniform_rate_bounds control hN
local notation "rY" => DeterministicEnvironmentConfiguration.rate κ q v T
local notation "bY" => DeterministicEnvironmentConfiguration.exists_uniform_rate_bounds control hN hActivity v T hT hv

/-- The actual unstopped running cost of one paired coordinate. -/
def coordinateRunningCost (i : Fin N) (S : ℝ) (p : Sample A (Label N D)) : ℝ≥0∞ :=
  runningCost VX hfin jump rX bX rY bY initialX initialY 0 (coordinateCost κ i) S p

/-- Average of the coordinate running suprema, with no spatial stopping. -/
def averagedRunningCost (S : ℝ) (p : Sample A (Label N D)) : ℝ≥0∞ :=
  ENNReal.ofReal (N : ℝ)⁻¹ * ∑ i : Fin N,
    coordinateRunningCost control hN hActivity v T hT hv initialX initialY i S p

omit [MeasurableSpace A] in
/-- Stopping changes no coordinate running cost when the whole horizon is
before or equal to the actual joint exit. Equality includes the exit jump. -/
theorem coordinateRunningCost_eq_stopped_of_le (R : ℝ) (i : Fin N) (S : ℝ)
    (p : Sample A (Label N D))
    (hbefore : ENNReal.ofReal S ≤ pairExit control hN hActivity v T hT hv initialX initialY R p) :
    coordinateRunningCost control hN hActivity v T hT hv initialX initialY i S p =
      coordinateStoppedCost control hN hActivity v T hT hv initialX initialY R i S p := by
  unfold coordinateRunningCost coordinateStoppedCost runningCost stoppedRunningCost intervalSup
  apply iSup_congr
  intro t
  symm
  apply stopped_eq_of_le _ _ t t.property.1
  exact (ENNReal.ofReal_le_ofReal t.property.2).trans hbefore

omit [MeasurableSpace A] in
/-- The actual population averages agree on the good event, pointwise on all
samples. No pathwise regularity or exceptional event is required here. -/
theorem averagedRunningCost_eq_stopped_of_le (R S : ℝ)
    (p : Sample A (Label N D))
    (hbefore : ENNReal.ofReal S ≤ pairExit control hN hActivity v T hT hv initialX initialY R p) :
    averagedRunningCost control hN hActivity v T hT hv initialX initialY S p =
      averagedStoppedCost control hN hActivity v T hT hv initialX initialY R S p := by
  unfold averagedRunningCost averagedStoppedCost
  congr 1
  exact Finset.sum_congr rfl (fun i _ => coordinateRunningCost_eq_stopped_of_le
    control hN hActivity v T hT hv initialX initialY R i S p hbefore)

omit [MeasurableSpace A] in
/-- A large unstopped discrepancy requires either an actual exit or a large
stopped discrepancy. This is an exact event inclusion, not an AE substitute. -/
theorem runningCost_event_subset (R S : ℝ) (ε : ℝ≥0∞) :
    {p | ε < averagedRunningCost control hN hActivity v T hT hv initialX initialY S p} ⊆
      {p | pairExit control hN hActivity v T hT hv initialX initialY R p ≤ ENNReal.ofReal S} ∪
      {p | ε ≤ averagedStoppedCost control hN hActivity v T hT hv initialX initialY R S p} := by
  intro p hp
  by_cases he : pairExit control hN hActivity v T hT hv initialX initialY R p ≤ ENNReal.ofReal S
  · exact Or.inl he
  · apply Or.inr
    change ε ≤ averagedStoppedCost control hN hActivity v T hT hv initialX initialY R S p
    rw [← averagedRunningCost_eq_stopped_of_le control hN hActivity v T hT hv initialX initialY
      R S p (lt_of_not_ge he).le]
    exact hp.le

variable (μ : Measure A) [IsProbabilityMeasure μ]
  (hCoupling : MomentCouplingBound κ q) (hinitX : Measurable initialX) (hinitY : Measurable initialY)
  (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ s ∈ Icc 0 T,
    LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
  (hInitialX : Integrable (fun a => lyapunov control (initialX a)) μ)
  (hInitialY : Integrable (fun a => lyapunov control (initialY a)) μ)
include hCoupling hinitX hinitY hB hEnv hInitialX hInitialY

/-- Each genuine coordinate supremum is AE measurable by the previously
constructed nonexplosive paths and their countable observation version. -/
theorem aemeasurable_coordinateRunningCost (i : Fin N) (S : ℝ≥0) :
    AEMeasurable (coordinateRunningCost control hN hActivity v T hT hv initialX initialY i S)
      (law μ (Label N D)) := by
  exact aemeasurable_runningCost VX hfin jump rX bX rY bY initialX initialY 0 μ
    (ConfigurationTimeDependent.measurable_timeRate hN)
    (DeterministicEnvironmentConfiguration.measurable_rate v T hT hv hCoupling) hinitX hinitY
    (ConfigurationTimeDependent.ae_exhaustive control hN initialX μ hinitX hInitialX)
    (DeterministicEnvironmentConfiguration.ae_exhaustive control hN hActivity v T hT hv initialY μ
      hCoupling hinitY B hB hEnv hInitialY) (coordinateCost κ i) S

/-- The actual average of uncountable coordinate suprema is AE measurable. -/
theorem aemeasurable_averagedRunningCost (S : ℝ≥0) :
    AEMeasurable (averagedRunningCost control hN hActivity v T hT hv initialX initialY S)
      (law μ (Label N D)) := by
  exact aemeasurable_const.mul (Finset.univ.aemeasurable_sum (fun i _ =>
    aemeasurable_coordinateRunningCost control hN hActivity v T hT hv initialX initialY μ
      hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY i S))

/-- The genuine cutoff-removal estimate. Both random discrepancies refer to
the actual same-noise configuration pair. No finite stopped expectation is
required at this stage; all terms have their extended nonnegative meaning. -/
theorem probability_runningCost_le_exit_add_markov (R : ℝ) (S : ℝ≥0)
    (ε : ℝ) (hε : 0 < ε) :
    (law μ (Label N D))
      {p | ENNReal.ofReal ε < averagedRunningCost control hN hActivity v T hT hv initialX initialY S p} ≤
      (law μ (Label N D))
        {p | pairExit control hN hActivity v T hT hv initialX initialY R p ≤ (S : ℝ≥0∞)} +
      (ENNReal.ofReal ε)⁻¹ *
        ∫⁻ p, averagedStoppedCost control hN hActivity v T hT hv initialX initialY R S p
          ∂law μ (Label N D) := by
  have hm := aemeasurable_averagedStoppedCost control hN hActivity v T hT hv initialX initialY μ
    hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R S
  have hmarkov := meas_ge_le_lintegral_div hm (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
    ENNReal.ofReal_ne_top
  have he := (measure_mono (μ := law μ (Label N D)) (runningCost_event_subset control hN hActivity v T hT hv
    initialX initialY R S (ENNReal.ofReal ε))).trans (measure_union_le _ _)
  apply he.trans
  simpa only [ENNReal.ofReal_coe_nnreal, ENNReal.div_eq_inv_mul] using add_le_add_left hmarkov
    ((law μ (Label N D))
      {p | pairExit control hN hActivity v T hT hv initialX initialY R p ≤ ENNReal.ofReal (S : ℝ)})

end CarryingCapacity.PopulationCouplingRemoval
