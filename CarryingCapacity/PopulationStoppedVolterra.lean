import CarryingCapacity.PopulationStoppedIntegrability
import CarryingCapacity.PopulationCouplingExit
import CarryingCapacity.PopulationCouplingTime

/-!
# Sharp stopped population integral inequality

The current average distance before the genuine joint exit is dominated by
the average of the actual coordinate running suprema. Combining this with
the derived local activity estimate and predictable compensation gives the
sharp integral inequality. Only a Lebesgue-null exit endpoint is removed;
the stopped cost retains the exit jump.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal

namespace CarryingCapacity.PopulationStoppedVolterra
open CommonInitialNoise ConfigurationLocalization PopulationCouplingAlgebra
open PopulationStoppedCoupling PopulationStoppedIntegrability
open SynchronousStoppedCompensation SynchronousStoppedRunningSupremum MarkedIntensity

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

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
local notation "X" => ConfigurationTimeDependent.process control hN initialX
local notation "Y" => DeterministicEnvironmentConfiguration.process control hN hActivity v T hT hv initialY

omit [MeasurableSpace A] in
/-- Averaging coordinate domination preserves the population normalization. -/
theorem currentMeanDistance_le_stoppedCost (R S s : ℝ) (p : Sample A (Label N D))
    (hs : s ∈ Icc 0 S)
    (hbefore : ENNReal.ofReal s ≤ pairExit control hN hActivity v T hT hv initialX initialY R p) :
    ENNReal.ofReal (meanDistance κ (X p s) (Y p s)) ≤
      averagedStoppedCost control hN hActivity v T hT hv initialX initialY R S p := by
  simp only [meanDistance, ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg N)),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => adaptedDistance_nonneg κ (X p s i) (Y p s i)),
    averagedStoppedCost]
  apply mul_le_mul_left'
  apply Finset.sum_le_sum
  intro i _
  exact currentCost_le_stoppedRunningCost VX hfin jump rX bX rY bY initialX initialY 0
    (jointRegion control R) (coordinateCost κ i) S s p hs hbefore

omit [MeasurableSpace A] in
/-- Strict pre-exit activity is controlled by the actual running cost and
actual empirical error, with the paper's coefficient independent of N. -/
theorem strictActivity_le_stoppedCost (hCoupling : MomentCouplingBound κ q)
    (B : ℝ) (hB : 0 ≤ B)
    (hEnv : ∀ s ∈ Icc 0 T,
      LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
    (R : ℝ) (hR : 0 ≤ R) (p : Sample A (Label N D)) (s : ℝ) (hs : s ∈ Icc 0 T) :
    (if ENNReal.ofReal s < pairExit control hN hActivity v T hT hv initialX initialY R p
      then ENNReal.ofReal (activity control hN hActivity v T hT hv initialX initialY p s) else 0) ≤
    ENNReal.ofReal (localizedConstant κ q hCoupling R B) *
      (averagedStoppedCost control hN hActivity v T hT hv initialX initialY R s p +
        ENNReal.ofReal (empiricalError control hN hActivity v T hT hv initialY p s)) := by
  split_ifs with hbefore
  · apply (ENNReal.ofReal_le_ofReal (activity_le_localized control hN hActivity v T hT hv initialX initialY
      hCoupling B hB hEnv R p s hs hbefore)).trans
    rw [ENNReal.ofReal_mul (localizedConstant_nonnegative κ q hCoupling R B hR hB),
      ENNReal.ofReal_add (meanDistance_nonnegative κ _ _)
        (empiricalError_nonnegative control hN hActivity v T hT hv initialY p s)]
    exact mul_le_mul_left' (add_le_add_right
      (currentMeanDistance_le_stoppedCost control hN hActivity v T hT hv initialX initialY
        R s s p ⟨hs.1, le_rfl⟩ hbefore.le) _) _
  · exact zero_le _

omit [MeasurableSpace A] in
/-- Pathwise time integration removes the single null exit endpoint and
retains the sharper running-cost feedback in the dominating integrand. -/
theorem lintegral_stoppedMeanActivity_le_sharp (hCoupling : MomentCouplingBound κ q)
    (B : ℝ) (hB : 0 ≤ B)
    (hEnv : ∀ s ∈ Icc 0 T,
      LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
    (R : ℝ) (hR : 0 ≤ R) (S : ℝ≥0) (hST : (S : ℝ) ≤ T) (p : Sample A (Label N D)) :
    (∫⁻ s in Ioc 0 (S : ℝ), stoppedMeanActivity control hN hActivity v T hT hv initialX initialY R p s
      ∂positiveVolume) ≤
    ∫⁻ s in Ioc 0 (S : ℝ), ENNReal.ofReal (localizedConstant κ q hCoupling R B) *
      (averagedStoppedCost control hN hActivity v T hT hv initialX initialY R s p +
        ENNReal.ofReal (empiricalError control hN hActivity v T hT hv initialY p s)) ∂positiveVolume := by
  unfold stoppedMeanActivity
  rw [lintegral_inclusive_eq_strict]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact strictActivity_le_stoppedCost control hN hActivity v T hT hv initialX initialY
    hCoupling B hB hEnv R hR p s ⟨hs.1.le, hs.2.trans hST⟩

/-- Strict mask used only under the ordinary time integral. -/
def strictStoppedMeanActivity (R : ℝ) (p : Sample A (Label N D)) (s : ℝ) : ℝ≥0∞ :=
  if ENNReal.ofReal s < pairExit control hN hActivity v T hT hv initialX initialY R p
  then stoppedMeanActivity control hN hActivity v T hT hv initialX initialY R p s else 0

omit [MeasurableSpace A] in
/-- The inclusive and strict masks have the same pathwise time integral. -/
theorem lintegral_stopped_eq_strict (R S : ℝ) (p : Sample A (Label N D)) :
    (∫⁻ s in Ioc 0 S, stoppedMeanActivity control hN hActivity v T hT hv initialX initialY R p s
      ∂positiveVolume) =
    ∫⁻ s in Ioc 0 S, strictStoppedMeanActivity control hN hActivity v T hT hv initialX initialY R p s
      ∂positiveVolume := by
  unfold stoppedMeanActivity
  rw [lintegral_inclusive_eq_strict]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  by_cases hb : ENNReal.ofReal s < pairExit control hN hActivity v T hT hv initialX initialY R p
  · simp only [strictStoppedMeanActivity, stoppedMeanActivity, hb, if_true, hs.1,
      hb.le, and_self]
  · simp only [strictStoppedMeanActivity, hb, if_false]

variable (μ : Measure A) [IsProbabilityMeasure μ]
  (hCoupling : MomentCouplingBound κ q) (hinitX : Measurable initialX) (hinitY : Measurable initialY)
  (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ s ∈ Icc 0 T,
    LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
  (hInitialX : Integrable (fun a => lyapunov control (initialX a)) μ)
  (hInitialY : Integrable (fun a => lyapunov control (initialY a)) μ)
include hCoupling hinitX hinitY hB hEnv hInitialX hInitialY

/-- The sharp sample-outer extended inequality follows directly from actual
compensation and the deterministic pre-exit bound. No stochastic estimate is assumed. -/
theorem expected_stoppedCost_le_sampleTime (R : ℝ) (hR : 0 ≤ R)
    (S : ℝ≥0) (hST : (S : ℝ) ≤ T) :
    (∫⁻ p, averagedStoppedCost control hN hActivity v T hT hv initialX initialY R S p
      ∂law μ (Label N D)) ≤
    ENNReal.ofReal (∫ a, meanDistance κ (initialX a) (initialY a) ∂μ) +
    ∫⁻ p, ∫⁻ s in Ioc 0 (S : ℝ), ENNReal.ofReal (localizedConstant κ q hCoupling R B) *
      (averagedStoppedCost control hN hActivity v T hT hv initialX initialY R s p +
        ENNReal.ofReal (empiricalError control hN hActivity v T hT hv initialY p s))
      ∂positiveVolume ∂law μ (Label N D) := by
  apply (expected_averagedStoppedCost_le control hN hActivity v T hT hv initialX initialY
    μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R S hST).trans
  rw [lintegral_initialMeanDistance_eq control hN initialX initialY μ hinitX hinitY hInitialX hInitialY]
  rw [← lintegral_lintegral_swap (aemeasurable_stoppedMeanActivity control hN hActivity v T hT hv initialX initialY
    μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R S hST)]
  exact add_le_add_left (lintegral_mono (fun p =>
    lintegral_stoppedMeanActivity_le_sharp control hN hActivity v T hT hv initialX initialY
      hCoupling B hB hEnv R hR S hST p)) _

/-- The strict field is jointly AE measurable using a measurable version of
the actual exit; no joint running-supremum measurability premise is used. -/
theorem aemeasurable_strictStoppedMeanActivity (R : ℝ) (S : ℝ≥0) (hST : (S : ℝ) ≤ T) :
    AEMeasurable (fun p : Sample A (Label N D) × ℝ =>
      strictStoppedMeanActivity control hN hActivity v T hT hv initialX initialY R p.1 p.2)
      ((law μ (Label N D)).prod (positiveVolume.restrict (Ioc 0 S))) := by
  have hσ := PopulationCouplingExit.aemeasurable_pairExit control hN hActivity v T hT hv initialX initialY
    μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R
  let σ := pairExit control hN hActivity v T hT hv initialX initialY R
  have hm := aemeasurable_stoppedMeanActivity control hN hActivity v T hT hv initialX initialY
    μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R S hST
  have hset : MeasurableSet {p : Sample A (Label N D) × ℝ |
      ENNReal.ofReal p.2 < hσ.mk σ p.1} :=
    measurableSet_lt measurable_snd.ennreal_ofReal (hσ.measurable_mk.comp measurable_fst)
  apply (hm.indicator hset).congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hσ.ae_eq_mk] with p hp
  simp only [Set.indicator_apply, Set.mem_setOf_eq, strictStoppedMeanActivity]
  change (if ENNReal.ofReal p.2 < hσ.mk σ p.1 then _ else _) =
    (if ENNReal.ofReal p.2 < σ p.1 then _ else _)
  change σ p.1 = hσ.mk σ p.1 at hp
  rw [hp]

/-- The sharp extended inequality in time-outer form. Sectionwise
measurability of the stopped supremum suffices for the exact expectation sum. -/
theorem expected_stoppedCost_le_timeExpected (R : ℝ) (hR : 0 ≤ R)
    (S : ℝ≥0) (hST : (S : ℝ) ≤ T) :
    (∫⁻ p, averagedStoppedCost control hN hActivity v T hT hv initialX initialY R S p
      ∂law μ (Label N D)) ≤
    ENNReal.ofReal (∫ a, meanDistance κ (initialX a) (initialY a) ∂μ) +
    ∫⁻ s in Ioc 0 (S : ℝ), ENNReal.ofReal (localizedConstant κ q hCoupling R B) *
      ((∫⁻ p, averagedStoppedCost control hN hActivity v T hT hv initialX initialY R s p ∂law μ (Label N D)) +
        ∫⁻ p, ENNReal.ofReal (empiricalError control hN hActivity v T hT hv initialY p s) ∂law μ (Label N D))
      ∂positiveVolume := by
  apply (expected_averagedStoppedCost_le control hN hActivity v T hT hv initialX initialY
    μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R S hST).trans
  rw [lintegral_initialMeanDistance_eq control hN initialX initialY μ hinitX hinitY hInitialX hInitialY]
  apply add_le_add_left
  rw [← lintegral_lintegral_swap (aemeasurable_stoppedMeanActivity control hN hActivity v T hT hv initialX initialY
    μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R S hST)]
  simp_rw [lintegral_stopped_eq_strict control hN hActivity v T hT hv initialX initialY R S]
  rw [lintegral_lintegral_swap (aemeasurable_strictStoppedMeanActivity control hN hActivity v T hT hv initialX initialY
    μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R S hST)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  calc
    _ ≤ ∫⁻ p, ENNReal.ofReal (localizedConstant κ q hCoupling R B) *
        (averagedStoppedCost control hN hActivity v T hT hv initialX initialY R s p +
          ENNReal.ofReal (empiricalError control hN hActivity v T hT hv initialY p s)) ∂law μ (Label N D) := by
      apply lintegral_mono
      intro p
      have h := strictActivity_le_stoppedCost control hN hActivity v T hT hv initialX initialY
        hCoupling B hB hEnv R hR p s ⟨hs.1.le, hs.2.trans hST⟩
      by_cases hb : ENNReal.ofReal s < pairExit control hN hActivity v T hT hv initialX initialY R p
      · simpa only [strictStoppedMeanActivity, stoppedMeanActivity, hb, if_true, hs.1,
          hb.le, and_self] using h
      · simpa only [strictStoppedMeanActivity, hb, if_false] using h
    _ = _ := by
      have hd : AEMeasurable
          (averagedStoppedCost control hN hActivity v T hT hv initialX initialY R s)
          (law μ (Label N D)) :=
        aemeasurable_averagedStoppedCost control hN hActivity v T hT hv initialX initialY
          μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R ⟨s, hs.1.le⟩
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hd]

/-- Genuine empirical-error integrability converts the actual extended
comparison to the real integral inequality used by integrable Gronwall.
For the nonlinear iid configuration these hypotheses are proved separately
from its actual particle marginal laws. -/
theorem expectedCost_le_integral
    (hError : ∀ s ∈ Icc 0 T, Integrable
      (fun p => empiricalError control hN hActivity v T hT hv initialY p s) (law μ (Label N D)))
    (hErrorProd : Integrable (fun p : Sample A (Label N D) × ℝ =>
      empiricalError control hN hActivity v T hT hv initialY p.1 p.2)
      ((law μ (Label N D)).prod (volume.restrict (Ioc 0 T))))
    (R : ℝ) (hR : 0 ≤ R) (S : ℝ≥0) (hST : (S : ℝ) ≤ T) :
    PopulationCouplingTime.expectedCost control hN hActivity v T hT hv initialX initialY μ R S ≤
    (∫ a, meanDistance κ (initialX a) (initialY a) ∂μ) +
      localizedConstant κ q hCoupling R B * ∫ s in Ioc 0 (S : ℝ),
        (PopulationCouplingTime.expectedCost control hN hActivity v T hT hv initialX initialY μ R s +
          ∫ p, empiricalError control hN hActivity v T hT hv initialY p s ∂law μ (Label N D)) := by
  let U := PopulationCouplingTime.expectedCost control hN hActivity v T hT hv initialX initialY μ R
  let β : ℝ → ℝ := fun s => ∫ p, empiricalError control hN hActivity v T hT hv initialY p s ∂law μ (Label N D)
  let a : ℝ := ∫ x, meanDistance κ (initialX x) (initialY x) ∂μ
  let C := localizedConstant κ q hCoupling R B
  have hC : 0 ≤ C := localizedConstant_nonnegative κ q hCoupling R B hR hB
  have ha : 0 ≤ a := integral_nonneg (fun x => meanDistance_nonnegative κ _ _)
  have hU (s : ℝ) : 0 ≤ U s :=
    PopulationCouplingTime.expectedCost_nonnegative control hN hActivity v T hT hv initialX initialY μ R s
  have hβ (s : ℝ) : 0 ≤ β s :=
    integral_nonneg (fun p => empiricalError_nonnegative control hN hActivity v T hT hv initialY p s)
  have hiU : IntegrableOn U (Ioc 0 (S : ℝ)) :=
    (PopulationCouplingTime.integrableOn_expectedCost_Ioc control hN hActivity v T hT hv initialX initialY
      μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R hR).mono_set (Ioc_subset_Ioc_right hST)
  have hiβFull : IntegrableOn β (Ioc 0 T) := hErrorProd.integral_prod_right
  have hiβ : IntegrableOn β (Ioc 0 (S : ℝ)) :=
    hiβFull.mono_set (Ioc_subset_Ioc_right hST)
  have hi : IntegrableOn (fun s => C * (U s + β s)) (Ioc 0 (S : ℝ)) :=
    (hiU.add hiβ).const_mul C
  have hn (s : ℝ) : 0 ≤ C * (U s + β s) := mul_nonneg hC (add_nonneg (hU s) (hβ s))
  have hrewrite :
      (∫⁻ s in Ioc 0 (S : ℝ), ENNReal.ofReal C *
        ((∫⁻ p, averagedStoppedCost control hN hActivity v T hT hv initialX initialY R s p ∂law μ (Label N D)) +
          ∫⁻ p, ENNReal.ofReal (empiricalError control hN hActivity v T hT hv initialY p s) ∂law μ (Label N D))
        ∂positiveVolume) = ∫⁻ s in Ioc 0 (S : ℝ), ENNReal.ofReal (C * (U s + β s)) := by
    rw [TimeDependentDynkin.positiveVolume_restrict_Ioc_zero]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.trans hST⟩
    have huEq : (∫⁻ p, averagedStoppedCost control hN hActivity v T hT hv initialX initialY R s p
        ∂law μ (Label N D)) = ENNReal.ofReal (U s) :=
      PopulationCouplingTime.expectedStoppedCost_eq_ofReal control hN hActivity v T hT hv initialX initialY
        μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R hR s hsT
    have hbEq : (∫⁻ p, ENNReal.ofReal (empiricalError control hN hActivity v T hT hv initialY p s)
        ∂law μ (Label N D)) = ENNReal.ofReal (β s) :=
      (ofReal_integral_eq_lintegral_ofReal (hError s hsT)
        (Eventually.of_forall (fun p => empiricalError_nonnegative control hN hActivity v T hT hv initialY p s))).symm
    rw [huEq, hbEq, ENNReal.ofReal_mul hC, ENNReal.ofReal_add (hU s) (hβ s)]
  have he : ENNReal.ofReal (U S) ≤ ENNReal.ofReal (a + ∫ s in Ioc 0 (S : ℝ), C * (U s + β s)) := by
    calc
      _ = ∫⁻ p, averagedStoppedCost control hN hActivity v T hT hv initialX initialY R S p ∂law μ (Label N D) :=
        (PopulationCouplingTime.expectedStoppedCost_eq_ofReal control hN hActivity v T hT hv initialX initialY
          μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R hR S ⟨S.coe_nonneg, hST⟩).symm
      _ ≤ ENNReal.ofReal a + ∫⁻ s in Ioc 0 (S : ℝ), ENNReal.ofReal (C * (U s + β s)) := by
        have hh := expected_stoppedCost_le_timeExpected control hN hActivity v T hT hv initialX initialY
          μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R hR S hST
        exact hh.trans_eq (congrArg (fun z => ENNReal.ofReal a + z) hrewrite)
      _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn),
          ENNReal.ofReal_add ha (integral_nonneg hn)]
  have hr := (ENNReal.ofReal_le_ofReal_iff (add_nonneg ha (integral_nonneg hn))).mp he
  simpa only [integral_const_mul] using hr

end CarryingCapacity.PopulationStoppedVolterra
