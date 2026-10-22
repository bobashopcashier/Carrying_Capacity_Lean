import CarryingCapacity.PopulationStoppedCoupling

/-!
# Genuine integrability of the stopped averaged population cost

Strictly before the common Lyapunov exit, both paired distance and empirical
error are bounded by deterministic moment bounds. Actual stopped compensation
then gives a finite expected running cost. Integrability is proved before the
extended expectation is converted to a real expectation.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal

namespace CarryingCapacity.PopulationStoppedIntegrability
open CommonInitialNoise ConfigurationLocalization PopulationCouplingAlgebra PopulationStoppedCoupling
open SynchronousStoppedCompensation MarkedIntensity

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

variable {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N) (hActivity : MomentActivityBound κ q)
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))
  {A : Type*} [MeasurableSpace A] (initialX initialY : A → Configuration N D)

local notation "X" => ConfigurationTimeDependent.process control hN initialX
local notation "Y" => DeterministicEnvironmentConfiguration.process control hN hActivity v T hT hv initialY

include hN in
/-- Genuine initial distance is bounded by the two empirical Lyapunov values. -/
theorem meanDistance_le_lyapunov (z w : Configuration N D) :
    meanDistance κ z w ≤ lyapunov control z + lyapunov control w :=
  (meanDistance_le_moments κ hN z w).trans
    (add_le_add (moment_empirical_le_lyapunov κ q control hN z)
      (moment_empirical_le_lyapunov κ q control hN w))

/-- The deterministic activity bound used only to establish finiteness. -/
def activityBound (hCoupling : MomentCouplingBound κ q) (R B : ℝ) : ℝ :=
  localizedConstant κ q hCoupling R B * (2 * R + B)

theorem activityBound_nonnegative (hCoupling : MomentCouplingBound κ q)
    (R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B) :
    0 ≤ activityBound hCoupling R B :=
  mul_nonneg (localizedConstant_nonnegative κ q hCoupling R B hR hB) (by positivity)

omit [MeasurableSpace A] in
/-- The actual paired distance is bounded at every strict pre-exit time. -/
theorem meanDistance_le_before (R : ℝ) (p : Sample A (Label N D)) (s : ℝ)
    (hs : 0 ≤ s)
    (hbefore : ENNReal.ofReal s < pairExit control hN hActivity v T hT hv initialX initialY R p) :
    meanDistance κ (X p s) (Y p s) ≤ R :=
  (meanDistance_le_lyapunov control hN _ _).trans
    (lyapunov_pair_lt_before control hN hActivity v T hT hv initialX initialY R p s hs hbefore).le

omit [MeasurableSpace A] in
/-- Transport to the prescribed environment is bounded before the joint exit. -/
theorem empiricalError_le_before (B : ℝ) (hB : 0 ≤ B)
    (hEnv : ∀ s ∈ Icc 0 T,
      LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
    (R : ℝ) (p : Sample A (Label N D)) (s : ℝ) (hs : s ∈ Icc 0 T)
    (hbefore : ENNReal.ofReal s < pairExit control hN hActivity v T hT hv initialX initialY R p) :
    empiricalError control hN hActivity v T hT hv initialY p s ≤ R + B := by
  have hpair := lyapunov_pair_lt_before control hN hActivity v T hT hv initialX initialY R p s hs.1 hbefore
  have hVX := lyapunov_nonnegative control (X p s)
  have hMY := moment_empirical_le_lyapunov κ q control hN (Y p s)
  have hMV := DeterministicEnvironmentGeneralCoupling.moment_le_of_lyapunov_bound control
    (v s) B hB (hEnv s hs)
  exact (wasserstein_le_moments (empiricalLaw κ hN (Y p s)) (v s)).trans (by linarith)

omit [MeasurableSpace A] in
/-- Actual activity is uniformly bounded before the exit, with no N factor. -/
theorem activity_le_bound_before (hCoupling : MomentCouplingBound κ q)
    (B : ℝ) (hB : 0 ≤ B)
    (hEnv : ∀ s ∈ Icc 0 T,
      LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
    (R : ℝ) (hR : 0 ≤ R) (p : Sample A (Label N D)) (s : ℝ) (hs : s ∈ Icc 0 T)
    (hbefore : ENNReal.ofReal s < pairExit control hN hActivity v T hT hv initialX initialY R p) :
    activity control hN hActivity v T hT hv initialX initialY p s ≤ activityBound hCoupling R B := by
  apply (activity_le_localized control hN hActivity v T hT hv initialX initialY
    hCoupling B hB hEnv R p s hs hbefore).trans
  apply mul_le_mul_of_nonneg_left _ (localizedConstant_nonnegative κ q hCoupling R B hR hB)
  have hd := meanDistance_le_before control hN hActivity v T hT hv initialX initialY R p s hs.1 hbefore
  have he := empiricalError_le_before control hN hActivity v T hT hv initialX initialY B hB hEnv R p s hs hbefore
  linarith

omit [MeasurableSpace A] in
/-- Removing only the null time endpoint permits the strict pre-exit bound;
the counting integral still includes the exit jump. -/
theorem lintegral_stoppedMeanActivity_le (hCoupling : MomentCouplingBound κ q)
    (B : ℝ) (hB : 0 ≤ B)
    (hEnv : ∀ s ∈ Icc 0 T,
      LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
    (R : ℝ) (hR : 0 ≤ R) (S : ℝ≥0) (hST : (S : ℝ) ≤ T) (p : Sample A (Label N D)) :
    (∫⁻ s in Ioc 0 (S : ℝ), stoppedMeanActivity control hN hActivity v T hT hv initialX initialY R p s
      ∂positiveVolume) ≤ ENNReal.ofReal (activityBound hCoupling R B * S) := by
  unfold stoppedMeanActivity
  rw [lintegral_inclusive_eq_strict]
  calc
    _ ≤ ∫⁻ _s in Ioc 0 (S : ℝ), ENNReal.ofReal (activityBound hCoupling R B) ∂positiveVolume := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      split_ifs with hb
      · exact ENNReal.ofReal_le_ofReal (activity_le_bound_before control hN hActivity v T hT hv initialX initialY
          hCoupling B hB hEnv R hR p s ⟨hs.1.le, hs.2.trans hST⟩ hb)
      · exact zero_le _
    _ = _ := by
      simp only [lintegral_const, Measure.restrict_apply_univ,
        MarkedCountMoments.positiveVolume_Ioc 0 S le_rfl, sub_zero]
      rw [ENNReal.ofReal_mul (activityBound_nonnegative hCoupling R B hR hB)]


section InitialMoment
variable (μ : Measure A) [IsProbabilityMeasure μ]
  (hinitX : Measurable initialX) (hinitY : Measurable initialY)
  (hInitialX : Integrable (fun a => lyapunov control (initialX a)) μ)
  (hInitialY : Integrable (fun a => lyapunov control (initialY a)) μ)
include hinitX hinitY hInitialX hInitialY hN

omit [IsProbabilityMeasure μ] in
/-- Initial paired distance is genuinely integrable from the original two
averaged Lyapunov assumptions, without a supplied distance-moment premise. -/
theorem integrable_initialMeanDistance :
    Integrable (fun a => meanDistance κ (initialX a) (initialY a)) μ := by
  apply (hInitialX.add hInitialY).mono'
    (((measurable_of_countable (fun z : Configuration N D × Configuration N D =>
      meanDistance κ z.1 z.2)).comp (hinitX.prodMk hinitY)).aestronglyMeasurable)
  exact Eventually.of_forall (fun a => by
    change ‖meanDistance κ (initialX a) (initialY a)‖ ≤
      lyapunov control (initialX a) + lyapunov control (initialY a)
    rw [Real.norm_of_nonneg (meanDistance_nonnegative κ _ _)]
    exact meanDistance_le_lyapunov control hN _ _)

/-- The same initial moment is finite on the actual initial/noise product. -/
theorem integrable_initialMeanDistance_record :
    Integrable (fun p : Sample A (Label N D) => meanDistance κ (initialX p.1) (initialY p.1))
      (law μ (Label N D)) := by
  have hi : Integrable (fun a => meanDistance κ (initialX a) (initialY a))
      ((law μ (Label N D)).map Prod.fst) := by
    rw [map_initial]
    exact integrable_initialMeanDistance control hN initialX initialY μ hinitX hinitY hInitialX hInitialY
  exact hi.comp_measurable measurable_fst

/-- The extended initial expectation equals the actual real initial mean. -/
theorem lintegral_initialMeanDistance_eq :
    (∫⁻ p : Sample A (Label N D), ENNReal.ofReal (meanDistance κ (initialX p.1) (initialY p.1))
      ∂law μ (Label N D)) = ENNReal.ofReal (∫ a, meanDistance κ (initialX a) (initialY a) ∂μ) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_initialMeanDistance_record control hN initialX initialY μ hinitX hinitY hInitialX hInitialY)
    (Eventually.of_forall (fun p => meanDistance_nonnegative κ _ _))]
  simpa only [measureReal_univ_eq_one, one_smul] using congrArg ENNReal.ofReal (integral_fun_fst
    (μ := μ) (ν := MarkedNoise.law (Label N D)) (fun a => meanDistance κ (initialX a) (initialY a)))

end InitialMoment

section StoppedMoment
variable (μ : Measure A) [IsProbabilityMeasure μ]
  (hCoupling : MomentCouplingBound κ q) (hinitX : Measurable initialX) (hinitY : Measurable initialY)
  (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ s ∈ Icc 0 T,
    LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
  (hInitialX : Integrable (fun a => lyapunov control (initialX a)) μ)
  (hInitialY : Integrable (fun a => lyapunov control (initialY a)) μ)
include hCoupling hinitX hinitY hB hEnv hInitialX hInitialY

/-- Fubini transfers the deterministic per-path activity bound to the actual
expected compensated activity on the time horizon. -/
theorem lintegral_expected_stoppedMeanActivity_le (R : ℝ) (hR : 0 ≤ R)
    (S : ℝ≥0) (hST : (S : ℝ) ≤ T) :
    (∫⁻ s in Ioc 0 (S : ℝ), ∫⁻ p,
      stoppedMeanActivity control hN hActivity v T hT hv initialX initialY R p s
        ∂law μ (Label N D) ∂positiveVolume) ≤ ENNReal.ofReal (activityBound hCoupling R B * S) := by
  rw [← lintegral_lintegral_swap (aemeasurable_stoppedMeanActivity control hN hActivity v T hT hv initialX initialY
    μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R S hST)]
  calc
    _ ≤ ∫⁻ _p, ENNReal.ofReal (activityBound hCoupling R B * S) ∂law μ (Label N D) :=
      lintegral_mono (fun p => lintegral_stoppedMeanActivity_le control hN hActivity v T hT hv initialX initialY
        hCoupling B hB hEnv R hR S hST p)
    _ = _ := by simp

/-- A finite explicit expectation bound derived from actual compensated
increments and initial Lyapunov integrability, before any real conversion. -/
theorem expected_averagedStoppedCost_le_finite (R : ℝ) (hR : 0 ≤ R)
    (S : ℝ≥0) (hST : (S : ℝ) ≤ T) :
    (∫⁻ p, averagedStoppedCost control hN hActivity v T hT hv initialX initialY R S p
      ∂law μ (Label N D)) ≤
    ENNReal.ofReal ((∫ a, meanDistance κ (initialX a) (initialY a) ∂μ) + activityBound hCoupling R B * S) := by
  apply (expected_averagedStoppedCost_le control hN hActivity v T hT hv initialX initialY
    μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R S hST).trans
  rw [lintegral_initialMeanDistance_eq control hN initialX initialY μ hinitX hinitY hInitialX hInitialY]
  apply (add_le_add_left (lintegral_expected_stoppedMeanActivity_le control hN hActivity v T hT hv initialX initialY
    μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R hR S hST) _).trans
  rw [ENNReal.ofReal_add (integral_nonneg (fun a => meanDistance_nonnegative κ _ _))
    (mul_nonneg (activityBound_nonnegative hCoupling R B hR hB) S.coe_nonneg)]

/-- The stopped average has a genuinely finite extended expectation. -/
theorem lintegral_averagedStoppedCost_lt_top (R : ℝ) (hR : 0 ≤ R)
    (S : ℝ≥0) (hST : (S : ℝ) ≤ T) :
    (∫⁻ p, averagedStoppedCost control hN hActivity v T hT hv initialX initialY R S p
      ∂law μ (Label N D)) < ⊤ :=
  (expected_averagedStoppedCost_le_finite control hN hActivity v T hT hv initialX initialY
    μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R hR S hST).trans_lt ENNReal.ofReal_lt_top

/-- Consequently the actual uncountable running cost is finite almost surely. -/
theorem ae_averagedStoppedCost_lt_top (R : ℝ) (hR : 0 ≤ R)
    (S : ℝ≥0) (hST : (S : ℝ) ≤ T) :
    ∀ᵐ p ∂law μ (Label N D), averagedStoppedCost control hN hActivity v T hT hv initialX initialY R S p < ⊤ :=
  ae_lt_top' (aemeasurable_averagedStoppedCost control hN hActivity v T hT hv initialX initialY
    μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R S)
    (lintegral_averagedStoppedCost_lt_top control hN hActivity v T hT hv initialX initialY
      μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R hR S hST).ne

/-- Genuine real integrability follows from the extended estimate and actual
supremum measurability; it is not an input to the compensation argument. -/
theorem integrable_averagedStoppedCost_toReal (R : ℝ) (hR : 0 ≤ R)
    (S : ℝ≥0) (hST : (S : ℝ) ≤ T) :
    Integrable (fun p => (averagedStoppedCost control hN hActivity v T hT hv initialX initialY R S p).toReal)
      (law μ (Label N D)) :=
  integrable_toReal_of_lintegral_ne_top
    (aemeasurable_averagedStoppedCost control hN hActivity v T hT hv initialX initialY
      μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R S)
    (lintegral_averagedStoppedCost_lt_top control hN hActivity v T hT hv initialX initialY
      μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R hR S hST).ne

/-- The corresponding ordinary expectation bound has already-established
integrability and is safe to use in the subsequent real Gronwall argument. -/
theorem integral_averagedStoppedCost_toReal_le (R : ℝ) (hR : 0 ≤ R)
    (S : ℝ≥0) (hST : (S : ℝ) ≤ T) :
    (∫ p, (averagedStoppedCost control hN hActivity v T hT hv initialX initialY R S p).toReal
      ∂law μ (Label N D)) ≤
      (∫ a, meanDistance κ (initialX a) (initialY a) ∂μ) + activityBound hCoupling R B * S := by
  rw [integral_toReal
    (aemeasurable_averagedStoppedCost control hN hActivity v T hT hv initialX initialY
      μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R S)
    (ae_averagedStoppedCost_lt_top control hN hActivity v T hT hv initialX initialY
      μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R hR S hST)]
  have hn : 0 ≤ (∫ a, meanDistance κ (initialX a) (initialY a) ∂μ) + activityBound hCoupling R B * S :=
    add_nonneg (integral_nonneg (fun a => meanDistance_nonnegative κ _ _))
      (mul_nonneg (activityBound_nonnegative hCoupling R B hR hB) S.coe_nonneg)
  simpa only [ENNReal.toReal_ofReal hn] using ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (expected_averagedStoppedCost_le_finite control hN hActivity v T hT hv initialX initialY
      μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R hR S hST)

end StoppedMoment
end CarryingCapacity.PopulationStoppedIntegrability
