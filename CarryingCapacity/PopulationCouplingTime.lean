import CarryingCapacity.PopulationStoppedIntegrability
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Time integrability of the genuine stopped population cost

The all-real running supremum increases with the horizon. Its extended
expectation is therefore measurable without a joint-supremum measurability
assumption. The previously proved finite stopped-cost estimate makes its real
value monotone and integrable on the construction horizon.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal

namespace CarryingCapacity.PopulationCouplingTime
open CommonInitialNoise ConfigurationLocalization PopulationStoppedCoupling
open PopulationStoppedIntegrability

/-- Enlarging a horizon enlarges the actual supremum, including empty negative
horizons. No regularity or measurability of the function is needed. -/
theorem monotone_intervalSup (f : ℝ → ℝ≥0∞) :
    Monotone (SynchronousRunningSupremum.intervalSup f) := by
  intro s t hst
  apply iSup_le
  intro r
  exact le_iSup_of_le (⟨r.1, r.2.1, r.2.2.trans hst⟩ : Icc (0 : ℝ) t) le_rfl

variable {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N) (hActivity : MomentActivityBound κ q)
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))
  {A : Type*} [MeasurableSpace A] (initialX initialY : A → Configuration N D)

omit [MeasurableSpace A] in
/-- Each actual coordinate cost increases with its observation horizon. -/
theorem monotone_coordinateStoppedCost (R : ℝ) (i : Fin N) (p : Sample A (Label N D)) :
    Monotone (fun S => coordinateStoppedCost control hN hActivity v T hT hv initialX initialY R i S p) :=
  monotone_intervalSup _

omit [MeasurableSpace A] in
/-- The finite average is taken after the coordinate suprema and remains
monotone in the horizon for every sample. -/
theorem monotone_averagedStoppedCost (R : ℝ) (p : Sample A (Label N D)) :
    Monotone (fun S => averagedStoppedCost control hN hActivity v T hT hv initialX initialY R S p) := by
  intro s t hst
  apply mul_le_mul_left'
  exact Finset.sum_le_sum (fun i _ =>
    monotone_coordinateStoppedCost control hN hActivity v T hT hv initialX initialY R i p hst)

/-- The actual extended expected averaged stopped running cost. -/
def expectedStoppedCost (μ : Measure A) (R S : ℝ) : ℝ≥0∞ :=
  ∫⁻ p, averagedStoppedCost control hN hActivity v T hT hv initialX initialY R S p
    ∂law μ (Label N D)

/-- Its real value; genuine finiteness on the construction horizon is proved
below before using this as the ordinary expectation. -/
def expectedCost (μ : Measure A) (R S : ℝ) : ℝ :=
  (expectedStoppedCost control hN hActivity v T hT hv initialX initialY μ R S).toReal

/-- Extended expectations are globally monotone without any moment hypothesis. -/
theorem monotone_expectedStoppedCost (μ : Measure A) (R : ℝ) :
    Monotone (expectedStoppedCost control hN hActivity v T hT hv initialX initialY μ R) := by
  intro s t hst
  exact lintegral_mono (fun p =>
    monotone_averagedStoppedCost control hN hActivity v T hT hv initialX initialY R p hst)

/-- Monotonicity supplies actual time measurability of the extended mean. -/
theorem measurable_expectedStoppedCost (μ : Measure A) (R : ℝ) :
    Measurable (expectedStoppedCost control hN hActivity v T hT hv initialX initialY μ R) :=
  (monotone_expectedStoppedCost control hN hActivity v T hT hv initialX initialY μ R).measurable

/-- The real-valued mean is measurable even outside the interval where its
extended value is known to be finite. -/
theorem measurable_expectedCost (μ : Measure A) (R : ℝ) :
    Measurable (expectedCost control hN hActivity v T hT hv initialX initialY μ R) :=
  (measurable_expectedStoppedCost control hN hActivity v T hT hv initialX initialY μ R).ennreal_toReal

theorem expectedCost_nonnegative (μ : Measure A) (R S : ℝ) :
    0 ≤ expectedCost control hN hActivity v T hT hv initialX initialY μ R S :=
  ENNReal.toReal_nonneg

section FiniteHorizon
variable (μ : Measure A) [IsProbabilityMeasure μ]
  (hCoupling : MomentCouplingBound κ q) (hinitX : Measurable initialX) (hinitY : Measurable initialY)
  (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ s ∈ Icc 0 T,
    LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
  (hInitialX : Integrable (fun a => lyapunov control (initialX a)) μ)
  (hInitialY : Integrable (fun a => lyapunov control (initialY a)) μ)
include hCoupling hinitX hinitY hB hEnv hInitialX hInitialY

/-- Finiteness is derived from genuine stopped compensation and the original
averaged Lyapunov assumptions, not from a supplied expected-cost bound. -/
theorem expectedStoppedCost_lt_top (R : ℝ) (hR : 0 ≤ R) (s : ℝ) (hs : s ∈ Icc 0 T) :
    expectedStoppedCost control hN hActivity v T hT hv initialX initialY μ R s < ⊤ :=
  lintegral_averagedStoppedCost_lt_top control hN hActivity v T hT hv initialX initialY
    μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R hR ⟨s, hs.1⟩ hs.2

/-- On the true construction horizon the real value is exactly the ordinary
expectation of the actual stopped running cost. -/
theorem expectedCost_eq_integral (R : ℝ) (hR : 0 ≤ R) (s : ℝ) (hs : s ∈ Icc 0 T) :
    expectedCost control hN hActivity v T hT hv initialX initialY μ R s =
      ∫ p, (averagedStoppedCost control hN hActivity v T hT hv initialX initialY R s p).toReal
        ∂law μ (Label N D) := by
  symm
  exact integral_toReal
    (aemeasurable_averagedStoppedCost control hN hActivity v T hT hv initialX initialY
      μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R ⟨s, hs.1⟩)
    (ae_averagedStoppedCost_lt_top control hN hActivity v T hT hv initialX initialY
      μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R hR ⟨s, hs.1⟩ hs.2)

/-- The extended mean is genuinely the `ofReal` of the real mean throughout
the construction horizon. -/
theorem expectedStoppedCost_eq_ofReal (R : ℝ) (hR : 0 ≤ R) (s : ℝ) (hs : s ∈ Icc 0 T) :
    expectedStoppedCost control hN hActivity v T hT hv initialX initialY μ R s =
      ENNReal.ofReal (expectedCost control hN hActivity v T hT hv initialX initialY μ R s) := by
  exact (ENNReal.ofReal_toReal (expectedStoppedCost_lt_top control hN hActivity v T hT hv
    initialX initialY μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R hR s hs).ne).symm

/-- Finiteness makes `toReal` preserve the horizon order on the actual interval. -/
theorem monotoneOn_expectedCost (R : ℝ) (hR : 0 ≤ R) :
    MonotoneOn (expectedCost control hN hActivity v T hT hv initialX initialY μ R) (Icc 0 T) := by
  intro s _ t ht hst
  exact ENNReal.toReal_mono
    (expectedStoppedCost_lt_top control hN hActivity v T hT hv initialX initialY
      μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R hR t ht).ne
    (monotone_expectedStoppedCost control hN hActivity v T hT hv initialX initialY μ R hst)

/-- The genuine expected stopped cost is time integrable. No time continuity
of the running supremum or its expectation is required. -/
theorem integrableOn_expectedCost (R : ℝ) (hR : 0 ≤ R) :
    IntegrableOn (expectedCost control hN hActivity v T hT hv initialX initialY μ R) (Icc 0 T) :=
  MonotoneOn.integrableOn_isCompact isCompact_Icc
    (monotoneOn_expectedCost control hN hActivity v T hT hv initialX initialY
      μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R hR)

/-- The same time integrability on the half-open interval used in Dynkin and
Gronwall identities. -/
theorem integrableOn_expectedCost_Ioc (R : ℝ) (hR : 0 ≤ R) :
    IntegrableOn (expectedCost control hN hActivity v T hT hv initialX initialY μ R) (Ioc 0 T) :=
  (integrableOn_expectedCost control hN hActivity v T hT hv initialX initialY
    μ hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R hR).mono_set Ioc_subset_Icc_self

end FiniteHorizon
end CarryingCapacity.PopulationCouplingTime
