import CarryingCapacity.RateTableSumCompensation
import CarryingCapacity.RightContinuousProcessMeasurability

/-!
# Genuine real integration of stopped current activity

Adapted càdlàg scalar rate tables provide measurable right-grid versions of
all current-rate observables. Thus finite extended expected activity implies
actual product integrability and the ordinary iterated integral identity.
The original environment space need not carry a Polish instance.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal BigOperators

namespace CarryingCapacity.RandomEnvironmentActivityIntegral
open RandomEnvironmentCompensation RateTableCompensation MarkedIntensity
  RightContinuousProcessMeasurability
local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

variable {Ω E V J : Type*} [mΩ : MeasurableSpace Ω]
  [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
  [Countable E] [MeasurableSingletonClass E] [DiscreteTopology E]
  [Fintype J] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  (F : Filtration ℝ mΩ) (jump : J → E → E) (q : J → E → V → ℝ)
  (X Y : ℝ → Ω → E) (U W : ℝ → Ω → V) (e : E)

/-- The original current activity, stopped inclusively and zero before time
zero and after the specified horizon. -/
def stoppedActivity (τ : Ω → ℝ≥0∞) (T : ℝ) (ρ : E → E → ℝ) (p : Ω × ℝ) : ℝ :=
  if p.2 ∈ Ioc 0 T ∧ ENNReal.ofReal p.2 ≤ τ p.1 then
    ∑ j, currentActivity jump q X Y U W ρ j p.1 p.2 else 0

omit mΩ [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
  [Countable E] [MeasurableSingletonClass E] [DiscreteTopology E]
  [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] in
theorem lintegral_stoppedActivity (τ : Ω → ℝ≥0∞) (T : ℝ) (ρ : E → E → ℝ) (ω : Ω) :
    (∫⁻ t, ENNReal.ofReal (stoppedActivity jump q X Y U W τ T ρ (ω,t)) ∂positiveVolume) =
      ∫⁻ t in Ioc 0 T, if ENNReal.ofReal t ≤ τ ω then
        ENNReal.ofReal (∑ j, currentActivity jump q X Y U W ρ j ω t) else 0 ∂positiveVolume := by
  rw [← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ Ioc 0 T <;> by_cases hs : ENNReal.ofReal t ≤ τ ω <;>
    simp [stoppedActivity,ht,hs]

omit mΩ [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
  [Countable E] [MeasurableSingletonClass E] [DiscreteTopology E]
  [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] in
theorem integral_stoppedActivity (τ : Ω → ℝ≥0∞) (T : ℝ) (ρ : E → E → ℝ) (ω : Ω) :
    (∫ t, stoppedActivity jump q X Y U W τ T ρ (ω,t) ∂positiveVolume) =
      ∫ t in Ioc 0 T, if ENNReal.ofReal t ≤ τ ω then
        ∑ j, currentActivity jump q X Y U W ρ j ω t else 0 ∂positiveVolume := by
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Ioc 0 T <;> by_cases hs : ENNReal.ofReal t ≤ τ ω <;>
    simp [stoppedActivity,ht,hs]

variable (hq : ∀ j x, Continuous (q j x))
  (hX : ∀ s, 0 ≤ s → Measurable[F s] (X s))
  (hY : ∀ s, 0 ≤ s → Measurable[F s] (Y s))
  (hU : ∀ s, 0 ≤ s → Measurable[F s] (U s))
  (hW : ∀ s, 0 ≤ s → Measurable[F s] (W s))
  (P : Measure Ω) [IsProbabilityMeasure P]
  (τ : Ω → ℝ≥0∞)
  (hτ : ∀ s : ℝ, 0 ≤ s → MeasurableSet[F s] {ω | τ ω ≤ ENNReal.ofReal s})
  (hnonneg : ∀ j x u, 0 ≤ q j x u)
  (hcX : ∀ᵐ ω ∂P, CadlagNonnegative (fun t => X t ω))
  (hcY : ∀ᵐ ω ∂P, CadlagNonnegative (fun t => Y t ω))
  (hcU : ∀ᵐ ω ∂P, CadlagNonnegative (fun t => U t ω))
  (hcW : ∀ᵐ ω ∂P, CadlagNonnegative (fun t => W t ω))

omit F e hq hX hY hU hW P hτ hcX hcY hcU hcW mΩ [TopologicalSpace E]
  [PolishSpace E] [MeasurableSpace E] [BorelSpace E] [Countable E]
  [MeasurableSingletonClass E] [DiscreteTopology E] [TopologicalSpace V]
  [MeasurableSpace V] [BorelSpace V] in
include hnonneg in
theorem stoppedActivity_nonnegative (T : ℝ) (ρ : E → E → ℝ) (p : Ω × ℝ) :
    0 ≤ stoppedActivity jump q X Y U W τ T ρ p := by
  unfold stoppedActivity
  split_ifs
  · exact Finset.sum_nonneg (fun j _ =>
      SynchronousPositiveIncrement.heightActivity_nonnegative ρ jump j _ _ _ _
        (hnonneg j _ _) (hnonneg j _ _))
  · exact le_rfl

include e hq hX hY hU hW hτ hnonneg hcX hcY hcU hcW

omit [DiscreteTopology E] [IsProbabilityMeasure P] in
/-- Joint AE measurability is derived from adapted evaluations and the actual
right-continuous sample paths, not imposed as an additional process premise. -/
theorem aemeasurable_stoppedActivity (T : ℝ) (ρ : E → E → ℝ) :
    AEMeasurable (stoppedActivity jump q X Y U W τ T ρ) (P.prod positiveVolume) := by
  let Xv := version X e
  let Yv := version Y e
  let Uv := version (fun t ω => table q (U t ω)) (fun _ => 0)
  let Wv := version (fun t ω => table q (W t ω)) (fun _ => 0)
  have hx : Measurable (fun p : Ω × ℝ => Xv p.1 p.2) :=
    measurable_version X (fun s hs => (hX s hs).mono (F.le s) le_rfl) e
  have hy : Measurable (fun p : Ω × ℝ => Yv p.1 p.2) :=
    measurable_version Y (fun s hs => (hY s hs).mono (F.le s) le_rfl) e
  have hu : Measurable (fun p : Ω × ℝ => Uv p.1 p.2) :=
    measurable_version _ (fun s hs =>
      (measurable_table_process F q U hq hU s hs).mono (F.le s) le_rfl) _
  have hw : Measurable (fun p : Ω × ℝ => Wv p.1 p.2) :=
    measurable_version _ (fun s hs =>
      (measurable_table_process F q W hq hW s hs).mono (F.le s) le_rfl) _
  have hσ := measurable_of_stopping_sublevels F τ hτ
  let g := fun p : Ω × ℝ => if p.2 ∈ Ioc 0 T ∧ ENNReal.ofReal p.2 ≤ τ p.1 then
    ∑ j, SynchronousPositiveIncrement.heightActivity ρ jump j
      (evaluation j (Xv p.1 p.2) (Uv p.1 p.2))
      (evaluation j (Yv p.1 p.2) (Wv p.1 p.2)) (Xv p.1 p.2) (Yv p.1 p.2) else 0
  have hg : Measurable g := by
    apply Measurable.ite ((measurableSet_Ioc.preimage measurable_snd).inter
      (measurableSet_le measurable_snd.ennreal_ofReal (hσ.comp measurable_fst)))
    · exact Finset.measurable_sum _ (fun j _ =>
        SynchronousCompensation.measurable_heightActivity_comp jump ρ j _ _ _ _
          (measurable_rate_comp evaluation continuous_evaluation j _ _ hx hu)
          (measurable_rate_comp evaluation continuous_evaluation j _ _ hy hw) hx hy)
    · exact measurable_const
  apply hg.aemeasurable.congr
  have he : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t →
      Xv ω t = X t ω ∧ Yv ω t = Y t ω ∧ Uv ω t = table q (U t ω) ∧ Wv ω t = table q (W t ω) := by
    filter_upwards [hcX,hcY,hcU,hcW] with ω hxc hyc huc hwc
    intro t ht
    exact ⟨version_eq X e ω t ht (hxc.1 t ht), version_eq Y e ω t ht (hyc.1 t ht),
      version_eq _ _ ω t ht ((cadlag_comp (table q) (continuous_table q hq) _ huc).1 t ht),
      version_eq _ _ ω t ht ((cadlag_comp (table q) (continuous_table q hq) _ hwc).1 t ht)⟩
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae he] with p hp
  by_cases ht : p.2 ∈ Ioc 0 T ∧ ENNReal.ofReal p.2 ≤ τ p.1
  · obtain ⟨heX,heY,heU,heW⟩ := hp p.2 ht.1.1.le
    simp only [g,stoppedActivity,ht,if_true,heX,heY,heU,heW,
      evaluation_table q hnonneg,currentActivity]
  · simp only [g,stoppedActivity,ht,if_false]

omit [DiscreteTopology E] [IsProbabilityMeasure P] in
/-- Finite extended expected stopped activity gives genuine product
integrability; the conclusion is not an assumed Bochner integral. -/
theorem integrable_stoppedActivity_of_lintegral_lt_top (T : ℝ) (ρ : E → E → ℝ)
    (hfin : (∫⁻ ω, ∫⁻ t, ENNReal.ofReal (stoppedActivity jump q X Y U W τ T ρ (ω,t))
      ∂positiveVolume ∂P) < ⊤) :
    Integrable (stoppedActivity jump q X Y U W τ T ρ) (P.prod positiveVolume) := by
  have hm := aemeasurable_stoppedActivity F jump q X Y U W e hq hX hY hU hW
    P τ hτ hnonneg hcX hcY hcU hcW T ρ
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall
    (stoppedActivity_nonnegative jump q X Y U W τ hnonneg T ρ))]
  rwa [lintegral_prod _ hm.ennreal_ofReal]

omit [DiscreteTopology E] in
/-- Actual real iterated integration agrees with the extended expected
activity after the finite-integral condition has been proved. -/
theorem toReal_lintegral_stoppedActivity (T : ℝ) (ρ : E → E → ℝ)
    (hfin : (∫⁻ ω, ∫⁻ t, ENNReal.ofReal (stoppedActivity jump q X Y U W τ T ρ (ω,t))
      ∂positiveVolume ∂P) < ⊤) :
    (∫⁻ ω, ∫⁻ t, ENNReal.ofReal (stoppedActivity jump q X Y U W τ T ρ (ω,t))
      ∂positiveVolume ∂P).toReal =
      ∫ ω, ∫ t, stoppedActivity jump q X Y U W τ T ρ (ω,t) ∂positiveVolume ∂P := by
  have hi := integrable_stoppedActivity_of_lintegral_lt_top F jump q X Y U W e hq hX hY hU hW
    P τ hτ hnonneg hcX hcY hcU hcW T ρ hfin
  rw [← lintegral_prod _ hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
  rw [← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall
    (stoppedActivity_nonnegative jump q X Y U W τ hnonneg T ρ)) hi.aestronglyMeasurable]
  exact integral_prod _ hi

omit [DiscreteTopology E] in
/-- The paper's current-activity integral has its ordinary real meaning
whenever its nonnegative extended expectation is finite. -/
theorem currentActivity_integrable_and_toReal (T : ℝ) (ρ : E → E → ℝ)
    (hfin : (∫⁻ ω, ∫⁻ t in Ioc 0 T, if ENNReal.ofReal t ≤ τ ω then
        ENNReal.ofReal (∑ j, currentActivity jump q X Y U W ρ j ω t) else 0
        ∂positiveVolume ∂P) < ⊤) :
    Integrable (stoppedActivity jump q X Y U W τ T ρ) (P.prod positiveVolume) ∧
    (∀ᵐ ω ∂P, Integrable (fun t => stoppedActivity jump q X Y U W τ T ρ (ω,t)) positiveVolume) ∧
    Integrable (fun ω => ∫ t in Ioc 0 T, if ENNReal.ofReal t ≤ τ ω then
      ∑ j, currentActivity jump q X Y U W ρ j ω t else 0 ∂positiveVolume) P ∧
    (∫⁻ ω, ∫⁻ t in Ioc 0 T, if ENNReal.ofReal t ≤ τ ω then
      ENNReal.ofReal (∑ j, currentActivity jump q X Y U W ρ j ω t) else 0
      ∂positiveVolume ∂P).toReal =
      ∫ ω, ∫ t in Ioc 0 T, if ENNReal.ofReal t ≤ τ ω then
        ∑ j, currentActivity jump q X Y U W ρ j ω t else 0 ∂positiveVolume ∂P := by
  have hf : (∫⁻ ω, ∫⁻ t, ENNReal.ofReal (stoppedActivity jump q X Y U W τ T ρ (ω,t))
      ∂positiveVolume ∂P) < ⊤ := by
    simpa only [lintegral_stoppedActivity] using hfin
  have hi := integrable_stoppedActivity_of_lintegral_lt_top F jump q X Y U W e hq hX hY hU hW
    P τ hτ hnonneg hcX hcY hcU hcW T ρ hf
  refine ⟨hi,hi.prod_right_ae,?_,?_⟩
  · simpa only [integral_stoppedActivity] using hi.integral_prod_left
  · simpa only [lintegral_stoppedActivity,integral_stoppedActivity] using
      toReal_lintegral_stoppedActivity F jump q X Y U W e hq hX hY hU hW
        P τ hτ hnonneg hcX hcY hcU hcW T ρ hf

end CarryingCapacity.RandomEnvironmentActivityIntegral
