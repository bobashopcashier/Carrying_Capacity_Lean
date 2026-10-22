import CarryingCapacity.RateTableCompensation

/-!
# Finite-label compensation in arbitrary adapted random environments

The finite-label identity is obtained from genuine kernel compensation.
Predictable scalar tables justify all finite-sum exchanges, and their values
are replaced by the original current rates only on the proved time-null sets.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal BigOperators

namespace CarryingCapacity.RateTableSumCompensation
open RandomEnvironmentCompensation PredictableStepApproximation PredictableSets
  MarkedIntensity IndependentIncrementCompensation RateTableCompensation

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

variable {Ω E V J : Type*} [mΩ : MeasurableSpace Ω]
  [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
  [Countable E] [MeasurableSingletonClass E] [DiscreteTopology E]
  [Fintype J] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  (F : Filtration ℝ mΩ) (jump : J → E → E) (q : J → E → V → ℝ)
  (X Y : ℝ → Ω → E) (U W : ℝ → Ω → V) (e : E)
  (hq : ∀ j x, Continuous (q j x))
  (hX : ∀ s, 0 ≤ s → Measurable[F s] (X s))
  (hY : ∀ s, 0 ≤ s → Measurable[F s] (Y s))
  (hU : ∀ s, 0 ≤ s → Measurable[F s] (U s))
  (hW : ∀ s, 0 ≤ s → Measurable[F s] (W s))

include hq hX hY hU hW

omit [DiscreteTopology E] in
/-- The scalar-table pre-activity is genuinely predictable. -/
theorem measurable_preActivity (ρ : E → E → ℝ) (j : J) :
    Measurable[predictable F] (fun p : Ω × (ℝ × ℝ) =>
      preActivity jump evaluation X Y (fun t ω => table q (U t ω))
        (fun t ω => table q (W t ω)) e (fun _ => 0) ρ j p.1 p.2.1) := by
  letI : MeasurableSpace (Ω × (ℝ × ℝ)) := predictable F
  have hx := measurable_pastLimit F X hX e
  have hy := measurable_pastLimit F Y hY e
  have hu := measurable_pastLimit F (fun t ω => table q (U t ω))
    (measurable_table_process F q U hq hU) (fun _ => 0)
  have hw := measurable_pastLimit F (fun t ω => table q (W t ω))
    (measurable_table_process F q W hq hW) (fun _ => 0)
  exact SynchronousCompensation.measurable_heightActivity_comp jump ρ j _ _ _ _
    (measurable_rate_comp evaluation continuous_evaluation j _ _ hx hu)
    (measurable_rate_comp evaluation continuous_evaluation j _ _ hy hw) hx hy

omit [DiscreteTopology E] in
/-- A time section of the stopped pre-activity is measurable without any
ambient measurability assumption on the stopping time beyond its past events. -/
theorem measurable_stoppedPreActivity (τ : Ω → ℝ≥0∞)
    (hτ : ∀ s : ℝ, 0 ≤ s → MeasurableSet[F s] {ω | τ ω ≤ ENNReal.ofReal s})
    (ρ : E → E → ℝ) (j : J) (T : ℝ) :
    Measurable (fun p : Ω × ℝ => if p.2 ∈ Ioc 0 T then
      if ENNReal.ofReal p.2 ≤ τ p.1 then ENNReal.ofReal
        (preActivity jump evaluation X Y (fun t ω => table q (U t ω))
          (fun t ω => table q (W t ω)) e (fun _ => 0) ρ j p.1 p.2) else 0 else 0) := by
  have hm := ((PredictableStoppingMask.measurable_mask F τ hτ _
    ((measurable_preActivity F jump q X Y U W e hq hX hY hU hW ρ j).ennreal_ofReal.indicator
      (measurableSet_predictable_rectangle F 0 T le_rfl univ MeasurableSet.univ
        univ MeasurableSet.univ))).mono (predictable_le F) le_rfl).comp
      (show Measurable (fun p : Ω × ℝ => (p.1,(p.2,(0:ℝ)))) from
        measurable_fst.prodMk (measurable_snd.prodMk measurable_const))
  convert hm using 1
  funext p
  by_cases ht : p.2 ∈ Ioc 0 T
  · simp [PredictableStoppingMask.mask_apply, rectangle, ht, ht.1]
  · simp [PredictableStoppingMask.mask_apply, rectangle, ht]

/-- The exact finite sum of stopped positive jump integrals equals the time
integral of the full current activity. Both sides may be infinite. -/
theorem expected_sum_stoppedField_eq_currentActivity
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : J → Kernel Ω (ℝ × ℝ)) [∀ j, IsSFiniteKernel (K j)]
    (hmean : ∀ j, HasIntensity P (K j)) (hind : ∀ j, FutureCountsIndependent F P (K j))
    (τ : Ω → ℝ≥0∞)
    (hτ : ∀ s : ℝ, 0 ≤ s → MeasurableSet[F s] {ω | τ ω ≤ ENNReal.ofReal s})
    (hnonneg : ∀ j x u, 0 ≤ q j x u)
    (hcX : ∀ᵐ ω ∂P, CadlagNonnegative (fun t => X t ω))
    (hcY : ∀ᵐ ω ∂P, CadlagNonnegative (fun t => Y t ω))
    (hcU : ∀ᵐ ω ∂P, CadlagNonnegative (fun t => U t ω))
    (hcW : ∀ᵐ ω ∂P, CadlagNonnegative (fun t => W t ω))
    (ρ : E → E → ℝ) (T : ℝ) :
    (∫⁻ ω, ∑ j, ∫⁻ z, ENNReal.ofReal
      (RateTableCompensation.stoppedField jump q X Y U W e τ ρ j T (ω,z)) ∂K j ω ∂P) =
      ∫⁻ ω, ∫⁻ t in Ioc 0 T, if ENNReal.ofReal t ≤ τ ω then
        ENNReal.ofReal (∑ j, currentActivity jump q X Y U W ρ j ω t) else 0
        ∂positiveVolume ∂P := by
  let f := fun j => ENNReal.ofReal ∘ RateTableCompensation.stoppedField jump q X Y U W e τ ρ j T
  have hf (j : J) : Measurable (f j) :=
    ((RateTableCompensation.measurable_stoppedField F jump q X Y U W e hq hX hY hU hW
      τ hτ ρ j T).mono (predictable_le F) le_rfl).ennreal_ofReal
  let H := fun j (ω : Ω) (t : ℝ) => if t ∈ Ioc 0 T then
      if ENNReal.ofReal t ≤ τ ω then ENNReal.ofReal
        (preActivity jump evaluation X Y (fun t ω => table q (U t ω))
          (fun t ω => table q (W t ω)) e (fun _ => 0) ρ j ω t) else 0 else 0
  have hH (j : J) : Measurable (Function.uncurry (H j)) :=
    measurable_stoppedPreActivity F jump q X Y U W e hq hX hY hU hW τ hτ ρ j T
  have hheight (j : J) (ω : Ω) :
      (∫⁻ z, f j (ω,z) ∂positiveVolume.prod positiveVolume) = ∫⁻ t, H j ω t ∂positiveVolume := by
    have h := intensity_integral F jump evaluation X Y (fun t ω => table q (U t ω))
      (fun t ω => table q (W t ω)) e (fun _ => 0) continuous_evaluation hX hY
      (measurable_table_process F q U hq hU) (measurable_table_process F q W hq hW)
      τ hτ evaluation_nonnegative ρ j T ω
    rw [← lintegral_indicator measurableSet_Ioc] at h
    simpa only [f, H, RateTableCompensation.stoppedField, Function.comp_apply,
      Set.indicator_apply] using h
  change (∫⁻ ω, ∑ j, ∫⁻ z, f j (ω,z) ∂K j ω ∂P) = _
  rw [lintegral_finset_sum Finset.univ (fun j _ => (hf j).lintegral_kernel_prod_right')]
  have hc (j : J) := compensation_nonnegative F P (K j) (hmean j) (hind j) (f j)
    ((RateTableCompensation.measurable_stoppedField F jump q X Y U W e hq hX hY hU hW
      τ hτ ρ j T).ennreal_ofReal)
  simp_rw [hc, hheight]
  have houter (j : J) : Measurable (fun ω => ∫⁻ t, H j ω t ∂positiveVolume) :=
    (hH j).lintegral_prod_right'
  rw [← lintegral_finset_sum Finset.univ (fun j _ => houter j)]
  apply lintegral_congr_ae
  filter_upwards [hcX, hcY, hcU, hcW] with ω hx hy hu hw
  have hinner (j : J) : Measurable (H j ω) :=
    (hH j).comp (show Measurable (fun t : ℝ => (ω,t)) from measurable_const.prodMk measurable_id)
  rw [← lintegral_finset_sum Finset.univ (fun j _ => hinner j)]
  rw [← lintegral_indicator measurableSet_Ioc]
  have he : ∀ᵐ t ∂positiveVolume, ∀ j,
      preActivity jump evaluation X Y (fun t ω => table q (U t ω))
        (fun t ω => table q (W t ω)) e (fun _ => 0) ρ j ω t =
      currentActivity jump q X Y U W ρ j ω t := by
    apply ae_all_iff.mpr
    intro j
    have h := ae_preActivity_eq_currentActivity jump evaluation X Y
      (fun t ω => table q (U t ω)) (fun t ω => table q (W t ω)) e (fun _ => 0)
      continuous_evaluation ω hx hy
      (cadlag_comp (table q) (continuous_table q hq) _ hu)
      (cadlag_comp (table q) (continuous_table q hq) _ hw) ρ j
    filter_upwards [h] with t ht
    simpa only [currentActivity, evaluation_table q hnonneg] using ht
  apply lintegral_congr_ae
  filter_upwards [he] with t ht
  by_cases hT : t ∈ Ioc 0 T
  · by_cases hstop : ENNReal.ofReal t ≤ τ ω
    · simp only [H, hT, if_true, hstop, ht, Set.indicator_of_mem hT]
      exact (ENNReal.ofReal_sum_of_nonneg (fun j _ =>
        SynchronousPositiveIncrement.heightActivity_nonnegative ρ jump j _ _ _ _
          (hnonneg j _ _) (hnonneg j _ _))).symm
    · simp [H, hT, hstop]
  · simp only [H, if_neg hT, Finset.sum_const_zero, Set.indicator_of_not_mem hT]

end CarryingCapacity.RateTableSumCompensation
