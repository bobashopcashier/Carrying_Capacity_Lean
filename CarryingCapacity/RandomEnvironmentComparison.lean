import CarryingCapacity.RandomEnvironmentPathwise
import CarryingCapacity.RateTableSumCompensation
import CarryingCapacity.RightContinuousProcessMeasurability
import CarryingCapacity.StoppedComparisonLocalization

/-!
# Candidate thinning equations and predictable stopped comparison

Candidate paths are arbitrary càdlàg processes. Their own actual left-limit
equations are compared on a decoded noise space with the genuine canonical
PRM law. All coefficients may depend on that same sample. The predictable
scalar-table field is identified with the exact left-state/environment field.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal BigOperators NNReal

namespace CarryingCapacity.RandomEnvironmentComparison
open RandomEnvironmentCompensation PredictableStepApproximation
  SynchronousRunningSupremum SynchronousStoppedRunningSupremum CommonFrozenExit

variable {Ω E V J I : Type*} [mΩ : MeasurableSpace Ω]
  [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
  [Countable E] [MeasurableSingletonClass E] [DiscreteTopology E] [DecidableEq E]
  [Fintype J] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  (jump : J → E → E) (q : J → E → V → ℝ)
  (X Y preX preY : ℝ → Ω → E) (U W preU preW : ℝ → Ω → V) (e : E)

omit mΩ [MeasurableSpace E] [BorelSpace E] [MeasurableSingletonClass E]
  [DiscreteTopology E] [DecidableEq E] [MeasurableSpace V] [BorelSpace V] in
/-- The predictable version is the original equation's exact integrand at
all positive times, simultaneously, on genuine left-limit paths. -/
theorem stoppedField_eq_explicit (hq : ∀ j x, Continuous (q j x))
    (hnonneg : ∀ j x u, 0 ≤ q j x u) (τ : Ω → ℝ≥0∞)
    (ρ : E → E → ℝ) (j : J) (T : ℝ) (ω : Ω)
    (hx : ∀ t : ℝ, 0 < t → Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 (preX t ω)))
    (hy : ∀ t : ℝ, 0 < t → Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 (preY t ω)))
    (hu : ∀ t : ℝ, 0 < t → Tendsto (fun s => U s ω) (𝓝[<] t) (𝓝 (preU t ω)))
    (hw : ∀ t : ℝ, 0 < t → Tendsto (fun s => W s ω) (𝓝[<] t) (𝓝 (preW t ω)))
    (z : ℝ × ℝ) :
    ENNReal.ofReal (RateTableCompensation.stoppedField jump q X Y U W e τ ρ j T (ω,z)) =
      UniversalStoppedComparison.stoppedField jump
        (fun j s x => q j x (preU s ω)) (fun j s x => q j x (preW s ω))
        (fun s => preX s ω) (fun s => preY s ω) ρ (τ ω) T j z := by
  by_cases ht : z.1 ∈ Ioc 0 T
  · have hX := pastLimit_eq_of_tendsto X e ω z.1 ht.1 _ (hx z.1 ht.1)
    have hY := pastLimit_eq_of_tendsto Y e ω z.1 ht.1 _ (hy z.1 ht.1)
    have hU := pastLimit_eq_of_tendsto
      (fun s ω => RateTableCompensation.table q (U s ω)) (fun _ => 0) ω z.1 ht.1
      (RateTableCompensation.table q (preU z.1 ω))
      ((RateTableCompensation.continuous_table q hq).continuousAt.tendsto.comp (hu z.1 ht.1))
    have hW := pastLimit_eq_of_tendsto
      (fun s ω => RateTableCompensation.table q (W s ω)) (fun _ => 0) ω z.1 ht.1
      (RateTableCompensation.table q (preW z.1 ω))
      ((RateTableCompensation.continuous_table q hq).continuousAt.tendsto.comp (hw z.1 ht.1))
    by_cases hs : ENNReal.ofReal z.1 ≤ τ ω
    · simp only [RateTableCompensation.stoppedField, RandomEnvironmentCompensation.stoppedField,
        PredictableStoppingMask.mask_apply, field, ht, ht.1, hs, and_self, if_true,
        hX,hY,hU,hW,RateTableCompensation.evaluation_table q hnonneg,
        UniversalStoppedComparison.stoppedField]
    · simp [RateTableCompensation.stoppedField, RandomEnvironmentCompensation.stoppedField,
        PredictableStoppingMask.mask_apply, field, ht, ht.1, hs,
        UniversalStoppedComparison.stoppedField]
  · simp [RateTableCompensation.stoppedField, RandomEnvironmentCompensation.stoppedField,
      PredictableStoppingMask.mask_apply, field, ht, UniversalStoppedComparison.stoppedField]

variable (P : Measure Ω) [IsProbabilityMeasure P]
  (noise : Ω → MarkedNoise.Sample J) (hnoise : MeasurePreserving noise P (MarkedNoise.law J))
  (K : J → Kernel Ω (ℝ × ℝ))
  (hK : ∀ᵐ ω ∂P, ∀ j, K j ω = MarkedNoise.countingMeasure j (noise ω))
  (test : I → E → ℝ) (hsep : ∀ x y : E, (∀ i, test i x = test i y) → x = y)
  (hq : ∀ j x, Continuous (q j x)) (hnonneg : ∀ j x u, 0 ≤ q j x u)
  (τ : Ω → ℝ≥0∞) (T : ℝ≥0) (ρ : E → E → ℝ) (hρ : ∀ x y, 0 ≤ ρ x y)
  (hcX : ∀ᵐ ω ∂P, CadlagNonnegative (fun t => X t ω))
  (hcY : ∀ᵐ ω ∂P, CadlagNonnegative (fun t => Y t ω))
  (hcU : ∀ᵐ ω ∂P, CadlagNonnegative (fun t => U t ω))
  (hcW : ∀ᵐ ω ∂P, CadlagNonnegative (fun t => W t ω))
  (hpreX : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
    Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 (preX t ω)))
  (hpreY : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
    Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 (preY t ω)))
  (hpreU : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
    Tendsto (fun s => U s ω) (𝓝[<] t) (𝓝 (preU t ω)))
  (hpreW : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
    Tendsto (fun s => W s ω) (𝓝[<] t) (𝓝 (preW t ω)))
  (heqX : ∀ᵐ ω ∂P, ∀ i t, t ∈ Icc 0 (cutHorizon (τ ω) T : ℝ) →
    test i (X t ω) - test i (X 0 ω) = ∑ j : J, ∫ z,
      TimeDependentEquationUniqueness.increment jump (fun j s x => q j x (preU s ω))
        (fun s => preX s ω) (test i) j t z ∂K j ω)
  (heqY : ∀ᵐ ω ∂P, ∀ i t, t ∈ Icc 0 (cutHorizon (τ ω) T : ℝ) →
    test i (Y t ω) - test i (Y 0 ω) = ∑ j : J, ∫ z,
      TimeDependentEquationUniqueness.increment jump (fun j s x => q j x (preW s ω))
        (fun s => preY s ω) (test i) j t z ∂K j ω)

include hnoise hK hsep hq hnonneg hρ hcX hcY hcU hcW hpreX hpreY hpreU hpreW heqX heqY in
omit [IsProbabilityMeasure P] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSingletonClass E] [MeasurableSpace V] [BorelSpace V] in
/-- No finite-state, rate-cap, or paired-equation premise remains. -/
theorem ae_stopped_sup_le_predictable : ∀ᵐ ω ∂P,
    intervalSup (stopped (τ ω) (fun t => ENNReal.ofReal (ρ (X t ω) (Y t ω)))) T ≤
      ENNReal.ofReal (ρ (X 0 ω) (Y 0 ω)) + ∑ j : J, ∫⁻ z,
        ENNReal.ofReal (RateTableCompensation.stoppedField jump q X Y U W e τ ρ j T (ω,z)) ∂K j ω := by
  have hp := hnoise.quasiMeasurePreserving.ae
    (RandomEnvironmentPathwise.ae_stopped_sup_le_of_cadlag (J := J) (M := V) test hsep)
  filter_upwards [hp,hK,hcX,hcY,hcU,hcW,hpreX,hpreY,hpreU,hpreW,heqX,heqY]
    with ω hp hk hx hy hu hw hpx hpy hpu hpw heqx heqy
  have heqx' : ∀ i t, t ∈ Icc 0 (cutHorizon (τ ω) T : ℝ) →
      test i (X t ω) - test i (X 0 ω) = ∑ j : J, ∫ z,
      TimeDependentEquationUniqueness.increment jump (fun j s x => q j x (preU s ω))
        (fun s => preX s ω) (test i) j t z ∂MarkedNoise.countingMeasure j (noise ω) := by
    intro i t ht
    simpa only [hk] using heqx i t ht
  have heqy' : ∀ i t, t ∈ Icc 0 (cutHorizon (τ ω) T : ℝ) →
      test i (Y t ω) - test i (Y 0 ω) = ∑ j : J, ∫ z,
      TimeDependentEquationUniqueness.increment jump (fun j s x => q j x (preW s ω))
        (fun s => preY s ω) (test i) j t z ∂MarkedNoise.countingMeasure j (noise ω) := by
    intro i t ht
    simpa only [hk] using heqy i t ht
  have h := hp jump q hq (fun t => X t ω) (fun t => Y t ω)
    (fun t => preX t ω) (fun t => preY t ω) (fun t => U t ω) (fun t => W t ω)
    (fun t => preU t ω) (fun t => preW t ω) (τ ω) T ρ hρ hx hy hu hw
    hpx hpy hpu hpw heqx' heqy'
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [hk j]
  apply lintegral_congr
  exact stoppedField_eq_explicit jump q X Y preX preY U W preU preW e hq hnonneg
    τ ρ j T ω hpx hpy hpu hpw

variable (F : Filtration ℝ mΩ) [∀ j, IsSFiniteKernel (K j)]
  (hmean : ∀ j, IndependentIncrementCompensation.HasIntensity P (K j))
  (hind : ∀ j, IndependentIncrementCompensation.FutureCountsIndependent F P (K j))
  (hX : ∀ s, 0 ≤ s → Measurable[F s] (X s))
  (hY : ∀ s, 0 ≤ s → Measurable[F s] (Y s))
  (hU : ∀ s, 0 ≤ s → Measurable[F s] (U s))
  (hW : ∀ s, 0 ≤ s → Measurable[F s] (W s))
  (hτ : ∀ s : ℝ, 0 ≤ s → MeasurableSet[F s] {ω | τ ω ≤ ENNReal.ofReal s})

include e hX hY hcX hcY hτ in
omit noise hnoise K hK test hsep hq hnonneg hρ hmean hind hU hW hcU hcW
  hpreX hpreY hpreU hpreW heqX heqY [∀ j, IsSFiniteKernel (K j)]
  [IsProbabilityMeasure P] [DecidableEq E] in
/-- The true uncountable stopped supremum is AE measurable, derived from
adapted evaluations and càdlàg paths rather than imposed on the candidate. -/
theorem aemeasurable_stopped_sup :
    AEMeasurable (fun ω => intervalSup
      (stopped (τ ω) (fun t => ENNReal.ofReal (ρ (X t ω) (Y t ω)))) T) P := by
  have hp : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      ContinuousWithinAt (fun s => (X s ω,Y s ω)) (Ici t) t := by
    filter_upwards [hcX,hcY] with ω hx hy
    exact fun t ht => (hx.1 t ht).prodMk (hy.1 t ht)
  have hm := RightContinuousProcessMeasurability.aemeasurable_intervalSup_stopped
    (fun t ω => (X t ω,Y t ω))
    (fun t ht => ((hX t ht).mono (F.le t) le_rfl).prodMk ((hY t ht).mono (F.le t) le_rfl))
    (e,e) P hp τ (RightContinuousProcessMeasurability.measurable_of_stopping_sublevels F τ hτ).aemeasurable
    (fun z : E × E => ENNReal.ofReal (ρ z.1 z.2)) T T.coe_nonneg
  convert hm using 1
  funext ω
  unfold intervalSup
  apply iSup_congr
  intro t
  simp only [stopped]
  split_ifs <;> rfl

include hnoise hK hsep hq hnonneg hρ hcX hcY hcU hcW hpreX hpreY hpreU hpreW heqX heqY
  e hmean hind hX hY hU hW hτ in
/-- The full expected running-supremum inequality, with arbitrary adapted
càdlàg environments and any common stopping time. Its right side is the exact
three-region synchronous current activity, and may initially be infinite. -/
theorem expected_stopped_sup_le_activity :
    (∫⁻ ω, intervalSup (stopped (τ ω)
      (fun t => ENNReal.ofReal (ρ (X t ω) (Y t ω)))) T ∂P) ≤
      (∫⁻ ω, ENNReal.ofReal (ρ (X 0 ω) (Y 0 ω)) ∂P) +
        ∫⁻ ω, ∫⁻ t in Ioc 0 T, if ENNReal.ofReal t ≤ τ ω then
          ENNReal.ofReal (∑ j : J, currentActivity jump q X Y U W ρ j ω t) else 0
          ∂MarkedIntensity.positiveVolume ∂P := by
  have hp := ae_stopped_sup_le_predictable jump q X Y preX preY U W preU preW e
    P noise hnoise K hK test hsep hq hnonneg τ T ρ hρ hcX hcY hcU hcW
    hpreX hpreY hpreU hpreW heqX heqY
  have hm : Measurable (fun ω => ENNReal.ofReal (ρ (X 0 ω) (Y 0 ω))) :=
    ((measurable_of_countable (fun z : E × E => ρ z.1 z.2)).comp
      (((hX 0 le_rfl).mono (F.le 0) le_rfl).prodMk
        ((hY 0 le_rfl).mono (F.le 0) le_rfl))).ennreal_ofReal
  refine (lintegral_mono_ae hp).trans_eq ?_
  rw [lintegral_add_left hm]
  congr 1
  exact RateTableSumCompensation.expected_sum_stoppedField_eq_currentActivity
    F jump q X Y U W e hq hX hY hU hW P K hmean hind τ hτ hnonneg hcX hcY hcU hcW ρ T

end CarryingCapacity.RandomEnvironmentComparison
