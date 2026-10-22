import CarryingCapacity.PrescribedRandomEnvironmentCompensation
import CarryingCapacity.RandomEnvironmentComparison
import CarryingCapacity.RandomEnvironmentActivityIntegral
import CarryingCapacity.FiniteStateActivityIntegrability

/-!
# Synchronous comparison on the supplied Poisson space

This is the manuscript's positive-increment estimate for arbitrary adapted
càdlàg environments. The inputs are the primitive supplied Poisson laws,
independence of the initial record, and each candidate's own coordinate
thinning equations with genuine left limits. No deterministic-environment,
finite-state, rate-cap, paired-equation, or stochastic-estimate premise is
introduced. The ordinary real conclusion follows when the initial distance
and nonnegative activity on the right have finite expectations.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal NNReal BigOperators

namespace CarryingCapacity.PrescribedRandomEnvironmentComparison
open PrescribedPoissonFiltration PrescribedPoissonRealization RandomEnvironmentCompensation
  SynchronousRunningSupremum SynchronousStoppedRunningSupremum CommonFrozenExit

local instance {D : ℕ} (κ : MomentScale) : MeasurableSpace (MomentLaw κ D) := borel _
local instance {D : ℕ} (κ : MomentScale) : BorelSpace (MomentLaw κ D) := ⟨rfl⟩

variable {Ω A : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace A]
  {D : ℕ} (κ : MomentScale) (q : Rates D (MomentLaw κ D))
  (hCoupling : MomentCouplingBound κ q)
  (M : Jump D → Ω → Measure (ℝ × ℝ)) (ξ : Ω → A) (P : Measure Ω)
  [IsProbabilityMeasure P]
  (hM : ∀ j, Measurable (M j))
  (hPoisson : PoissonObservationLaw.HasDisjointLaws P (Jump D) M)
  (hξ : Measurable ξ) (hIndependent : IndepFun ξ (fun ω j => M j ω) P)
  (X Y preX preY : ℝ → Ω → State D)
  (U W preU preW : ℝ → Ω → MomentLaw κ D)
  (τ : Ω → ℝ≥0∞) (T : ℝ≥0)
  (hX : ∀ s, 0 ≤ s → Measurable[(UsualFiltration.filtration P
    (rawFiltration (Jump D) M ξ hM hξ)) s] (X s))
  (hY : ∀ s, 0 ≤ s → Measurable[(UsualFiltration.filtration P
    (rawFiltration (Jump D) M ξ hM hξ)) s] (Y s))
  (hU : ∀ s, 0 ≤ s → Measurable[(UsualFiltration.filtration P
    (rawFiltration (Jump D) M ξ hM hξ)) s] (U s))
  (hW : ∀ s, 0 ≤ s → Measurable[(UsualFiltration.filtration P
    (rawFiltration (Jump D) M ξ hM hξ)) s] (W s))
  (hτ : ∀ s : ℝ, 0 ≤ s → MeasurableSet[(UsualFiltration.filtration P
    (rawFiltration (Jump D) M ξ hM hξ)) s] {ω | τ ω ≤ ENNReal.ofReal s})
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
  (heqX : ∀ᵐ ω ∂P, ∀ i : Fin D, ∀ t, t ∈ Icc 0 (cutHorizon (τ ω) T : ℝ) →
    (X t ω i : ℝ) - (X 0 ω i : ℝ) = ∑ j : Jump D, ∫ z,
      TimeDependentEquationUniqueness.increment Jump.advance
        (fun j s x => q.rate j x (preU s ω)) (fun s => preX s ω)
        (fun x : State D => (x i : ℝ)) j t z ∂M j ω)
  (heqY : ∀ᵐ ω ∂P, ∀ i : Fin D, ∀ t, t ∈ Icc 0 (cutHorizon (τ ω) T : ℝ) →
    (Y t ω i : ℝ) - (Y 0 ω i : ℝ) = ∑ j : Jump D, ∫ z,
      TimeDependentEquationUniqueness.increment Jump.advance
        (fun j s x => q.rate j x (preW s ω)) (fun s => preY s ω)
        (fun x : State D => (x i : ℝ)) j t z ∂M j ω)

/-- The actual uncountable stopped running distance, including the exit jump. -/
def stoppedDistance (ω : Ω) : ℝ≥0∞ :=
  intervalSup (stopped (τ ω) (fun t => ENNReal.ofReal (adaptedDistance κ (X t ω) (Y t ω)))) T

include hCoupling hPoisson hIndependent hX hY hU hW hτ hcX hcY hcU hcW
  hpreX hpreY hpreU hpreW heqX heqY

/-- The exact manuscript activity controls the actual stopped supremum on
any space carrying the prescribed independent PRMs and initial record. -/
theorem expected_stoppedDistance_le_couplingActivity :
    (∫⁻ ω, stoppedDistance κ X Y τ T ω ∂UsualFiltration.completedLaw P) ≤
      (∫⁻ ω, ENNReal.ofReal (adaptedDistance κ (X 0 ω) (Y 0 ω)) ∂UsualFiltration.completedLaw P) +
      ∫⁻ ω, ∫⁻ s in Ioc 0 (T : ℝ), if ENNReal.ofReal s ≤ τ ω then
        ENNReal.ofReal (couplingActivity κ q (X s ω) (Y s ω) (U s ω) (W s ω)) else 0
        ∂MarkedIntensity.positiveVolume ∂UsualFiltration.completedLaw P := by
  let F := UsualFiltration.filtration P (rawFiltration (Jump D) M ξ hM hξ)
  let Q := UsualFiltration.completedLaw P
  let K := PrescribedCountingKernel.countingKernel (Jump D) M P hM
  have hm := measurable_noise (Jump D) M hM
  have hmQ := hm.mono (show mΩ ≤ UsualFiltration.completedSpace P from
    EventuallyMeasurableSpace.measurable_le) le_rfl
  have hmap := noise_map (Jump D) M P hM hPoisson
  have hnoise : @MeasurePreserving Ω (MarkedNoise.Sample (Jump D))
      (UsualFiltration.completedSpace P) inferInstance (noise (Jump D) M) Q (MarkedNoise.law (Jump D)) := by
    letI : MeasurableSpace Ω := UsualFiltration.completedSpace P
    refine ⟨hmQ, ?_⟩
    rw [← hmap]
    apply Measure.ext
    intro S hS
    rw [Measure.map_apply hmQ hS, Measure.map_apply hm hS]
    rfl
  have hk : ∀ᵐ ω ∂Q, ∀ j, K j ω = MarkedNoise.countingMeasure j (noise (Jump D) M ω) :=
    Eventually.of_forall (fun ω j => PrescribedCountingKernel.countingKernel_apply (Jump D) M P hM j ω)
  have he := PrescribedCountingKernel.ae_countingKernel_eq (Jump D) M P hM hPoisson
  have heqx : ∀ᵐ ω ∂Q, ∀ i : Fin D, ∀ t, t ∈ Icc 0 (cutHorizon (τ ω) T : ℝ) →
      (X t ω i : ℝ) - (X 0 ω i : ℝ) = ∑ j : Jump D, ∫ z,
        TimeDependentEquationUniqueness.increment Jump.advance
          (fun j s x => q.rate j x (preU s ω)) (fun s => preX s ω)
          (fun x : State D => (x i : ℝ)) j t z ∂K j ω := by
    filter_upwards [heqX,he] with ω hω hkω
    intro i t ht
    simpa only [K,hkω] using hω i t ht
  have heqy : ∀ᵐ ω ∂Q, ∀ i : Fin D, ∀ t, t ∈ Icc 0 (cutHorizon (τ ω) T : ℝ) →
      (Y t ω i : ℝ) - (Y 0 ω i : ℝ) = ∑ j : Jump D, ∫ z,
        TimeDependentEquationUniqueness.increment Jump.advance
          (fun j s x => q.rate j x (preW s ω)) (fun s => preY s ω)
          (fun x : State D => (x i : ℝ)) j t z ∂K j ω := by
    filter_upwards [heqY,he] with ω hω hkω
    intro i t ht
    simpa only [K,hkω] using hω i t ht
  have hsep : ∀ x y : State D, (∀ i : Fin D, (x i : ℝ) = (y i : ℝ)) → x = y := by
    intro x y h
    funext i
    exact_mod_cast h i
  exact RandomEnvironmentComparison.expected_stopped_sup_le_activity
    (mΩ := UsualFiltration.completedSpace P)
    Jump.advance q.rate X Y preX preY U W preU preW (fun _ => 0)
    Q (noise (Jump D) M) hnoise K hk (fun i x => (x i : ℝ)) hsep
    (DeterministicEnvironmentRates.continuous_rate κ q hCoupling) q.nonnegative τ T
    (adaptedDistance κ) (adaptedDistance_nonneg κ) hcX hcY hcU hcW
    hpreX hpreY hpreU hpreW heqx heqy F
    (PrescribedCountingKernel.hasIntensity (Jump D) M P hM hPoisson)
    (PrescribedCountingKernel.futureCountsIndependent (Jump D) M P hM hPoisson ξ hξ hIndependent)
    hX hY hU hW hτ

omit hCoupling hPoisson hIndependent hU hW hcU hcW hpreX hpreY hpreU hpreW heqX heqY
  [IsProbabilityMeasure P] in
/-- Measurability of the actual all-real supremum requires no separately
assumed path-map or supremum measurability. -/
theorem aemeasurable_stoppedDistance :
    AEMeasurable (stoppedDistance κ X Y τ T) (UsualFiltration.completedLaw P) := by
  exact RandomEnvironmentComparison.aemeasurable_stopped_sup
    (mΩ := UsualFiltration.completedSpace P)
    X Y (fun _ => 0) (UsualFiltration.completedLaw P) τ T (adaptedDistance κ) hcX hcY
    (UsualFiltration.filtration P (rawFiltration (Jump D) M ξ hM hξ)) hX hY hτ

/-- Under a finite right-hand side, the actual stopped running distance is
almost surely finite and genuinely integrable. The displayed real inequality
uses ordinary Lebesgue time integration and includes the stopping-time jump. -/
theorem integrable_stoppedDistance_and_integral_le
    (hInitial : Integrable (fun ω => adaptedDistance κ (X 0 ω) (Y 0 ω))
      (UsualFiltration.completedLaw P))
    (hActivity : (∫⁻ ω, ∫⁻ s in Ioc 0 (T : ℝ), if ENNReal.ofReal s ≤ τ ω then
        ENNReal.ofReal (couplingActivity κ q (X s ω) (Y s ω) (U s ω) (W s ω)) else 0
        ∂MarkedIntensity.positiveVolume ∂UsualFiltration.completedLaw P) < ⊤) :
    (∀ᵐ ω ∂UsualFiltration.completedLaw P, stoppedDistance κ X Y τ T ω < ⊤) ∧
    Integrable (fun ω => (stoppedDistance κ X Y τ T ω).toReal) (UsualFiltration.completedLaw P) ∧
    (∫ ω, (stoppedDistance κ X Y τ T ω).toReal ∂UsualFiltration.completedLaw P) ≤
      (∫ ω, adaptedDistance κ (X 0 ω) (Y 0 ω) ∂UsualFiltration.completedLaw P) +
      ∫ ω, ∫ s in Ioc 0 (T : ℝ), if ENNReal.ofReal s ≤ τ ω then
        couplingActivity κ q (X s ω) (Y s ω) (U s ω) (W s ω) else 0
        ∂volume ∂UsualFiltration.completedLaw P := by
  have hb := expected_stoppedDistance_le_couplingActivity κ q hCoupling M ξ P hM hPoisson
    hξ hIndependent X Y preX preY U W preU preW τ T hX hY hU hW hτ
    hcX hcY hcU hcW hpreX hpreY hpreU hpreW heqX heqY
  have hm := aemeasurable_stoppedDistance κ M ξ P hM hξ X Y τ T hX hY hτ hcX hcY
  have hInit := ofReal_integral_eq_lintegral_ofReal hInitial
    (Eventually.of_forall (fun ω => adaptedDistance_nonneg κ (X 0 ω) (Y 0 ω)))
  have hInitFinite : (∫⁻ ω, ENNReal.ofReal (adaptedDistance κ (X 0 ω) (Y 0 ω))
      ∂UsualFiltration.completedLaw P) ≠ ⊤ := by
    rw [← hInit]
    exact ENNReal.ofReal_ne_top
  have hfinite := ENNReal.add_ne_top.mpr ⟨hInitFinite,hActivity.ne⟩
  have hbound := @StoppedComparisonLocalization.integrable_and_integral_le Ω
    (UsualFiltration.completedSpace P)
    (UsualFiltration.completedLaw P) (stoppedDistance κ X Y τ T) hm _ hfinite hb
  have hreal := RandomEnvironmentActivityIntegral.currentActivity_integrable_and_toReal
    (mΩ := UsualFiltration.completedSpace P)
    (UsualFiltration.filtration P (rawFiltration (Jump D) M ξ hM hξ))
    Jump.advance q.rate X Y U W (fun _ => 0)
    (DeterministicEnvironmentRates.continuous_rate κ q hCoupling) hX hY hU hW
    (UsualFiltration.completedLaw P) τ hτ q.nonnegative hcX hcY hcU hcW T
    (adaptedDistance κ) hActivity
  refine ⟨@ae_lt_top' Ω (UsualFiltration.completedSpace P) _ _ hm (ne_top_of_le_ne_top hfinite hb), hbound.1, ?_⟩
  rw [ENNReal.toReal_add hInitFinite hActivity.ne, ← hInit,
    ENNReal.toReal_ofReal (integral_nonneg (μ := UsualFiltration.completedLaw P) (fun ω => adaptedDistance_nonneg κ (X 0 ω) (Y 0 ω)))]
      at hbound
  have ha : (∫⁻ ω, ∫⁻ s in Ioc 0 (T : ℝ), if ENNReal.ofReal s ≤ τ ω then
        ENNReal.ofReal (couplingActivity κ q (X s ω) (Y s ω) (U s ω) (W s ω)) else 0
        ∂MarkedIntensity.positiveVolume ∂UsualFiltration.completedLaw P).toReal =
      ∫ ω, ∫ s in Ioc 0 (T : ℝ), if ENNReal.ofReal s ≤ τ ω then
        couplingActivity κ q (X s ω) (Y s ω) (U s ω) (W s ω) else 0
        ∂volume ∂UsualFiltration.completedLaw P := by
    have h := hreal.2.2.2
    change (∫⁻ ω, ∫⁻ s in Ioc 0 (T : ℝ), if ENNReal.ofReal s ≤ τ ω then
        ENNReal.ofReal (couplingActivity κ q (X s ω) (Y s ω) (U s ω) (W s ω)) else 0
        ∂MarkedIntensity.positiveVolume ∂UsualFiltration.completedLaw P).toReal =
      ∫ ω, ∫ s in Ioc 0 (T : ℝ), if ENNReal.ofReal s ≤ τ ω then
        couplingActivity κ q (X s ω) (Y s ω) (U s ω) (W s ω) else 0
        ∂MarkedIntensity.positiveVolume ∂UsualFiltration.completedLaw P at h
    simpa only [TimeDependentDynkin.positiveVolume_restrict_Ioc_zero] using h
  simpa only [ha] using hbound.2

/-- The finite-state clause of Lemma 4.1: finite stopped ordinary-rate
expectation suffices. Finiteness of the weighted activity and of the initial
distance are conclusions of the finite-state bounds, not added premises. -/
theorem finite_state_comparison (G : Finset (State D))
    (hinit : ∀ᵐ ω ∂P, X 0 ω ∈ G ∧ Y 0 ω ∈ G)
    (hstates : ∀ᵐ ω ∂P, ∀ s ∈ Ioc 0 (T : ℝ), ENNReal.ofReal s ≤ τ ω →
      X s ω ∈ G ∧ Y s ω ∈ G)
    (hrates : (∫⁻ ω, ∫⁻ s in Ioc 0 (T : ℝ), if ENNReal.ofReal s ≤ τ ω then
      ENNReal.ofReal ((∑ j, q.rate j (X s ω) (U s ω)) + ∑ j, q.rate j (Y s ω) (W s ω))
      else 0 ∂MarkedIntensity.positiveVolume ∂UsualFiltration.completedLaw P) < ⊤) :
    (∀ᵐ ω ∂UsualFiltration.completedLaw P, stoppedDistance κ X Y τ T ω < ⊤) ∧
    Integrable (fun ω => (stoppedDistance κ X Y τ T ω).toReal) (UsualFiltration.completedLaw P) ∧
    (∫ ω, (stoppedDistance κ X Y τ T ω).toReal ∂UsualFiltration.completedLaw P) ≤
      (∫ ω, adaptedDistance κ (X 0 ω) (Y 0 ω) ∂UsualFiltration.completedLaw P) +
      ∫ ω, ∫ s in Ioc 0 (T : ℝ), if ENNReal.ofReal s ≤ τ ω then
        couplingActivity κ q (X s ω) (Y s ω) (U s ω) (W s ω) else 0
        ∂volume ∂UsualFiltration.completedLaw P := by
  have hi := @FiniteStateActivityIntegrability.integrable_initialCost
    (State D) (Jump D) _ _ G Jump.advance (adaptedDistance κ) Ω
    (UsualFiltration.completedSpace P) (UsualFiltration.completedLaw P) _ _ _ _
    (adaptedDistance_nonneg κ) (X 0) (Y 0)
    ((hX 0 le_rfl).mono ((UsualFiltration.filtration P (rawFiltration (Jump D) M ξ hM hξ)).le 0) le_rfl)
    ((hY 0 le_rfl).mono ((UsualFiltration.filtration P (rawFiltration (Jump D) M ξ hM hξ)).le 0) le_rfl)
    hinit
  have ha := @FiniteStateActivityIntegrability.expected_activity_lt_top_of_rates
    (State D) (Jump D) _ _ G Jump.advance (adaptedDistance κ) Ω (MomentLaw κ D)
    q.rate X Y U W (UsualFiltration.completedSpace P) (UsualFiltration.completedLaw P)
    (adaptedDistance_nonneg κ) q.nonnegative τ T MarkedIntensity.positiveVolume hstates hrates
  exact integrable_stoppedDistance_and_integral_le κ q hCoupling M ξ P hM hPoisson
    hξ hIndependent X Y preX preY U W preU preW τ T hX hY hU hW hτ
    hcX hcY hcU hcW hpreX hpreY hpreU hpreW heqX heqY hi ha

end CarryingCapacity.PrescribedRandomEnvironmentComparison
