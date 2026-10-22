import CarryingCapacity.LyapunovTails
import CarryingCapacity.TransportMetric

/-!
# Transport continuity of genuine common-space marginals

Almost-sure convergence of random states, together with uniform genuine
superlinear Lyapunov moments, implies convergence of their moment-adapted
transport laws. The proof uses the actual joint pushforward coupling and
derives uniform integrability of its transport cost before applying Vitali.

For time-indexed paths, almost-sure continuity at each fixed time gives a
continuous marginal curve. Its probability-one event may depend on that time;
sample paths need not be everywhere continuous.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace CarryingCapacity.LawCurveContinuity

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  {D : ℕ} {κ : MomentScale}

/-- The actual joint pushforward couples any two prescribed marginal laws
of random states on a common probability space. -/
def jointCoupling (X Y : Ω → State D) (hX : Measurable X) (hY : Measurable Y)
    (μ ν : MomentLaw κ D) (hμ : P.map X = μ.measure) (hν : P.map Y = ν.measure) :
    Coupling μ ν where
  measure := P.map (fun ω => (X ω, Y ω))
  first_marginal := by
    rw [Measure.map_map measurable_fst (hX.prodMk hY)]
    exact hμ
  second_marginal := by
    rw [Measure.map_map measurable_snd (hX.prodMk hY)]
    exact hν

omit [IsProbabilityMeasure P] in
/-- The common-space cost bounds the actual infimum over transport plans. -/
theorem wasserstein_le_integral_distance (X Y : Ω → State D)
    (hX : Measurable X) (hY : Measurable Y) (μ ν : MomentLaw κ D)
    (hμ : P.map X = μ.measure) (hν : P.map Y = ν.measure) :
    wasserstein μ ν ≤ ∫ ω, adaptedDistance κ (X ω) (Y ω) ∂P := by
  have h := wasserstein_le_cost (jointCoupling P X Y hX hY μ ν hμ hν)
  unfold Coupling.cost jointCoupling at h
  rwa [integral_map_of_stronglyMeasurable (hX.prodMk hY)
    (measurable_of_countable (fun p : State D × State D => adaptedDistance κ p.1 p.2)).stronglyMeasurable] at h

/-- The paired adapted-distance costs are uniformly integrable under a
uniform superlinear Lyapunov bound for each endpoint. No independence is used. -/
theorem uniformIntegrable_distance {I : Type*} (Ψ : State D → ℝ)
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (X Y : I → Ω → State D) (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hΨX : ∀ i, Integrable (fun ω => Ψ (X i ω)) P)
    (hΨY : ∀ i, Integrable (fun ω => Ψ (Y i ω)) P)
    (C : ℝ) (hC : 0 ≤ C)
    (hboundX : ∀ i, (∫ ω, Ψ (X i ω) ∂P) ≤ C)
    (hboundY : ∀ i, (∫ ω, Ψ (Y i ω) ∂P) ≤ C) :
    UniformIntegrable (fun i ω => adaptedDistance κ (X i ω) (Y i ω)) 1 P := by
  apply LyapunovTails.uniformIntegrable_of_affine_envelope P _
    (fun i ω => Ψ (X i ω) + Ψ (Y i ω))
    (fun i => ((measurable_of_countable (fun p : State D × State D => adaptedDistance κ p.1 p.2)).comp
      ((hX i).prodMk (hY i))).aestronglyMeasurable)
    (fun i => (hΨX i).add (hΨY i)) _ (2 * C) (mul_nonneg (by norm_num) hC) _
  · intro δ hδ
    obtain ⟨B, hB, hweight⟩ := LyapunovTails.exists_affine_weight_bound hdom hsuper hδ
    refine ⟨2 * B, mul_nonneg (by norm_num) hB, ?_⟩
    intro i ω
    change ‖adaptedDistance κ (X i ω) (Y i ω)‖ ≤ 2 * B + δ * (Ψ (X i ω) + Ψ (Y i ω))
    rw [Real.norm_eq_abs, abs_of_nonneg (adaptedDistance_nonneg κ _ _)]
    have hd := adaptedDistance_le_weights (κ := κ) (X i ω) (Y i ω)
    linarith [hweight (X i ω), hweight (Y i ω)]
  · intro i ω
    change 0 ≤ Ψ (X i ω) + Ψ (Y i ω)
    have hx := hdom (X i ω)
    have hy := hdom (Y i ω)
    linarith [momentWeight_nonneg κ (X i ω), momentWeight_nonneg κ (Y i ω)]
  · intro i
    rw [integral_add (hΨX i) (hΨY i)]
    linarith [hboundX i, hboundY i]

/-- Almost-sure state convergence and bounded genuine superlinear moments
imply convergence of the expected adapted distance on the common space. -/
theorem integral_distance_tendsto_zero (Ψ : State D → ℝ)
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (X : ℕ → Ω → State D) (Y : Ω → State D)
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (hΨX : ∀ n, Integrable (fun ω => Ψ (X n ω)) P) (hΨY : Integrable (fun ω => Ψ (Y ω)) P)
    (C : ℝ) (hC : 0 ≤ C)
    (hboundX : ∀ n, (∫ ω, Ψ (X n ω) ∂P) ≤ C) (hboundY : (∫ ω, Ψ (Y ω) ∂P) ≤ C)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Tendsto (fun n => ∫ ω, adaptedDistance κ (X n ω) (Y ω) ∂P) atTop (𝓝 0) := by
  have hui := uniformIntegrable_distance P Ψ hdom hsuper X (fun _ => Y) hX (fun _ => hY)
    hΨX (fun _ => hΨY) C hC hboundX (fun _ => hboundY)
  have hcost : ∀ᵐ ω ∂P,
      Tendsto (fun n => adaptedDistance κ (X n ω) (Y ω)) atTop (𝓝 0) := by
    filter_upwards [hconv] with ω hω
    have hc : Continuous (fun x : State D => adaptedDistance κ x (Y ω)) := continuous_of_discreteTopology
    simpa only [adaptedDistance_self] using hc.continuousAt.tendsto.comp hω
  have hm : TendstoInMeasure P (fun n ω => adaptedDistance κ (X n ω) (Y ω)) atTop 0 :=
    tendstoInMeasure_of_tendsto_ae hui.aestronglyMeasurable hcost
  have h := LyapunovTails.integral_abs_tendsto_zero_of_uniformIntegrable P _ hui hm
  simpa only [abs_of_nonneg (adaptedDistance_nonneg κ _ _)] using h

/-- The actual marginal transport distances converge to zero. The laws are
identified by pushforwards, not by an assumed convergence property. -/
theorem wasserstein_tendsto_zero (Ψ : State D → ℝ)
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (X : ℕ → Ω → State D) (Y : Ω → State D)
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (hΨX : ∀ n, Integrable (fun ω => Ψ (X n ω)) P) (hΨY : Integrable (fun ω => Ψ (Y ω)) P)
    (C : ℝ) (hC : 0 ≤ C)
    (hboundX : ∀ n, (∫ ω, Ψ (X n ω) ∂P) ≤ C) (hboundY : (∫ ω, Ψ (Y ω) ∂P) ≤ C)
    (μ : ℕ → MomentLaw κ D) (ν : MomentLaw κ D)
    (hμ : ∀ n, P.map (X n) = (μ n).measure) (hν : P.map Y = ν.measure)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Tendsto (fun n => wasserstein (μ n) ν) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => wasserstein_nonneg _ _)
    (fun n => wasserstein_le_integral_distance P (X n) Y (hX n) hY (μ n) ν (hμ n) hν)
  exact integral_distance_tendsto_zero P Ψ hdom hsuper X Y hX hY hΨX hΨY C hC hboundX hboundY hconv

/-- On a sequential parameter space, continuity at each fixed time on its
own probability-one event suffices for a continuous transport-law curve. -/
theorem continuous_marginals {I : Type*} [TopologicalSpace I] [SequentialSpace I]
    (Ψ : State D → ℝ) (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (X : I → Ω → State D) (hX : ∀ t, Measurable (X t))
    (hΨ : ∀ t, Integrable (fun ω => Ψ (X t ω)) P)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t, (∫ ω, Ψ (X t ω) ∂P) ≤ C)
    (μ : I → MomentLaw κ D) (hμ : ∀ t, P.map (X t) = (μ t).measure)
    (hpath : ∀ t, ∀ᵐ ω ∂P, ContinuousAt (fun s => X s ω) t) : Continuous μ := by
  apply continuous_iff_seqContinuous.mpr
  intro u t hut
  apply tendsto_iff_dist_tendsto_zero.mpr
  change Tendsto (fun n => wasserstein (μ (u n)) (μ t)) atTop (𝓝 0)
  apply wasserstein_tendsto_zero P Ψ hdom hsuper (fun n => X (u n)) (X t)
    (fun n => hX (u n)) (hX t) (fun n => hΨ (u n)) (hΨ t) C hC
    (fun n => hbound (u n)) (hbound t) (fun n => μ (u n)) (μ t)
    (fun n => hμ (u n)) (hμ t)
  filter_upwards [hpath t] with ω hω
  exact hω.tendsto.comp hut

end CarryingCapacity.LawCurveContinuity
