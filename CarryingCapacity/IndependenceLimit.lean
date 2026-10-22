import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Independence under almost-sure eventual equality

Locally finite count observations stabilize along a decreasing time sequence.
Bounded indicator convergence then preserves independence from an entire
sigma algebra, without any topology or continuity assumption on the target.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal

namespace CarryingCapacity.IndependenceLimit

variable {Ω B : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace B]
  (P : Measure Ω) [IsProbabilityMeasure P]

theorem tendsto_measure_of_eventually_membership (S : ℕ → Set Ω) (T : Set Ω)
    (hS : ∀ n, MeasurableSet (S n)) (hT : MeasurableSet T)
    (he : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, (ω ∈ S n) = (ω ∈ T)) :
    Tendsto (fun n => P (S n)) atTop (𝓝 (P T)) := by
  have hi : Tendsto (fun n => ∫⁻ ω, (S n).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P)
      atTop (𝓝 (∫⁻ ω, T.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P)) := by
    apply tendsto_lintegral_of_dominated_convergence (fun _ => (1 : ℝ≥0∞))
      (fun n => measurable_const.indicator (hS n))
    · intro n
      filter_upwards [] with ω
      by_cases hω : ω ∈ S n <;> simp [hω]
    · simp
    · filter_upwards [he] with ω hω
      apply tendsto_const_nhds.congr'
      filter_upwards [hω] with n hn
      simp only [Set.indicator_apply,hn]
  change Tendsto (fun n => ∫⁻ ω, (S n).indicator (1 : Ω → ℝ≥0∞) ω ∂P)
    atTop (𝓝 (∫⁻ ω, T.indicator (1 : Ω → ℝ≥0∞) ω ∂P)) at hi
  simpa only [lintegral_indicator_one (hS _),lintegral_indicator_one hT] using hi

/-- Eventual samplewise agreement passes independence from a whole fixed past
sigma algebra to the limiting observation. -/
theorem indep_of_ae_eventuallyEq (F : MeasurableSpace Ω) (hF : F ≤ mΩ)
    (f : ℕ → Ω → B) (g : Ω → B)
    (hf : ∀ n, @Measurable Ω B mΩ _ (f n)) (hg : @Measurable Ω B mΩ _ g)
    (hind : ∀ n, Indep F (MeasurableSpace.comap (f n) inferInstance) P)
    (he : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, f n ω = g ω) :
    Indep F (MeasurableSpace.comap g inferInstance) P := by
  letI : MeasurableSpace Ω := mΩ
  apply (Indep_iff _ _ _).mpr
  intro S T hS hT
  obtain ⟨C,hC,rfl⟩ := hT
  have hpre : Tendsto (fun n => P (f n ⁻¹' C)) atTop (𝓝 (P (g ⁻¹' C))) := by
    apply tendsto_measure_of_eventually_membership P _ _ (fun n => hC.preimage (hf n))
      (hC.preimage hg)
    filter_upwards [he] with ω hω
    filter_upwards [hω] with n hn
    exact congrArg (fun b => b ∈ C) hn
  have hinter : Tendsto (fun n => P (S ∩ f n ⁻¹' C)) atTop (𝓝 (P (S ∩ g ⁻¹' C))) := by
    apply tendsto_measure_of_eventually_membership P _ _
      (fun n => (hF S hS).inter (hC.preimage (hf n))) ((hF S hS).inter (hC.preimage hg))
    filter_upwards [he] with ω hω
    filter_upwards [hω] with n hn
    exact congrArg (fun b => ω ∈ S ∧ b ∈ C) hn
  have heq : ∀ n, P (S ∩ f n ⁻¹' C) = P S * P (f n ⁻¹' C) := fun n =>
    (Indep_iff _ _ _).mp (hind n) S _ hS ⟨C,hC,rfl⟩
  have hmul : Tendsto (fun n => P S * P (f n ⁻¹' C)) atTop (𝓝 (P S * P (g ⁻¹' C))) :=
    ENNReal.Tendsto.const_mul hpre (Or.inr (measure_ne_top P S))
  exact tendsto_nhds_unique hinter (hmul.congr' (Filter.Eventually.of_forall
    (fun n => (heq n).symm)))

end CarryingCapacity.IndependenceLimit
