import CarryingCapacity.CoupledPathLawConvergence

/-!
# Weak convergence to a deterministic point from concentration

The sample spaces may vary with the population size. Genuine AE-measurable
random variables whose distance from a fixed point tends to zero in probability
have pushforward probability laws converging weakly to the Dirac law. This
applies to the deterministic nonlinear curve in the actual J1 path space.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace CarryingCapacity.ConcentratingLaw
open CoupledPathLawConvergence

variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

def pointLaw (x : E) : ProbabilityMeasure E := ⟨Measure.dirac x, inferInstance⟩

theorem integral_difference_le_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → E) (hX : AEMeasurable X P)
    (x : E) (f : BoundedContinuousFunction E ℝ) (δ η : ℝ) (hη : 0 ≤ η)
    (hnear : ∀ y, dist y x ≤ δ → ‖f y - f x‖ ≤ η) :
    ‖(∫ p, f (X p) ∂P) - f x‖ ≤
      η + 2 * ‖f‖ * P.real {p | δ < dist (X p) x} := by
  let B : Set Ω := {p | δ < dist (X p) x}
  have hd : AEMeasurable (fun p => dist (X p) x) P :=
    (continuous_id.dist continuous_const).measurable.comp_aemeasurable hX
  have hB : NullMeasurableSet B P := nullMeasurableSet_lt aemeasurable_const hd
  let C := toMeasurable P B
  have hC : MeasurableSet C := measurableSet_toMeasurable P B
  have hiX : Integrable (fun p => f (X p)) P :=
    (f.integrable (P.map X)).comp_aemeasurable hX
  have hi : Integrable (fun p => η + C.indicator (fun _ => 2 * ‖f‖) p) P :=
    (integrable_const η).add ((integrable_const _).indicator hC)
  have hb : ∀ᵐ p ∂P, ‖f (X p) - f x‖ ≤
      η + C.indicator (fun _ => 2 * ‖f‖) p := by
    filter_upwards [hB.toMeasurable_ae_eq] with p hp
    have hp' : p ∈ C ↔ p ∈ B := iff_of_eq hp
    by_cases hpC : p ∈ C
    · rw [Set.indicator_of_mem hpC]
      have hnorm := norm_sub_le (f (X p)) (f x)
      have h1 := f.norm_coe_le_norm (X p)
      have h2 := f.norm_coe_le_norm x
      linarith
    · rw [Set.indicator_of_not_mem hpC, add_zero]
      exact hnear _ (le_of_not_gt (fun h => hpC (hp'.mpr h)))
  have he : (∫ p, f (X p) ∂P) - f x = ∫ p, (f (X p) - f x) ∂P := by
    rw [integral_sub hiX (integrable_const _), integral_const]
    simp
  rw [he]
  apply (norm_integral_le_of_norm_le hi hb).trans_eq
  rw [integral_add (integrable_const _) ((integrable_const _).indicator hC),
    integral_const, integral_indicator_const _ hC, smul_eq_mul]
  simp only [C, measureReal_def, measure_toMeasurable, measure_univ, ENNReal.toReal_one,
    one_smul, B, smul_eq_mul]
  ring

/-- Convergence in probability to a fixed point gives actual weak convergence
of laws, without identifying the varying underlying sample spaces. -/
theorem tendsto_imageLaw_of_probability_distance
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n, Ω n → E) (hX : ∀ n, AEMeasurable (X n) (P n)) (x : E)
    (htail : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => (P n).real {p | δ < dist (X n p) x}) atTop (𝓝 0)) :
    Tendsto (fun n => imageLaw (P n) (X n) (hX n)) atTop (𝓝 (pointLaw x)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hpoint : (∫ y, f y ∂(pointLaw x).toMeasure) = f x := by
    change (∫ y, f y ∂Measure.dirac x) = f x
    rw [integral_dirac]
  rw [hpoint]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp f.continuous.continuousAt
    (ε / 2) (by linarith)
  have hlim : Tendsto (fun n => 2 * ‖f‖ *
      (P n).real {p | δ / 2 < dist (X n p) x}) atTop (𝓝 0) := by
    simpa using (htail (δ / 2) (by linarith)).const_mul (2 * ‖f‖)
  filter_upwards [(tendsto_order.mp hlim).2 (ε / 2) (by linarith)] with n hn
  change dist (∫ y, f y ∂(P n).map (X n)) (f x) < ε
  rw [integral_map (hX n) f.continuous.measurable.stronglyMeasurable.aestronglyMeasurable,
    dist_eq_norm]
  have hb := integral_difference_le_tail (P n) (X n) (hX n) x f (δ / 2) (ε / 2)
    (by linarith) (fun y hy => (by
      have h := hnear (lt_of_le_of_lt hy (by linarith : δ / 2 < δ))
      simpa only [dist_eq_norm] using h.le))
  linarith

end CarryingCapacity.ConcentratingLaw
