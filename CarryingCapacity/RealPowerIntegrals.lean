import CarryingCapacity.RealPowerMoment

/-! # Integral inequalities for real power costs

These are inequalities for genuine integrable functions. They will be applied
to a transport plan times the finite counting measure on the coordinates.
-/

noncomputable section
open MeasureTheory Filter

namespace CarryingCapacity.RealPowerIntegrals

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem memLp_of_integrable_rpow {p : ℝ} (hp : 0 < p) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hi : Integrable (fun x => f x ^ p) μ) : MemLp f (ENNReal.ofReal p) μ := by
  apply (integrable_norm_rpow_iff hf (by positivity) ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using hi

theorem integrable_rpow_mul {p : ℝ} (hp : 1 < p) {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : Integrable (fun x => f x ^ p) μ)
    (hgi : Integrable (fun x => g x ^ p) μ) :
    Integrable (fun x => f x ^ (p - 1) * g x) μ := by
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  letI := hpq.symm.ennrealOfReal
  have hfq : MemLp (fun x => f x ^ (p - 1)) (ENNReal.ofReal (p / (p - 1))) μ := by
    apply memLp_of_integrable_rpow hpq.symm.pos
      (hf.aemeasurable.pow_const _).aestronglyMeasurable
      (fun x => Real.rpow_nonneg (hf0 x) _)
    convert hfi using 1
    ext x
    rw [← Real.rpow_mul (hf0 x)]
    congr 1
    field_simp [ne_of_gt (sub_pos.mpr hp)]
  exact hfq.integrable_mul (memLp_of_integrable_rpow hpq.pos hg hg0 hgi)

/-- Hölder for the power appearing in the secant estimate. -/
theorem integral_rpow_mul_le {p : ℝ} (hp : 1 < p) {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : Integrable (fun x => f x ^ p) μ)
    (hgi : Integrable (fun x => g x ^ p) μ) :
    (∫ x, f x ^ (p - 1) * g x ∂μ) ≤
      (∫ x, f x ^ p ∂μ) ^ ((p - 1) / p) * (∫ x, g x ^ p ∂μ) ^ (1 / p) := by
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  have heq (x : Ω) : (f x ^ (p - 1)) ^ (p / (p - 1)) = f x ^ p := by
    rw [← Real.rpow_mul (hf0 x)]
    congr 1
    field_simp [ne_of_gt (sub_pos.mpr hp)]
  have hfq : MemLp (fun x => f x ^ (p - 1)) (ENNReal.ofReal (p / (p - 1))) μ := by
    apply memLp_of_integrable_rpow hpq.symm.pos
      (hf.aemeasurable.pow_const _).aestronglyMeasurable
      (fun x => Real.rpow_nonneg (hf0 x) _)
    simpa only [heq] using hfi
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq.symm
    (ae_of_all _ fun x => Real.rpow_nonneg (hf0 x) _)
    (ae_of_all _ hg0) hfq (memLp_of_integrable_rpow hpq.pos hg hg0 hgi)
  simpa only [heq, one_div_div] using h

/-- The real Lp size, used only when the indicated power is integrable. -/
def lpSize (p : ℝ) (μ : Measure Ω) (f : Ω → ℝ) : ℝ :=
  (∫ x, |f x| ^ p ∂μ) ^ (1 / p)

theorem lpSize_nonneg (p : ℝ) (μ : Measure Ω) (f : Ω → ℝ) :
    0 ≤ lpSize p μ f := Real.rpow_nonneg (integral_nonneg fun _ =>
      Real.rpow_nonneg (abs_nonneg _) _) _

theorem ofReal_lpSize {p : ℝ} (hp : 0 < p) {f : Ω → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    ENNReal.ofReal (lpSize p μ f) = eLpNorm f (ENNReal.ofReal p) μ := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by positivity) ENNReal.ofReal_ne_top]
  simp only [lpSize, ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs, one_div]

theorem lpSize_add_le {p : ℝ} (hp : 1 ≤ p) {f g : Ω → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) μ) (hg : MemLp g (ENNReal.ofReal p) μ) :
    lpSize p μ (f + g) ≤ lpSize p μ f + lpSize p μ g := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  apply (ENNReal.ofReal_le_ofReal_iff (add_nonneg (lpSize_nonneg _ _ _) (lpSize_nonneg _ _ _))).mp
  rw [ofReal_lpSize hp0 (hf.add hg), ENNReal.ofReal_add (lpSize_nonneg _ _ _) (lpSize_nonneg _ _ _),
    ofReal_lpSize hp0 hf, ofReal_lpSize hp0 hg]
  exact eLpNorm_add_le hf.1 hg.1 (by simpa using ENNReal.ofReal_le_ofReal hp)

end CarryingCapacity.RealPowerIntegrals
