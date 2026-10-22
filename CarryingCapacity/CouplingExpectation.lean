import CarryingCapacity.DeterministicEnvironmentRates
import CarryingCapacity.LawCurveContinuity

/-!
# Genuine expected coupling-activity bounds

The paper's pointwise coupling hypothesis implies integrability of the
positive-increment activity under any common-space coupling with finite
adapted moments. Its expectation is then bounded using actual moment bounds.
No stochastic coupling inequality or process evolution is assumed here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators

namespace CarryingCapacity.CouplingExpectation
open DeterministicEnvironmentRates

variable {D : ℕ} (κ : MomentScale) (q : Rates D (MomentLaw κ D))

theorem activity_nonnegative (x y : State D) (μ ν : MomentLaw κ D) :
    0 ≤ couplingActivity κ q x y μ ν := by
  apply Finset.sum_nonneg
  intro j _
  exact add_nonneg
    (add_nonneg (mul_nonneg (le_min (q.nonnegative j x μ) (q.nonnegative j y ν)) (le_max_right _ _))
      (mul_nonneg (le_max_right _ _) (le_max_right _ _)))
    (mul_nonneg (le_max_right _ _) (le_max_right _ _))

variable (hCoupling : MomentCouplingBound κ q)

/-- The selected constant retains exactly the stated positive-increment bound. -/
theorem activity_le (x y : State D) (μ ν : MomentLaw κ D) :
    couplingActivity κ q x y μ ν ≤ couplingConstant κ q hCoupling *
      ((1 + moment μ + moment ν) * adaptedDistance κ x y +
        (1 + momentWeight κ x + momentWeight κ y) * wasserstein μ ν) :=
  (Classical.choose_spec hCoupling).2 x y μ ν

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X Y : Ω → State D) (hX : Measurable X) (hY : Measurable Y)
  (hWX : Integrable (fun ω => momentWeight κ (X ω)) P)
  (hWY : Integrable (fun ω => momentWeight κ (Y ω)) P)
include hX hY hWX hWY

omit q hCoupling [IsProbabilityMeasure P] in
/-- The common-space distance is integrable by its two endpoint weights. -/
theorem integrable_distance : Integrable (fun ω => adaptedDistance κ (X ω) (Y ω)) P := by
  apply (hWX.add hWY).mono'
    ((measurable_of_countable (fun p : State D × State D => adaptedDistance κ p.1 p.2)).comp
      (hX.prodMk hY)).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    dsimp only [Function.comp_def, Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (adaptedDistance_nonneg κ _ _)]
    exact adaptedDistance_le_weights _ _

include hCoupling hX hY hWX hWY

/-- Positive coupling activity is genuinely integrable, as a consequence of
the original pointwise assumption and finite endpoint moments. -/
theorem integrable_activity (μ ν : MomentLaw κ D) :
    Integrable (fun ω => couplingActivity κ q (X ω) (Y ω) μ ν) P := by
  have hi := (((integrable_distance κ P X Y hX hY hWX hWY).const_mul
    (1 + moment μ + moment ν)).add
    (((integrable_const (1 : ℝ)).add hWX).add hWY |>.mul_const (wasserstein μ ν))).const_mul
      (couplingConstant κ q hCoupling)
  apply hi.mono'
    ((measurable_of_countable (fun p : State D × State D => couplingActivity κ q p.1 p.2 μ ν)).comp
      (hX.prodMk hY)).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    dsimp only [Function.comp_def, Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (activity_nonnegative κ q _ _ μ ν)]
    exact activity_le κ q hCoupling _ _ μ ν

/-- Integration preserves the exact two terms in the weighted coupling bound. -/
theorem integral_activity_le (μ ν : MomentLaw κ D) :
    (∫ ω, couplingActivity κ q (X ω) (Y ω) μ ν ∂P) ≤
      couplingConstant κ q hCoupling *
        ((1 + moment μ + moment ν) * (∫ ω, adaptedDistance κ (X ω) (Y ω) ∂P) +
          (1 + (∫ ω, momentWeight κ (X ω) ∂P) + (∫ ω, momentWeight κ (Y ω) ∂P)) *
            wasserstein μ ν) := by
  have hd := integrable_distance κ P X Y hX hY hWX hWY
  have hw : Integrable (fun ω => 1 + momentWeight κ (X ω) + momentWeight κ (Y ω)) P :=
    ((integrable_const (1 : ℝ)).add hWX).add hWY
  have hwX : Integrable (fun ω => 1 + momentWeight κ (X ω)) P :=
    (integrable_const (1 : ℝ)).add hWX
  calc
    _ ≤ ∫ ω, couplingConstant κ q hCoupling *
        ((1 + moment μ + moment ν) * adaptedDistance κ (X ω) (Y ω) +
          (1 + momentWeight κ (X ω) + momentWeight κ (Y ω)) * wasserstein μ ν) ∂P :=
      integral_mono (integrable_activity κ q hCoupling P X Y hX hY hWX hWY μ ν)
        (((hd.const_mul _).add (hw.mul_const _)).const_mul _)
        (fun ω => activity_le κ q hCoupling _ _ μ ν)
    _ = _ := by
      rw [integral_const_mul, integral_add (hd.const_mul _) (hw.mul_const _),
        integral_const_mul, integral_mul_const, integral_add hwX hWY,
        integral_add (integrable_const (1 : ℝ)) hWX]
      simp

/-- Uniform bounds on both prescribed laws and both coupled endpoint moments
give precisely the coefficient used in the manuscript's Volterra argument. -/
theorem integral_activity_le_uniform (μ ν : MomentLaw κ D) (C : ℝ)
    (hμ : moment μ ≤ C) (hν : moment ν ≤ C)
    (hEX : (∫ ω, momentWeight κ (X ω) ∂P) ≤ C)
    (hEY : (∫ ω, momentWeight κ (Y ω) ∂P) ≤ C) :
    (∫ ω, couplingActivity κ q (X ω) (Y ω) μ ν ∂P) ≤
      (couplingConstant κ q hCoupling * (1 + 2 * C)) *
        ((∫ ω, adaptedDistance κ (X ω) (Y ω) ∂P) + wasserstein μ ν) := by
  apply (integral_activity_le κ q hCoupling P X Y hX hY hWX hWY μ ν).trans
  have hd : 0 ≤ ∫ ω, adaptedDistance κ (X ω) (Y ω) ∂P :=
    integral_nonneg (fun _ => adaptedDistance_nonneg κ _ _)
  have h₁ := mul_le_mul_of_nonneg_right (show 1 + moment μ + moment ν ≤ 1 + 2 * C by linarith) hd
  have h₂ := mul_le_mul_of_nonneg_right
    (show 1 + (∫ ω, momentWeight κ (X ω) ∂P) + (∫ ω, momentWeight κ (Y ω) ∂P) ≤ 1 + 2 * C by linarith)
    (wasserstein_nonneg μ ν)
  calc
    _ ≤ couplingConstant κ q hCoupling *
        ((1 + 2 * C) * (∫ ω, adaptedDistance κ (X ω) (Y ω) ∂P) +
          (1 + 2 * C) * wasserstein μ ν) :=
      mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (couplingConstant_nonnegative κ q hCoupling)
    _ = _ := by ring

end CarryingCapacity.CouplingExpectation
