import CarryingCapacity.IntegralGronwallComparison

/-!
# Forced Gronwall with the explicit Volterra kernel

The integrating-factor solution is differentiated using the fundamental
theorem of calculus. Its integral equation supplies the supersolution in
the proved integral comparison theorem. This derives the precise exponential
convolution needed for the manuscript's Bielecki contraction argument.
-/

noncomputable section
open MeasureTheory Set

namespace CarryingCapacity.VolterraGronwall

/-- The actual integrating-factor response to a continuous forcing function. -/
def response (a b : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (b * t) * (a + ∫ s in (0 : ℝ)..t, Real.exp (-b * s) * g s)

theorem hasDerivAt_response (a b : ℝ) {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ) :
    HasDerivAt (response a b g) (b * response a b g t + g t) t := by
  have hc : Continuous (fun s : ℝ => Real.exp (-b * s) * g s) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hg
  have he := (((hasDerivAt_id t).const_mul b).exp).mul
    ((hc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add a)
  convert he using 1
  have hcancel : Real.exp (b * t) * Real.exp (-b * t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  dsimp only [response, id_eq]
  rw [← mul_assoc (Real.exp (b * t)) (Real.exp (-b * t)) (g t), hcancel]
  ring

theorem continuous_response (a b : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (response a b g) :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_response a b hg t).continuousAt)

@[simp] theorem response_zero (a b : ℝ) (g : ℝ → ℝ) : response a b g 0 = a := by
  simp [response]

/-- The explicit response satisfies the integral equation on every nonnegative horizon. -/
theorem response_integral_eq (a b : ℝ) {g : ℝ → ℝ} (hg : Continuous g)
    (t : ℝ) (ht : 0 ≤ t) :
    a + ∫ s in Ioc 0 t, (b * response a b g s + g s) = response a b g t := by
  have hi : IntervalIntegrable (fun s => b * response a b g s + g s) volume 0 t :=
    ((continuous_const.mul (continuous_response a b hg)).add hg).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_response a b hg s) hi
  rw [intervalIntegral.integral_of_le ht, response_zero] at he
  linarith

/-- Rewriting the integrating factor gives the actual exponential convolution. -/
theorem response_eq_convolution (a b : ℝ) (g : ℝ → ℝ) (t : ℝ) :
    response a b g t = a * Real.exp (b * t) +
      ∫ s in (0 : ℝ)..t, Real.exp (b * (t - s)) * g s := by
  rw [response, mul_add, mul_comm _ a, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- A continuous integral subsolution is bounded by the explicit forced
response; neither the subsolution nor the forcing needs to be nonnegative. -/
theorem le_exp_mul_add_convolution {u g : ℝ → ℝ} {a b T : ℝ}
    (hT : 0 ≤ T) (hu : ContinuousOn u (Icc 0 T)) (hg : Continuous g) (hb : 0 ≤ b)
    (hbound : ∀ t ∈ Icc 0 T, u t ≤ a + ∫ s in Ioc 0 t, (b * u s + g s)) :
    ∀ t ∈ Icc 0 T, u t ≤ a * Real.exp (b * t) +
      ∫ s in (0 : ℝ)..t, Real.exp (b * (t - s)) * g s := by
  have h := IntegralGronwallComparison.le_of_integral_subsolution hT hu
    (continuous_response a b hg).continuousOn hb
    (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self) hbound
    (fun t ht => (response_integral_eq a b hg t ht.1).le)
  intro t ht
  simpa only [response_eq_convolution] using h t ht

/-- The exact zero-initial-distance estimate used in the nonlinear
prescribed-environment coupling argument. -/
theorem le_volterra {u d : ℝ → ℝ} {A T : ℝ}
    (hT : 0 ≤ T) (hu : ContinuousOn u (Icc 0 T)) (hd : Continuous d) (hA : 0 ≤ A)
    (hbound : ∀ t ∈ Icc 0 T, u t ≤ A * ∫ s in Ioc 0 t, (u s + d s)) :
    ∀ t ∈ Icc 0 T, u t ≤ A *
      ∫ s in (0 : ℝ)..t, Real.exp (A * (t - s)) * d s := by
  have h := le_exp_mul_add_convolution (g := fun s => A * d s)
    hT hu (continuous_const.mul hd) hA (a := 0) (by
    intro t ht
    simpa only [zero_add, ← mul_add, integral_const_mul] using hbound t ht)
  intro t ht
  have he : (∫ s in (0 : ℝ)..t, Real.exp (A * (t - s)) * (A * d s)) =
      A * ∫ s in (0 : ℝ)..t, Real.exp (A * (t - s)) * d s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  simpa only [zero_mul, zero_add, he] using h t ht

end CarryingCapacity.VolterraGronwall
