import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc

/-!
# Integral Gronwall inequality

Continuity and the integral inequality imply the exponential bound. The
original function is not assumed differentiable. Instead, its accumulated
integral is differentiated using the fundamental theorem of calculus and
compared using mathlib's scalar differential Gronwall theorem.

Only nonnegativity of the integral coefficient is needed; the initial
constant and the function itself may have either sign.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace CarryingCapacity.IntegralGronwall

/-- Global continuity version, used after extending a function continuously
from its compact time interval. -/
theorem le_exp_mul_of_continuous {u : ℝ → ℝ} {a b T : ℝ}
    (hu : Continuous u) (hb : 0 ≤ b)
    (hbound : ∀ t ∈ Icc 0 T, u t ≤ a + b * ∫ s in (0 : ℝ)..t, u s) :
    ∀ t ∈ Icc 0 T, u t ≤ a * Real.exp (b * t) := by
  let F : ℝ → ℝ := fun t => a + b * ∫ s in (0 : ℝ)..t, u s
  have hderiv (t : ℝ) : HasDerivAt F (b * u t) t :=
    ((hu.integral_hasStrictDerivAt 0 t).hasDerivAt.const_mul b).const_add a
  have hcont : Continuous F := continuous_iff_continuousAt.mpr
    (fun t => (hderiv t).continuousAt)
  have hF : ∀ t ∈ Icc 0 T, F t ≤ gronwallBound a b 0 (t - 0) := by
    apply le_gronwallBound_of_liminf_deriv_right_le hcont.continuousOn
      (fun t _ r hr => (hderiv t).hasDerivWithinAt.liminf_right_slope_le hr)
    · simp [F]
    · intro t ht
      simpa only [add_zero] using mul_le_mul_of_nonneg_left
        (hbound t ⟨ht.1, ht.2.le⟩) hb
  intro t ht
  exact (hbound t ht).trans (by simpa only [gronwallBound_ε0, sub_zero] using hF t ht)

/-- Integral Gronwall on a finite interval. All derivative information is
derived from continuity and the fundamental theorem of calculus. -/
theorem le_exp_mul_of_intervalIntegral {u : ℝ → ℝ} {a b T : ℝ}
    (hT : 0 ≤ T) (hu : ContinuousOn u (Icc 0 T)) (hb : 0 ≤ b)
    (hbound : ∀ t ∈ Icc 0 T, u t ≤ a + b * ∫ s in (0 : ℝ)..t, u s) :
    ∀ t ∈ Icc 0 T, u t ≤ a * Real.exp (b * t) := by
  let v : ℝ → ℝ := IccExtend hT (fun s : Icc 0 T => u s)
  have hv : Continuous v := hu.restrict.Icc_extend'
  have heq : ∀ t ∈ Icc 0 T, v t = u t := by
    intro t ht
    exact IccExtend_of_mem hT (fun s : Icc 0 T => u s) ht
  have hint : ∀ t ∈ Icc 0 T,
      (∫ s in (0 : ℝ)..t, v s) = ∫ s in (0 : ℝ)..t, u s := by
    intro t ht
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact heq s ⟨hs.1, hs.2.trans ht.2⟩
  have h := le_exp_mul_of_continuous hv hb (T := T) (a := a) (by
    intro t ht
    simpa only [heq t ht, hint t ht] using hbound t ht)
  intro t ht
  simpa only [heq t ht] using h t ht

/-- A form matching time integrals against Lebesgue measure on `(0,t]`. -/
theorem le_exp_mul_of_setIntegral {u : ℝ → ℝ} {a b T : ℝ}
    (hT : 0 ≤ T) (hu : ContinuousOn u (Icc 0 T)) (hb : 0 ≤ b)
    (hbound : ∀ t ∈ Icc 0 T, u t ≤ a + b * ∫ s in Ioc (0 : ℝ) t, u s) :
    ∀ t ∈ Icc 0 T, u t ≤ a * Real.exp (b * t) := by
  apply le_exp_mul_of_intervalIntegral hT hu hb
  intro t ht
  simpa only [intervalIntegral.integral_of_le ht.1] using hbound t ht

/-- In particular, the desired bound holds at the terminal time. -/
theorem endpoint_le_exp_mul {u : ℝ → ℝ} {a b T : ℝ}
    (hT : 0 ≤ T) (hu : ContinuousOn u (Icc 0 T)) (hb : 0 ≤ b)
    (hbound : ∀ t ∈ Icc 0 T, u t ≤ a + b * ∫ s in Ioc (0 : ℝ) t, u s) :
    u T ≤ a * Real.exp (b * T) :=
  le_exp_mul_of_setIntegral hT hu hb hbound T ⟨hT, le_rfl⟩

end CarryingCapacity.IntegralGronwall
