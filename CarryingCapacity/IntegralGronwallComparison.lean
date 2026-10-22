import CarryingCapacity.IntegralGronwall

/-!
# Comparison for integral inequalities with a common forcing term

A continuous subsolution lies below a continuous supersolution when both use
the same nonnegative linear coefficient and integrable additive forcing.
Subtracting the two inequalities reduces the comparison to the proved
homogeneous integral Gronwall theorem. No differentiability is assumed.
-/

noncomputable section
open MeasureTheory Set

namespace CarryingCapacity.IntegralGronwallComparison

/-- Ordered integral sub- and supersolutions with common forcing are ordered
on the entire finite interval. The forcing need only be integrable. -/
theorem le_of_integral_subsolution {u v g : ℝ → ℝ} {a b T : ℝ}
    (hT : 0 ≤ T) (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hb : 0 ≤ b) (hg : IntegrableOn g (Ioc 0 T))
    (hsub : ∀ t ∈ Icc 0 T, u t ≤ a + ∫ s in Ioc 0 t, (b * u s + g s))
    (hsuper : ∀ t ∈ Icc 0 T, a + ∫ s in Ioc 0 t, (b * v s + g s) ≤ v t) :
    ∀ t ∈ Icc 0 T, u t ≤ v t := by
  have hw := IntegralGronwall.le_exp_mul_of_setIntegral hT (hu.sub hv) hb
    (a := 0) (by
      intro t ht
      have hsubt : Ioc (0 : ℝ) t ⊆ Ioc 0 T := Ioc_subset_Ioc_right ht.2
      have hiu : IntegrableOn u (Ioc 0 t) :=
        hu.integrableOn_Icc.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2))
      have hiv : IntegrableOn v (Ioc 0 t) :=
        hv.integrableOn_Icc.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2))
      have hig := hg.mono_set hsubt
      have hs := hsub t ht
      have hv' := hsuper t ht
      rw [integral_add (hiu.const_mul b) hig, integral_const_mul] at hs
      rw [integral_add (hiv.const_mul b) hig, integral_const_mul] at hv'
      rw [integral_sub hiu hiv]
      linarith)
  intro t ht
  have h := hw t ht
  simp only [Pi.sub_apply, zero_mul] at h
  exact sub_nonpos.mp h

end CarryingCapacity.IntegralGronwallComparison
