import CarryingCapacity.IntegralGronwall

/-!
# Gronwall for integrable subsolutions and forcing

The expected stopped cost need not first be proved continuous. Its continuous
primitive supplies an envelope to which the continuous Gronwall theorem
applies. The forcing is merely integrable and nonnegative almost everywhere.
Neither the subsolution nor the initial constant requires nonnegativity.
-/

noncomputable section
open MeasureTheory Set Filter

namespace CarryingCapacity.IntegrableGronwall

/-- An integrable subsolution has the usual terminal exponential bound even
without continuity. The forcing's nonnegativity is needed only almost everywhere. -/
theorem endpoint_le_exp_mul_add_integral {u g : ℝ → ℝ} {a b T : ℝ}
    (hT : 0 ≤ T) (hu : IntegrableOn u (Ioc 0 T)) (hg : IntegrableOn g (Ioc 0 T))
    (hg_nonneg : 0 ≤ᵐ[volume.restrict (Ioc 0 T)] g) (hb : 0 ≤ b)
    (hbound : ∀ t ∈ Icc 0 T, u t ≤ a + b * ∫ s in Ioc 0 t, (u s + g s)) :
    u T ≤ (a + b * ∫ s in Ioc 0 T, g s) * Real.exp (b * T) := by
  let A := a + b * ∫ s in Ioc 0 T, g s
  let F : ℝ → ℝ := fun t => A + b * ∫ s in Ioc 0 t, u s
  have hcont : ContinuousOn F (Icc 0 T) :=
    continuousOn_const.add (continuousOn_const.mul
      (intervalIntegral.continuousOn_primitive
        (integrableOn_Icc_iff_integrableOn_Ioc.mpr hu)))
  have huF : ∀ t ∈ Icc 0 T, u t ≤ F t := by
    intro t ht
    have hsub : Ioc (0 : ℝ) t ⊆ Ioc 0 T := Ioc_subset_Ioc_right ht.2
    have hgt : (∫ s in Ioc 0 t, g s) ≤ ∫ s in Ioc 0 T, g s :=
      setIntegral_mono_set hg hg_nonneg (Eventually.of_forall (fun s hs => hsub hs))
    have h := hbound t ht
    rw [integral_add (hu.mono_set hsub) (hg.mono_set hsub)] at h
    have hmul := mul_le_mul_of_nonneg_left hgt hb
    dsimp only [F, A]
    linarith
  have hFbound : ∀ t ∈ Icc 0 T, F t ≤ A + b * ∫ s in Ioc 0 t, F s := by
    intro t ht
    have hsub : Ioc (0 : ℝ) t ⊆ Ioc 0 T := Ioc_subset_Ioc_right ht.2
    have hFi : IntegrableOn F (Ioc 0 t) := hcont.integrableOn_Icc.mono_set
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2))
    have hi : (∫ s in Ioc 0 t, u s) ≤ ∫ s in Ioc 0 t, F s := by
      apply setIntegral_mono_ae_restrict (hu.mono_set hsub) hFi
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact huF s ⟨hs.1.le, hs.2.trans ht.2⟩
    exact add_le_add_left (mul_le_mul_of_nonneg_left hi hb) A
  exact (huF T ⟨hT, le_rfl⟩).trans
    (IntegralGronwall.endpoint_le_exp_mul hT hcont hb hFbound)

/-- The bound holds at every time, with the forcing integrated only up to that
time. All integrability and AE sign hypotheses are restricted from the full horizon. -/
theorem le_exp_mul_add_integral {u g : ℝ → ℝ} {a b T : ℝ}
    (hu : IntegrableOn u (Ioc 0 T)) (hg : IntegrableOn g (Ioc 0 T))
    (hg_nonneg : 0 ≤ᵐ[volume.restrict (Ioc 0 T)] g) (hb : 0 ≤ b)
    (hbound : ∀ t ∈ Icc 0 T, u t ≤ a + b * ∫ s in Ioc 0 t, (u s + g s)) :
    ∀ t ∈ Icc 0 T, u t ≤ (a + b * ∫ s in Ioc 0 t, g s) * Real.exp (b * t) := by
  intro t ht
  have hsub : Ioc (0 : ℝ) t ⊆ Ioc 0 T := Ioc_subset_Ioc_right ht.2
  exact endpoint_le_exp_mul_add_integral ht.1 (hu.mono_set hsub) (hg.mono_set hsub)
    (ae_restrict_of_ae_restrict_of_subset hsub hg_nonneg) hb
    (fun s hs => hbound s ⟨hs.1, hs.2.trans ht.2⟩)

/-- A pointwise nonnegative forcing is a convenient specialization for expected
empirical errors; continuity is still not required of either function. -/
theorem endpoint_le_exp_mul_add_integral_of_nonneg {u g : ℝ → ℝ} {a b T : ℝ}
    (hT : 0 ≤ T) (hu : IntegrableOn u (Ioc 0 T)) (hg : IntegrableOn g (Ioc 0 T))
    (hg_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ g t) (hb : 0 ≤ b)
    (hbound : ∀ t ∈ Icc 0 T, u t ≤ a + b * ∫ s in Ioc 0 t, (u s + g s)) :
    u T ≤ (a + b * ∫ s in Ioc 0 T, g s) * Real.exp (b * T) := by
  apply endpoint_le_exp_mul_add_integral hT hu hg _ hb hbound
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact hg_nonneg s ⟨hs.1.le, hs.2⟩

end CarryingCapacity.IntegrableGronwall
