import CarryingCapacity.FiniteJumpForward

/-!
# Restriction and local congruence of genuine weak forward equations

The weak forward equation can be restricted to a shorter nonnegative horizon.
Changing coefficients and candidate measures outside that horizon does not
change the equation. In both operations genuine time integrability is retained,
so the conclusions do not rely on the default value of a nonintegrable integral.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace CarryingCapacity.FiniteJumpForwardRestriction

open FiniteJumpForward

variable {E J : Type*} [Fintype J] [MeasurableSpace E]

omit [MeasurableSpace E] in
/-- At a fixed time the generator depends only on the rates at that time. -/
theorem generator_eq_of_rate_eq (jump : J → E → E)
    (rate rate' : J → ℝ → E → ℝ) (t : ℝ)
    (h : ∀ j x, rate j t x = rate' j t x) (f : E → ℝ) (x : E) :
    generator jump rate f t x = generator jump rate' f t x := by
  simp only [generator, h]

/-- A genuine forward solution on `[0,T]` remains a solution on `[0,S]`. -/
theorem restrict (jump : J → E → E) (rate : J → ℝ → E → ℝ)
    (α : Measure E) (p : ℝ → Measure E) (S T : ℝ)
    (hS : 0 ≤ S) (hST : S ≤ T) (hp : IsSolution jump rate α p T) :
    IsSolution jump rate α p S := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact hp.probability t ⟨ht.1, ht.2.trans hST⟩
  · intro f hf
    apply (hp.integrable f hf).mono_set
    rw [uIcc_of_le hS, uIcc_of_le (hS.trans hST)]
    exact Icc_subset_Icc_right hST
  · intro f hf t ht
    exact hp.equation f hf t ⟨ht.1, ht.2.trans hST⟩

/-- Only the values of the coefficients and the candidate on the given closed
time interval enter the weak equation and its genuine integrability condition. -/
theorem congr (jump : J → E → E) (rate rate' : J → ℝ → E → ℝ)
    (α : Measure E) (p p' : ℝ → Measure E) (T : ℝ) (hT : 0 ≤ T)
    (hp : IsSolution jump rate α p T)
    (hRate : ∀ t ∈ Icc 0 T, ∀ j x, rate j t x = rate' j t x)
    (hLaw : EqOn p p' (Icc 0 T)) : IsSolution jump rate' α p' T := by
  have hDrift (f : E → ℝ) :
      EqOn (fun s => ∫ x, generator jump rate f s x ∂p s)
        (fun s => ∫ x, generator jump rate' f s x ∂p' s) (Icc 0 T) := by
    intro s hs
    dsimp only
    rw [hLaw hs]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall
      (generator_eq_of_rate_eq jump rate rate' s (hRate s hs) f)
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [← hLaw ht]
    exact hp.probability t ht
  · intro f hf
    apply (hp.integrable f hf).congr
    rw [uIoc_of_le hT]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hDrift f ⟨hs.1.le, hs.2⟩
  · intro f hf t ht
    rw [← hLaw ht, hp.equation f hf t ht]
    congr 1
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le ht.1]
    exact (hDrift f).mono (Icc_subset_Icc_right ht.2)

/-- Restrict first and then change the coefficients and candidate only outside
the smaller interval. No agreement on the larger interval is required. -/
theorem restrict_congr (jump : J → E → E) (rate rate' : J → ℝ → E → ℝ)
    (α : Measure E) (p p' : ℝ → Measure E) (S T : ℝ)
    (hS : 0 ≤ S) (hST : S ≤ T) (hp : IsSolution jump rate α p T)
    (hRate : ∀ t ∈ Icc 0 S, ∀ j x, rate j t x = rate' j t x)
    (hLaw : EqOn p p' (Icc 0 S)) : IsSolution jump rate' α p' S :=
  congr jump rate rate' α p p' S hS
    (restrict jump rate α p S T hS hST hp) hRate hLaw

end CarryingCapacity.FiniteJumpForwardRestriction
