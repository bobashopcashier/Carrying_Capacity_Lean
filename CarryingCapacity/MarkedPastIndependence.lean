import CarryingCapacity.MarkedPastTransform
import CarryingCapacity.MarkedTimeCounts
import CarryingCapacity.CylinderIndependence
import CarryingCapacity.CountRestriction

/-!
# Future marked counts are independent of the full observed strip history

The past observation retains every indexed arrival time and mark that has
occurred. Finite cylinders are tested against the future count's complex power
transform. Uniqueness identifies the restricted count law without dividing by
the cylinder probability. A generating pi-system then gives independence from
the whole observation, rather than only from finitely many past counts.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

namespace CarryingCapacity.MarkedPastIndependence
open CountableJumpProcess FrozenProcess MarkedNoise MarkedObservation
  MarkedPastProducts MarkedPastTransform MarkedStripCounts MarkedTimeCounts MarkedThinning

theorem futureTimeProduct_markFactor_ae (B : Set ℝ) (s t : ℝ) (ht : 0 ≤ t) (z : ℂ) :
    futureTimeProduct s t (markFactor B z) =ᵐ[stripLaw]
      (fun ω => z ^ windowCount B s (s+t) ω) := by
  filter_upwards [strip_ae_good] with ω hω
  have he : windowCount B s (s+t) ω =
      indexCount B (proposalCount ω.1 s) (proposalCount ω.1 (s+t)) ω.2 :=
    prefixCount_sub_eq_indexCount B
      ((proposalCount_mono hω.1.2) (le_add_of_nonneg_right ht)) ω.2
  rw [he]
  exact indexProduct_indicator_eq_pow B z _ _ _

/-- Weighted future-count transform for arbitrary finite tests of past arrivals and marks. -/
theorem integral_observedProduct_window_pow (B : Set ℝ) (hB : MeasurableSet B)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (K : Finset ℕ)
    (F : ℕ → (ℝ × ℝ) → ℂ) (hF : ∀ k, Measurable (F k))
    (hFb : ∀ k p, ‖F k p‖ ≤ 1) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    (∫ ω, observedProduct s K F ω * z ^ windowCount B s (s+t) ω ∂stripLaw) =
      (∫ ω, observedProduct s K F ω ∂stripLaw) *
        Complex.exp (((t * uniformUnit.real B : ℝ) : ℂ) * (z-1)) := by
  have he : (∫ ω, observedProduct s K F ω * z ^ windowCount B s (s+t) ω ∂stripLaw) =
      ∫ ω, observedProduct s K F ω * futureTimeProduct s t (markFactor B z) ω
        ∂stripLaw := by
    apply integral_congr_ae
    filter_upwards [futureTimeProduct_markFactor_ae B s t ht z] with ω hω
    rw [hω]
  rw [he, integral_observedProduct_mul_future s t hs ht K F hF hFb
    (markFactor B z) (measurable_markFactor B hB z) (norm_markFactor_le_one B z hz),
    integral_markFactor B hB z]
  congr 2
  push_cast
  ring

theorem integral_windowCount_pow (B : Set ℝ) (hB : MeasurableSet B)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    (∫ ω, z ^ windowCount B s (s+t) ω ∂stripLaw) =
      Complex.exp (((t * uniformUnit.real B : ℝ) : ℂ) * (z-1)) := by
  simpa [observedProduct] using integral_observedProduct_window_pow B hB s t hs ht ∅
    (fun _ _ => 1) (fun _ => measurable_const) (by intros; simp) z hz

/-- The future category count has its genuine Poisson law, even at zero intensity. -/
theorem windowCount_map (B : Set ℝ) (hB : MeasurableSet B)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Measure.map (windowCount B s (s+t)) stripLaw =
      poissonMeasure ⟨t * uniformUnit.real B, mul_nonneg ht measureReal_nonneg⟩ := by
  apply natMeasure_eq_of_pow_integrals
  intro z hz
  rw [integral_map_of_stronglyMeasurable (measurable_windowCount B hB s (s+t))
    (measurable_of_countable _).stronglyMeasurable,
    integral_windowCount_pow B hB s t hs ht z hz, PoissonTransform.integral_poisson_pow]
  rfl

/-- Indicators are set to one outside the chosen finite coordinates. -/
def cylinderFactors (K : Finset ℕ) (A : ℕ → Set (ℝ × ℝ)) (k : ℕ) (p : ℝ × ℝ) : ℂ := by
  classical
  exact if k ∈ K then (A k).indicator (fun _ => 1) p else 1

theorem measurable_cylinderFactors (K : Finset ℕ) (A : ℕ → Set (ℝ × ℝ))
    (hA : ∀ k ∈ K, MeasurableSet (A k)) (k : ℕ) :
    Measurable (cylinderFactors K A k) := by
  classical
  change Measurable (fun p => if k ∈ K then (A k).indicator (fun _ => (1 : ℂ)) p else 1)
  by_cases hk : k ∈ K
  · simpa only [hk, if_true] using
      (measurable_const.indicator (hA k hk) : Measurable ((A k).indicator (fun _ => (1 : ℂ))))
  · simpa only [hk, if_false] using
      (measurable_const : Measurable (fun _ : ℝ × ℝ => (1 : ℂ)))

theorem norm_cylinderFactors_le_one (K : Finset ℕ) (A : ℕ → Set (ℝ × ℝ))
    (k : ℕ) (p : ℝ × ℝ) : ‖cylinderFactors K A k p‖ ≤ 1 := by
  classical
  by_cases hk : k ∈ K <;> by_cases hp : p ∈ A k <;> simp [cylinderFactors, hk, hp]

theorem observedProduct_cylinderFactors (s : ℝ) (K : Finset ℕ) (A : ℕ → Set (ℝ × ℝ)) :
    observedProduct s K (cylinderFactors K A) =
      (CylinderIndependence.cylinder (stripView s) K A).indicator (fun _ => (1 : ℂ)) := by
  classical
  funext ω
  have he : observedProduct s K (cylinderFactors K A) ω =
      ∏ k ∈ K, (if stripView s ω k ∈ A k then (1 : ℂ) else 0) := by
    apply Finset.prod_congr rfl
    intro k hk
    simp [cylinderFactors, hk, Set.indicator_apply]
  rw [he, Finset.prod_boole]
  simp only [CylinderIndependence.cylinder, Set.indicator_apply,
    Set.mem_iInter, Set.mem_preimage]

/-- Every past cylinder has the unchanged future Poisson law after restriction. -/
theorem windowCount_map_restrict_cylinder (B : Set ℝ) (hB : MeasurableSet B)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (K : Finset ℕ)
    (A : ℕ → Set (ℝ × ℝ)) (hA : ∀ k ∈ K, MeasurableSet (A k)) :
    Measure.map (windowCount B s (s+t))
      (stripLaw.restrict (CylinderIndependence.cylinder (stripView s) K A)) =
      stripLaw (CylinderIndependence.cylinder (stripView s) K A) •
        poissonMeasure ⟨t * uniformUnit.real B, mul_nonneg ht measureReal_nonneg⟩ := by
  have hC := CylinderIndependence.measurableSet_cylinder (stripView s)
    (measurable_pi_lambda _ (measurable_stripView s)) K A hA
  apply CountRestriction.map_restrict_eq_smul_of_indicator_mul_pow_integrals stripLaw
    (windowCount B s (s+t)) (measurable_windowCount B hB s (s+t)) _ hC
  intro z hz
  have h := integral_observedProduct_window_pow B hB s t hs ht K (cylinderFactors K A)
    (measurable_cylinderFactors K A hA) (norm_cylinderFactors_le_one K A) z hz
  rw [observedProduct_cylinderFactors s K A, integral_indicator_const _ hC,
    Complex.real_smul, mul_one] at h
  rw [PoissonTransform.integral_poisson_pow]
  exact h

/-- Future counts are independent of every indexed arrival time and mark
observed by time s, jointly over the entire observation sequence. -/
theorem independent_stripView_windowCount (B : Set ℝ) (hB : MeasurableSet B)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IndepFun (stripView s) (windowCount B s (s+t)) stripLaw := by
  apply CylinderIndependence.indepFun_of_cylinder_factorization
    (stripView s) (windowCount B s (s+t))
    (measurable_pi_lambda _ (measurable_stripView s)) (measurable_windowCount B hB s (s+t))
  intro K A hA D hD
  have h := congrArg (fun μ : Measure ℕ => μ D)
    (windowCount_map_restrict_cylinder B hB s t hs ht K A hA)
  dsimp only at h
  rw [Measure.map_apply (measurable_windowCount B hB s (s+t)) hD,
    Measure.restrict_apply ((measurable_windowCount B hB s (s+t)) hD),
    Measure.smul_apply, smul_eq_mul] at h
  have hfuture := congrArg (fun μ : Measure ℕ => μ D) (windowCount_map B hB s t hs ht)
  dsimp only at hfuture
  rw [Measure.map_apply (measurable_windowCount B hB s (s+t)) hD] at hfuture
  rw [hfuture]
  simpa only [Set.inter_comm] using h

end CarryingCapacity.MarkedPastIndependence
