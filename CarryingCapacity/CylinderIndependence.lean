import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-!
# From finite observation cylinders to full-history independence

Finite intersections of coordinate-measurable events form a generating
pi-system for the supremum of the coordinate sigma algebras. Factorization
against every future measurable event therefore gives independence of the
whole observation history. No coordinate independence is required, and no
countability assumption on the observation index is needed for its product
sigma algebra.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set MeasurableSpace

namespace CarryingCapacity.CylinderIndependence

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- Factorization on finite intersections generates independence of the entire
supremum sigma algebra, not just independence of individual coordinates. -/
theorem indep_iSup_of_finite_intersections [IsProbabilityMeasure μ]
    (m : ι → MeasurableSpace Ω) (n : MeasurableSpace Ω)
    (hm : ∀ i, m i ≤ mΩ) (hn : n ≤ mΩ)
    (hfactor : ∀ (K : Finset ι) (A : ι → Set Ω),
      (∀ i ∈ K, MeasurableSet[m i] (A i)) →
      ∀ B : Set Ω, MeasurableSet[n] B →
        μ ((⋂ i ∈ K, A i) ∩ B) = μ (⋂ i ∈ K, A i) * μ B) :
    Indep (⨆ i, m i) n μ := by
  let P := piiUnionInter (fun i => {A : Set Ω | MeasurableSet[m i] A}) univ
  have hP : IsPiSystem P :=
    isPiSystem_piiUnionInter _ (fun i => @isPiSystem_measurableSet Ω (m i)) univ
  have hgen : (⨆ i, m i) = generateFrom P := by
    simpa only [P, iSup_univ] using
      (generateFrom_piiUnionInter_measurableSet m univ).symm
  apply IndepSets.indep (iSup_le hm) hn hP
    (@isPiSystem_measurableSet Ω n) hgen generateFrom_measurableSet.symm
  apply (IndepSets_iff _ _ μ).mpr
  rintro A B ⟨K, _, sets, hsets, rfl⟩ hB
  exact hfactor K sets hsets B hB

variable {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
variable {β : Type*} [MeasurableSpace β]

/-- The finite measurable-coordinate cylinder as an event on the original sample space. -/
def cylinder (X : Ω → ∀ i, α i) (K : Finset ι) (A : ∀ i, Set (α i)) : Set Ω :=
  ⋂ i ∈ K, (fun ω => X ω i) ⁻¹' A i

theorem measurableSet_cylinder (X : Ω → ∀ i, α i) (hX : Measurable X)
    (K : Finset ι) (A : ∀ i, Set (α i)) (hA : ∀ i ∈ K, MeasurableSet (A i)) :
    MeasurableSet (cylinder X K A) :=
  K.measurableSet_biInter (fun i hi =>
    (hA i hi).preimage ((measurable_pi_apply i).comp hX))

omit mΩ in
/-- The full observation comap is exactly the supremum of its coordinate comaps. -/
theorem comap_pi_eq_iSup (X : Ω → ∀ i, α i) :
    MeasurableSpace.comap X inferInstance =
      ⨆ i, MeasurableSpace.comap (fun ω => X ω i) inferInstance := by
  simp only [MeasurableSpace.pi, comap_iSup, comap_comp, Function.comp_def]

/-- Factorization of all finite-coordinate cylinders against all future
measurable sets proves independence from the complete product-valued view. -/
theorem indepFun_of_cylinder_factorization [IsProbabilityMeasure μ]
    (X : Ω → ∀ i, α i) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    (hfactor : ∀ (K : Finset ι) (A : ∀ i, Set (α i)),
      (∀ i ∈ K, MeasurableSet (A i)) →
      ∀ B : Set β, MeasurableSet B →
        μ (cylinder X K A ∩ Y ⁻¹' B) = μ (cylinder X K A) * μ (Y ⁻¹' B)) :
    IndepFun X Y μ := by
  classical
  change Indep (MeasurableSpace.comap X inferInstance)
    (MeasurableSpace.comap Y inferInstance) μ
  rw [comap_pi_eq_iSup]
  apply indep_iSup_of_finite_intersections _ _
    (fun i => ((measurable_pi_apply i).comp hX).comap_le) hY.comap_le
  intro K sets hsets B hB
  have hrep : ∀ i, ∃ A : Set (α i), MeasurableSet A ∧
      (i ∈ K → (fun ω => X ω i) ⁻¹' A = sets i) := by
    intro i
    by_cases hi : i ∈ K
    · obtain ⟨A, hA, heq⟩ := (measurableSet_comap).mp (hsets i hi)
      exact ⟨A, hA, fun _ => heq⟩
    · exact ⟨univ, MeasurableSet.univ, fun h => (hi h).elim⟩
  choose A hA heq using hrep
  obtain ⟨C, hC, rfl⟩ := (measurableSet_comap).mp hB
  have hsets_eq : (⋂ i ∈ K, sets i) = cylinder X K A := by
    apply iInter_congr
    intro i
    apply iInter_congr
    intro hi
    exact (heq i hi).symm
  rw [hsets_eq]
  exact hfactor K A (fun i _ => hA i) C hC

end CarryingCapacity.CylinderIndependence
