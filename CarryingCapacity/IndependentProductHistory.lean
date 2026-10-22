import CarryingCapacity.CylinderIndependence
import Mathlib.Probability.ProductMeasure

/-!
# Independence of entire observation and future arrays

Under the actual infinite product probability law, independence between each
coordinate's observation and its future extends to independence of both full
product-valued arrays. The proof evaluates pairs of finite cylinders and then
uses both generating pi-systems. No countability assumption is needed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set MeasurableSpace
open scoped ENNReal

namespace CarryingCapacity.IndependentProductHistory

variable {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Exact two-cylinder factorization, using independence only where their
coordinate index sets overlap. -/
theorem infinitePi_pi_inter_pi
    (K L : Finset ι) (A B : ∀ i, Set (Ω i))
    (hA : ∀ i ∈ K, MeasurableSet (A i))
    (hB : ∀ i ∈ L, MeasurableSet (B i))
    (hlocal : ∀ i, i ∈ K → i ∈ L →
      μ i (A i ∩ B i) = μ i (A i) * μ i (B i)) :
    Measure.infinitePi μ (Set.pi K A ∩ Set.pi L B) =
      Measure.infinitePi μ (Set.pi K A) * Measure.infinitePi μ (Set.pi L B) := by
  classical
  let A' : ∀ i, Set (Ω i) := fun i => if i ∈ K then A i else univ
  let B' : ∀ i, Set (Ω i) := fun i => if i ∈ L then B i else univ
  have hA' : ∀ i, MeasurableSet (A' i) := by
    intro i
    by_cases hi : i ∈ K <;> simp only [A', hi, if_true, if_false]
    · exact hA i hi
    · exact MeasurableSet.univ
  have hB' : ∀ i, MeasurableSet (B' i) := by
    intro i
    by_cases hi : i ∈ L <;> simp only [B', hi, if_true, if_false]
    · exact hB i hi
    · exact MeasurableSet.univ
  have hset : Set.pi K A ∩ Set.pi L B =
      Set.pi (↑(K ∪ L) : Set ι) (fun i => A' i ∩ B' i) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_pi, Finset.mem_coe, Finset.mem_union,
      A', B']
    constructor
    · rintro ⟨h1, h2⟩ i hi
      constructor <;> split_ifs with h
      · exact h1 i h
      · trivial
      · exact h2 i h
      · trivial
    · intro h
      constructor
      · intro i hi
        simpa [hi] using (h i (Or.inl hi)).1
      · intro i hi
        simpa [hi] using (h i (Or.inr hi)).2
  have hfactor : ∀ i, μ i (A' i ∩ B' i) = μ i (A' i) * μ i (B' i) := by
    intro i
    by_cases hiK : i ∈ K <;> by_cases hiL : i ∈ L
    · simpa [A', B', hiK, hiL] using hlocal i hiK hiL
    all_goals simp [A', B', hiK, hiL]
  have hprodA : (∏ i ∈ K ∪ L, μ i (A' i)) = ∏ i ∈ K, μ i (A i) := by
    calc
      _ = ∏ i ∈ K, μ i (A' i) := (Finset.prod_subset Finset.subset_union_left
        (fun i _ hi => by simp [A', hi])).symm
      _ = _ := Finset.prod_congr rfl (fun i hi => by simp [A', hi])
  have hprodB : (∏ i ∈ K ∪ L, μ i (B' i)) = ∏ i ∈ L, μ i (B i) := by
    calc
      _ = ∏ i ∈ L, μ i (B' i) := (Finset.prod_subset Finset.subset_union_right
        (fun i _ hi => by simp [B', hi])).symm
      _ = _ := Finset.prod_congr rfl (fun i hi => by simp [B', hi])
  rw [hset, Measure.infinitePi_pi μ (fun i _ => (hA' i).inter (hB' i)),
    Measure.infinitePi_pi μ hA, Measure.infinitePi_pi μ hB]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, hprodA, hprodB]

variable {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

/-- Coordinatewise independent observations and futures give independence of
the entire two arrays under the actual infinite product sample law. -/
theorem indepFun_observations_futures
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (X : ∀ i, Ω i → α i) (hX : ∀ i, Measurable (X i))
    (Y : ∀ i, Ω i → β i) (hY : ∀ i, Measurable (Y i))
    (hlocal : ∀ i, IndepFun (X i) (Y i) (μ i)) :
    IndepFun (fun ω i => X i (ω i)) (fun ω i => Y i (ω i))
      (Measure.infinitePi μ) := by
  classical
  let m : ι → MeasurableSpace (∀ i, Ω i) := fun i =>
    MeasurableSpace.comap (fun ω => X i (ω i)) inferInstance
  let n : ι → MeasurableSpace (∀ i, Ω i) := fun i =>
    MeasurableSpace.comap (fun ω => Y i (ω i)) inferInstance
  let P := piiUnionInter
    (fun i => {A : Set (∀ i, Ω i) | MeasurableSet[m i] A}) univ
  let Q := piiUnionInter
    (fun i => {A : Set (∀ i, Ω i) | MeasurableSet[n i] A}) univ
  have hP : IsPiSystem P := isPiSystem_piiUnionInter _
    (fun i => @isPiSystem_measurableSet _ (m i)) univ
  have hQ : IsPiSystem Q := isPiSystem_piiUnionInter _
    (fun i => @isPiSystem_measurableSet _ (n i)) univ
  have hgenP : (⨆ i, m i) = MeasurableSpace.generateFrom P := by
    simpa only [P, iSup_univ] using
      (generateFrom_piiUnionInter_measurableSet m univ).symm
  have hgenQ : (⨆ i, n i) = MeasurableSpace.generateFrom Q := by
    simpa only [Q, iSup_univ] using
      (generateFrom_piiUnionInter_measurableSet n univ).symm
  change Indep (MeasurableSpace.comap (fun (ω : ∀ i, Ω i) i => X i (ω i)) inferInstance)
    (MeasurableSpace.comap (fun (ω : ∀ i, Ω i) i => Y i (ω i)) inferInstance) _
  rw [CylinderIndependence.comap_pi_eq_iSup, CylinderIndependence.comap_pi_eq_iSup]
  apply IndepSets.indep
    (iSup_le (fun i => ((hX i).comp (measurable_pi_apply i)).comap_le))
    (iSup_le (fun i => ((hY i).comp (measurable_pi_apply i)).comap_le))
    hP hQ hgenP hgenQ
  apply (IndepSets_iff _ _ _).mpr
  rintro S T ⟨K, _, sets, hsets, rfl⟩ ⟨L, _, other, hother, rfl⟩
  have hrepA : ∀ i, ∃ A : Set (α i), MeasurableSet A ∧
      (i ∈ K → (fun ω => X i (ω i)) ⁻¹' A = sets i) := by
    intro i
    by_cases hi : i ∈ K
    · obtain ⟨A, hA, heq⟩ := measurableSet_comap.mp (hsets i hi)
      exact ⟨A, hA, fun _ => heq⟩
    · exact ⟨univ, MeasurableSet.univ, fun h => (hi h).elim⟩
  have hrepB : ∀ i, ∃ B : Set (β i), MeasurableSet B ∧
      (i ∈ L → (fun ω => Y i (ω i)) ⁻¹' B = other i) := by
    intro i
    by_cases hi : i ∈ L
    · obtain ⟨B, hB, heq⟩ := measurableSet_comap.mp (hother i hi)
      exact ⟨B, hB, fun _ => heq⟩
    · exact ⟨univ, MeasurableSet.univ, fun h => (hi h).elim⟩
  choose A hA heqA using hrepA
  choose B hB heqB using hrepB
  have hsetA : (⋂ i ∈ K, sets i) = Set.pi K (fun i => (X i) ⁻¹' A i) := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_pi, Finset.mem_coe, Set.mem_preimage]
    constructor
    · intro h i hi
      exact (Set.ext_iff.mp (heqA i hi) ω).mpr (h i hi)
    · intro h i hi
      exact (Set.ext_iff.mp (heqA i hi) ω).mp (h i hi)
  have hsetB : (⋂ i ∈ L, other i) = Set.pi L (fun i => (Y i) ⁻¹' B i) := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_pi, Finset.mem_coe, Set.mem_preimage]
    constructor
    · intro h i hi
      exact (Set.ext_iff.mp (heqB i hi) ω).mpr (h i hi)
    · intro h i hi
      exact (Set.ext_iff.mp (heqB i hi) ω).mp (h i hi)
  rw [hsetA, hsetB]
  exact infinitePi_pi_inter_pi μ K L _ _
    (fun i _ => (hA i).preimage (hX i)) (fun i _ => (hB i).preimage (hY i))
    (fun i _ _ => (hlocal i).measure_inter_preimage_eq_mul _ _ (hA i) (hB i))

end CarryingCapacity.IndependentProductHistory
