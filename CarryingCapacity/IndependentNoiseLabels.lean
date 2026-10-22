import CarryingCapacity.MarkedPoissonMeasure
import CarryingCapacity.CylinderIndependence

/-!
# Independence of complete marked counting measures across labels

The actual independent strip records can be grouped by label. The resulting
entire label records, and hence their random counting measures, are jointly
independent. The grouping argument uses disjoint coordinate sigma algebras;
it does not infer joint independence from pairwise independence.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set MeasurableSpace
open scoped ENNReal NNReal BigOperators

namespace CarryingCapacity.IndependentNoiseLabels

/-- Grouping a jointly independent family of sigma algebras into disjoint
coordinate sets preserves joint independence of the complete groups. -/
theorem iIndep_grouped {Ω κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    (m : κ → MeasurableSpace Ω) (hm : ∀ k, m k ≤ mΩ) (hi : iIndep m μ)
    (G : ι → Set κ) (hG : Pairwise (fun i j => Disjoint (G i) (G j))) :
    iIndep (fun i => ⨆ k ∈ G i, m k) μ := by
  classical
  letI : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  apply (iIndep_iff _ _).mpr
  intro K f hf
  induction K using Finset.induction_on with
  | empty => simp
  | @insert a K ha ih =>
    have hdis : Disjoint (G a) (⋃ i ∈ K, G i) := by
      apply Set.disjoint_left.mpr
      intro k hka hk
      obtain ⟨i, hiK, hki⟩ := mem_iUnion₂.mp hk
      have hai : a ≠ i := by
        intro he
        subst i
        exact ha hiK
      exact Set.disjoint_left.mp (hG hai) hka hki
    have hind := indep_iSup_of_disjoint hm hi hdis
    have hfa := hf a (Finset.mem_insert_self a K)
    have hrest : MeasurableSet[⨆ k ∈ ⋃ i ∈ K, G i, m k] (⋂ i ∈ K, f i) := by
      apply K.measurableSet_biInter
      intro i hiK
      have hle : (⨆ k ∈ G i, m k) ≤ (⨆ k ∈ ⋃ l ∈ K, G l, m k) := by
        apply iSup_le
        intro k
        apply iSup_le
        intro hk
        exact le_iSup_of_le k (le_iSup_of_le (mem_iUnion₂.mpr ⟨i, hiK, hk⟩) le_rfl)
      exact hle _ (hf i (Finset.mem_insert_of_mem hiK))
    have he := (hind.indepSet_of_measurableSet hfa hrest).measure_inter_eq_mul
    rw [Finset.set_biInter_insert, Finset.prod_insert ha, he,
      ih (fun i hiK => hf i (Finset.mem_insert_of_mem hiK))]

open MarkedNoise MarkedIntensity MarkedSetCounts MarkedSetPoissonLimit

variable (J : Type*)

/-- The complete clock/mark record of a label, including every vertical strip. -/
def labelRecord (j : J) (ω : Sample J) : ℕ → StripSample := fun n => ω (j, n)

theorem measurable_labelRecord (j : J) : Measurable (labelRecord J j) :=
  measurable_pi_lambda _ (fun n => measurable_pi_apply (j, n))

/-- Independence of the entire label records under the original common-noise law. -/
theorem independent_labelRecords : iIndepFun (labelRecord J) (law J) := by
  let m : J × ℕ → MeasurableSpace (Sample J) :=
    fun p => MeasurableSpace.comap (fun ω => ω p) inferInstance
  have hG : Pairwise (fun i j : J => Disjoint {p : J × ℕ | p.1 = i} {p | p.1 = j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun p hi hj => hij (hi.symm.trans hj))
  have h := iIndep_grouped m (fun p => (measurable_pi_apply p).comap_le)
    (independent_strips J) (fun j => {p : J × ℕ | p.1 = j}) hG
  have he (j : J) : (⨆ p ∈ {p : J × ℕ | p.1 = j}, m p) =
      MeasurableSpace.comap (labelRecord J j) inferInstance := by
    rw [CylinderIndependence.comap_pi_eq_iSup]
    apply le_antisymm
    · apply iSup_le
      rintro ⟨i, n⟩
      apply iSup_le
      intro hp
      change i = j at hp
      subst i
      exact le_iSup (fun n => MeasurableSpace.comap (fun ω => labelRecord J j ω n) inferInstance) n
    · apply iSup_le
      intro n
      exact le_iSup_of_le (j, n) (le_iSup_of_le rfl le_rfl)
  simpa only [he] using h

/-- Entire random counting measures, not only selected counts, are independent
across noise labels. No countability assumption on the label type is needed. -/
theorem independent_countingMeasures : iIndepFun (countingMeasure : J → Sample J → _) (law J) := by
  let assemble : (ℕ → StripSample) → Sample Unit := fun z p => z p.2
  have hm : Measurable assemble := measurable_pi_lambda _ (fun p => measurable_pi_apply p.2)
  have h := (independent_labelRecords J).comp
    (fun _ z => countingMeasure () (assemble z))
    (fun _ => (measurable_countingMeasure ()).comp hm)
  simpa only [Function.comp_def, countingMeasure, point, assemble, labelRecord] using h

/-- Arbitrary measurable-set evaluations of distinct labels are independent,
without finite-intensity or disjointness restrictions across labels. -/
theorem independent_setMasses (S : J → Set (ℝ × ℝ)) (hS : ∀ j, MeasurableSet (S j)) :
    iIndepFun (fun j ω => countingMeasure j ω (S j)) (law J) := by
  exact (independent_countingMeasures J).comp (fun j ν => ν (S j))
    (fun j => Measure.measurable_coe (hS j))

variable {J} {L ι : Type*} [Fintype L] [Fintype ι]

/-- Full joint law across finitely many distinct labels and, within each label,
arbitrary disjoint measurable finite-intensity sets. Different labels may use
overlapping planar sets. The nested product is independence of all entries. -/
theorem countArrays_map (labels : L → J) (hlabels : Function.Injective labels)
    (S : L → ι → Set (ℝ × ℝ)) (hS : ∀ l i, MeasurableSet (S l i))
    (hdis : ∀ l, Pairwise (fun i k => Disjoint (S l i) (S l k)))
    (hfin : ∀ l i, (positiveVolume.prod positiveVolume) (S l i) ≠ ∞) :
    Measure.map (fun ω : Sample J => fun l i => count (labels l) (S l i) ω) (law J) =
      Measure.pi (fun l => Measure.pi (fun i => poissonMeasure (setRate (S l i)))) := by
  have hi := ((independent_countingMeasures J).precomp hlabels).comp
    (fun l ν => fun i => ⌊(ν (S l i)).toReal⌋₊)
    (fun l => measurable_pi_lambda _ (fun i =>
      ((Measure.measurable_coe (hS l i)).ennreal_toReal).nat_floor))
  have hm (l : L) : Measurable (fun ω : Sample J => fun i => count (labels l) (S l i) ω) :=
    measurable_pi_lambda _ (fun i => measurable_count (labels l) (S l i) (hS l i))
  have he := (iIndepFun_iff_map_fun_eq_pi_map (fun l => (hm l).aemeasurable)).mp hi
  simpa only [MarkedPoissonMeasure.countVector_map _ _ (hS _) (hdis _) (hfin _)] using he

end CarryingCapacity.IndependentNoiseLabels
