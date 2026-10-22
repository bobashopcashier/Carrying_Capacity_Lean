import CarryingCapacity.MarkedNoiseObservation
import CarryingCapacity.MarkedFullPoissonLaw

/-!
# The observed law of prescribed Poisson random measures

Finite disjoint-set count laws determine the full countable observation law.
Boolean atoms remove overlaps between observed sets, and uniqueness of
projective limits identifies the law of all observations. The hypotheses are
the finite-disjoint-count characterization of independent Poisson measures;
no map to hidden canonical clock records is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal BigOperators

namespace CarryingCapacity.PoissonObservationLaw
open MarkedNoiseObservation MarkedFullPoissonLaw MarkedIntensity

section Partition
variable {ι : Type} [Fintype ι]

/-- Membership patterns give disjoint atoms for a finite measurable family. -/
def atom (S : ι → Set (ℝ × ℝ)) (b : Finset ι) : Set (ℝ × ℝ) :=
  {x | ∀ i, x ∈ S i ↔ i ∈ b}

theorem measurableSet_atom (S : ι → Set (ℝ × ℝ)) (hS : ∀ i, MeasurableSet (S i))
    (b : Finset ι) : MeasurableSet (atom S b) := by
  simp only [atom, setOf_forall]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i ∈ b
  · simpa only [hi, iff_true] using hS i
  · simpa only [hi, iff_false] using (hS i).compl

omit [Fintype ι] in
theorem pairwise_disjoint_atom (S : ι → Set (ℝ × ℝ)) :
    Pairwise (fun b c : Finset ι => Disjoint (atom S b) (atom S c)) := by
  intro b c hbc
  apply Set.disjoint_left.mpr
  intro x hb hc
  apply hbc
  ext i
  exact (hb i).symm.trans (hc i)

theorem set_eq_atoms (S : ι → Set (ℝ × ℝ)) (i : ι) :
    S i = ⋃ b ∈ (Finset.univ.filter (fun b : Finset ι => i ∈ b)), atom S b := by
  ext x
  constructor
  · intro hx
    let b : Finset ι := Finset.univ.filter (fun k => x ∈ S k)
    apply mem_iUnion.mpr ⟨b, ?_⟩
    apply mem_iUnion.mpr
    refine ⟨by simpa only [Finset.mem_filter, Finset.mem_univ, true_and, b] using hx, ?_⟩
    intro k
    simp [b]
  · intro hx
    obtain ⟨b, hx⟩ := mem_iUnion.mp hx
    obtain ⟨hb, hx⟩ := mem_iUnion.mp hx
    exact (hx i).mpr (Finset.mem_filter.mp hb).2

theorem measure_eq_sum_atoms (μ : Measure (ℝ × ℝ)) (S : ι → Set (ℝ × ℝ))
    (hS : ∀ i, MeasurableSet (S i)) (i : ι) :
    μ (S i) = ∑ b : Finset ι, if i ∈ b then μ (atom S b) else 0 := by
  rw [set_eq_atoms S i,
    measure_biUnion_finset (fun b _ c _ hbc => pairwise_disjoint_atom S hbc)
      (fun b _ => measurableSet_atom S hS b), Finset.sum_filter]

end Partition

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
  (J : Type) [Fintype J] (M : J → Ω → Measure (ℝ × ℝ))

/-- The exact finite-array law of independent PRMs, with disjoint sets within
each label and with the paper's ds du intensity. -/
def HasDisjointLaws : Prop := ∀ (ι : Type) [Fintype ι] (S : J → ι → Set (ℝ × ℝ)),
  (∀ j i, MeasurableSet (S j i)) →
  (∀ j, Pairwise (fun i k => Disjoint (S j i) (S j k))) →
  P.map (fun ω => fun j i => M j ω (S j i)) =
    Measure.pi (fun j => Measure.pi
      (fun i => massLaw ((positiveVolume.prod positiveVolume) (S j i))))

/-- The actual constructed random measures satisfy the defining count laws. -/
theorem canonical_disjointLaws : HasDisjointLaws (MarkedNoise.law J) J
    (fun j ω => MarkedNoise.countingMeasure j ω) := by
  intro ι _ S hS hd
  exact MarkedFullPoissonLaw.countingMeasure_arrays_map id Function.injective_id S hS hd

/-- Standard independent-count and single-count hypotheses imply the finite-array
characterization, so it is not an extra observation-law assumption. -/
theorem disjointLaws_of_independent [IsProbabilityMeasure P] (hM : ∀ j, Measurable (M j))
    (hlabels : iIndepFun M P)
    (hcounts : ∀ (ι : Type) [Fintype ι] (j : J) (S : ι → Set (ℝ × ℝ)),
      (∀ i, MeasurableSet (S i)) → Pairwise (fun i k => Disjoint (S i) (S k)) →
      iIndepFun (fun i ω => M j ω (S i)) P)
    (hlaw : ∀ j S, MeasurableSet S →
      P.map (fun ω => M j ω S) = massLaw ((positiveVolume.prod positiveVolume) S)) :
    HasDisjointLaws P J M := by
  intro ι _ S hS hd
  have hm j : Measurable (fun ω => fun i => M j ω (S j i)) :=
    measurable_pi_lambda _ (fun i => (Measure.measurable_coe (hS j i)).comp (hM j))
  have hrow j : P.map (fun ω => fun i => M j ω (S j i)) =
      Measure.pi (fun i => massLaw ((positiveVolume.prod positiveVolume) (S j i))) := by
    have he := (iIndepFun_iff_map_fun_eq_pi_map (fun i =>
      ((Measure.measurable_coe (hS j i)).comp (hM j)).aemeasurable)).mp
        (hcounts ι j (S j) (hS j) (hd j))
    simpa only [Function.comp_def, hlaw _ _ (hS _ _)] using he
  have hi := hlabels.comp (fun j ν => fun i => ν (S j i))
    (fun j => measurable_pi_lambda _ (fun i => Measure.measurable_coe (hS j i)))
  have he := (iIndepFun_iff_map_fun_eq_pi_map (fun j => (hm j).aemeasurable)).mp hi
  simpa only [Function.comp_def, hrow] using he

/-- Restore an overlapping set's count by summing its disjoint atom counts. -/
def restore {ι : Type} [Fintype ι] (a : J → Finset ι → ℝ≥0∞) : J → ι → ℝ≥0∞ :=
  fun j i => ∑ b : Finset ι, if i ∈ b then a j b else 0

omit [Fintype J] in
theorem measurable_restore {ι : Type} [Fintype ι] : Measurable (restore J (ι := ι)) := by
  apply measurable_pi_lambda
  intro j
  apply measurable_pi_lambda
  intro i
  apply Finset.measurable_sum
  intro b _
  by_cases hi : i ∈ b
  · simpa only [hi, if_true] using (measurable_pi_apply b).comp (measurable_pi_apply j)
  · simpa only [hi, if_false] using (measurable_const : Measurable (fun _ : J → Finset ι → ℝ≥0∞ => (0 : ℝ≥0∞)))

/-- Equality of arbitrary finite count-array laws follows from disjoint laws,
even when the observed sets overlap or have infinite intensity. -/
theorem finite_array_map_eq (hM : ∀ j, Measurable (M j)) (hP : HasDisjointLaws P J M)
    {ι : Type} [Fintype ι] (S : J → ι → Set (ℝ × ℝ)) (hS : ∀ j i, MeasurableSet (S j i)) :
    P.map (fun ω => fun j i => M j ω (S j i)) =
      (MarkedNoise.law J).map (fun ω => fun j i => MarkedNoise.countingMeasure j ω (S j i)) := by
  let A : J → Finset ι → Set (ℝ × ℝ) := fun j => atom (S j)
  have ha j b : MeasurableSet (A j b) := measurableSet_atom (S j) (hS j) b
  have hd j : Pairwise (fun b c => Disjoint (A j b) (A j c)) := pairwise_disjoint_atom (S j)
  have he := (hP (Finset ι) A ha hd).trans (canonical_disjointLaws J (Finset ι) A ha hd).symm
  have he' := congrArg (Measure.map (restore J)) he
  have hm : Measurable (fun ω => fun j b => M j ω (A j b)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_lambda _ (fun b =>
      (Measure.measurable_coe (ha j b)).comp (hM j)))
  have hn : Measurable (fun ω => fun j b => MarkedNoise.countingMeasure j ω (A j b)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_lambda _ (fun b =>
      (Measure.measurable_coe (ha j b)).comp (MarkedNoise.measurable_countingMeasure j)))
  rw [Measure.map_map (measurable_restore J) hm,
    Measure.map_map (measurable_restore J) hn] at he'
  have hleft : restore J ∘ (fun ω => fun j b => M j ω (A j b)) =
      (fun ω => fun j i => M j ω (S j i)) := by
    funext ω j i
    exact (measure_eq_sum_atoms (M j ω) (S j) (hS j) i).symm
  have hright : restore J ∘ (fun ω => fun j b => MarkedNoise.countingMeasure j ω (A j b)) =
      (fun ω => fun j i => MarkedNoise.countingMeasure j ω (S j i)) := by
    funext ω j i
    exact (measure_eq_sum_atoms (MarkedNoise.countingMeasure j ω) (S j) (hS j) i).symm
  rw [hleft, hright] at he'
  exact he'

/-- The law of every bounded observation, jointly and without disjointness
restrictions, is determined by the standard Poisson laws. -/
theorem observation_map_eq [IsProbabilityMeasure P]
    (hM : ∀ j, Measurable (M j)) (hP : HasDisjointLaws P J M) :
    P.map (fun ω => observeMeasures J (fun j => M j ω)) =
      (MarkedNoise.law J).map (observe J) := by
  have hm : Measurable (fun ω => observeMeasures J (fun j => M j ω)) :=
    (measurable_observeMeasures J).comp (measurable_pi_lambda _ hM)
  let Q := (MarkedNoise.law J).map (observe J)
  haveI : IsProbabilityMeasure Q := isProbabilityMeasure_map (measurable_observe J).aemeasurable
  let R : ∀ I : Finset (J × ℕ × Finset ℕ), Measure (I → ℝ≥0∞) :=
    fun I => Q.map I.restrict
  haveI : ∀ I, IsProbabilityMeasure (R I) := fun I =>
    isProbabilityMeasure_map (measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)).aemeasurable
  apply MeasureTheory.IsProjectiveLimit.unique
    (α := fun _ : J × ℕ × Finset ℕ => ℝ≥0∞) (P := R) ?_ (fun _ => rfl)
  intro I
  let S : J → I → Set (ℝ × ℝ) := fun _ i => box i.val.2.1 ∩ basis i.val.2.2
  have hs j i : MeasurableSet (S j i) := (measurableSet_box _).inter (measurableSet_basis _)
  let select : (J → I → ℝ≥0∞) → I → ℝ≥0∞ := fun a i => a i.val.1 i
  have hselect : Measurable select :=
    measurable_pi_lambda _ (fun i => (measurable_pi_apply i).comp (measurable_pi_apply i.val.1))
  have he := congrArg (Measure.map select) (finite_array_map_eq P J M hM hP S hs)
  have hmArray : Measurable (fun ω => fun j i => M j ω (S j i)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_lambda _ (fun i =>
      (Measure.measurable_coe (hs j i)).comp (hM j)))
  have hnArray : Measurable (fun ω => fun j i => MarkedNoise.countingMeasure j ω (S j i)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_lambda _ (fun i =>
      (Measure.measurable_coe (hs j i)).comp (MarkedNoise.measurable_countingMeasure j)))
  rw [Measure.map_map hselect hmArray, Measure.map_map hselect hnArray] at he
  change (P.map (fun ω => observeMeasures J (fun j => M j ω))).map
      (fun x : Observation J => fun i : I => x i.val) =
    Q.map (fun x : Observation J => fun i : I => x i.val)
  have hproj : Measurable (fun x : Observation J => fun i : I => x i.val) :=
    measurable_pi_lambda _ (fun i : I => measurable_pi_apply i.val)
  rw [Measure.map_map hproj hm]
  dsimp only [Q]
  rw [Measure.map_map hproj (measurable_observe J)]
  exact he

end CarryingCapacity.PoissonObservationLaw
