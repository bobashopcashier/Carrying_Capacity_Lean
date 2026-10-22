import CarryingCapacity.MarkedNoiseReconstruction
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# A measurable decoder of the actual Poisson counting measures

A fixed countable generating family, intersected with bounded boxes, determines
any locally finite planar measure. On the actual canonical good event its mass
observations determine the complete clock/mark sample. Lusin--Souslin supplies
a measurable decoder, with a fixed fallback away from the good image. No extra
randomness or assumed hidden-record map is used.
-/

noncomputable section
open MeasureTheory MeasurableSpace Set Filter
open scoped Classical ENNReal

namespace CarryingCapacity.MarkedNoiseObservation
open MarkedNoise

/-- Finite intersections of one fixed countable Borel generator. -/
def basis (I : Finset ℕ) : Set (ℝ × ℝ) :=
  ⋂ i ∈ I, natGeneratingSequence (ℝ × ℝ) i

theorem measurableSet_basis (I : Finset ℕ) : MeasurableSet (basis I) :=
  I.measurableSet_biInter (fun i _ => measurableSet_natGeneratingSequence i)

@[simp] theorem basis_empty : basis ∅ = univ := by simp [basis]

@[simp] theorem basis_singleton (n : ℕ) : basis {n} = natGeneratingSequence (ℝ × ℝ) n := by
  simp [basis]

theorem basis_union (I K : Finset ℕ) : basis (I ∪ K) = basis I ∩ basis K := by
  ext x
  simp only [basis, mem_iInter, Finset.mem_union, mem_inter_iff]
  aesop

theorem isPiSystem_basis : IsPiSystem (range basis) := by
  rintro _ ⟨I,rfl⟩ _ ⟨K,rfl⟩ _
  exact ⟨I ∪ K, basis_union I K⟩

theorem generateFrom_basis : generateFrom (range basis) = (inferInstance : MeasurableSpace (ℝ × ℝ)) := by
  apply le_antisymm
  · apply generateFrom_le
    rintro _ ⟨I,rfl⟩
    exact measurableSet_basis I
  · rw [← generateFrom_natGeneratingSequence (ℝ × ℝ)]
    apply generateFrom_mono
    rintro _ ⟨n,rfl⟩
    exact ⟨{n}, basis_singleton n⟩

/-- The lower boxes exhaust the plane and are finite on every good noise sample. -/
def box (n : ℕ) : Set (ℝ × ℝ) := Iic (n : ℝ) ×ˢ Iic (n : ℝ)

theorem measurableSet_box (n : ℕ) : MeasurableSet (box n) :=
  measurableSet_Iic.prod measurableSet_Iic

theorem iUnion_box : ⋃ n, box n = univ := by
  apply eq_univ_of_forall
  intro x
  refine mem_iUnion.mpr ⟨Nat.ceil (max x.1 x.2), ?_, ?_⟩
  · change x.1 ≤ (Nat.ceil (max x.1 x.2) : ℝ)
    exact (le_max_left x.1 x.2).trans (Nat.le_ceil (max x.1 x.2))
  · change x.2 ≤ (Nat.ceil (max x.1 x.2) : ℝ)
    exact (le_max_right x.1 x.2).trans (Nat.le_ceil (max x.1 x.2))

/-- These countably many bounded mass observations determine a locally finite measure. -/
theorem measure_eq_of_observations (μ ν : Measure (ℝ × ℝ))
    (hfinite : ∀ n, μ (box n) ≠ ∞)
    (he : ∀ n I, μ (box n ∩ basis I) = ν (box n ∩ basis I)) : μ = ν := by
  apply Measure.ext_of_generateFrom_of_cover generateFrom_basis.symm (countable_range box)
    isPiSystem_basis (by simpa only [sUnion_range] using iUnion_box)
  · rintro _ ⟨n,rfl⟩
    exact hfinite n
  · rintro _ ⟨n,rfl⟩ _ ⟨I,rfl⟩
    simpa only [inter_comm] using he n I
  · rintro _ ⟨n,rfl⟩
    simpa using he n ∅

variable (J : Type*)

abbrev Observation := J × ℕ × Finset ℕ → ℝ≥0∞

/-- The decoder's input consists solely of measurable-set masses. -/
def observeMeasures (M : J → Measure (ℝ × ℝ)) : Observation J :=
  fun i => M i.1 (box i.2.1 ∩ basis i.2.2)

theorem measurable_observeMeasures : Measurable (observeMeasures J) :=
  measurable_pi_lambda _ (fun i =>
    (Measure.measurable_coe ((measurableSet_box _).inter (measurableSet_basis _))).comp
      (measurable_pi_apply i.1))

def observe (ω : Sample J) : Observation J := observeMeasures J (fun j => countingMeasure j ω)

theorem measurable_observe : Measurable (observe J) :=
  (measurable_observeMeasures J).comp (measurable_pi_lambda _ measurable_countingMeasure)

def Good (ω : Sample J) : Prop := MarkedNoiseReconstruction.Good ω ∧
  ∀ j n, countingMeasure j ω (box n) < ∞

theorem measurableSet_good [Countable J] : MeasurableSet {ω : Sample J | Good J ω} := by
  change MeasurableSet ({ω : Sample J | MarkedNoiseReconstruction.Good ω} ∩
    {ω | ∀ j n, countingMeasure j ω (box n) < ∞})
  refine MarkedNoiseReconstruction.measurableSet_good.inter ?_
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro n
  exact measurableSet_lt
    ((Measure.measurable_coe (measurableSet_box n)).comp (measurable_countingMeasure j))
    measurable_const

theorem ae_good [Countable J] : ∀ᵐ ω ∂law J, Good J ω := by
  filter_upwards [MarkedNoiseReconstruction.ae_good, ae_locally_finite_boxes (J := J)] with ω hω hf
  exact ⟨hω, fun j n => hf j n n⟩

theorem injective_observe : Set.InjOn (observe J) {ω | Good J ω} := by
  intro ω hω η hη he
  apply MarkedNoiseReconstruction.injective_countingMeasures hω.1 hη.1
  funext j
  apply measure_eq_of_observations _ _ (fun n => (hω.2 j n).ne)
  intro n I
  exact congrFun he (j,n,I)

/-- The measurable inverse is derived from actual injectivity on a Borel good
set in the canonical standard Borel sample space. -/
theorem exists_measurable_decoder [Countable J] :
    ∃ decode : Observation J → Sample J, Measurable decode ∧
      ∀ ω, Good J ω → decode (observe J ω) = ω := by
  let S := {ω : Sample J | Good J ω}
  letI : StandardBorelSpace S := (measurableSet_good J).standardBorel
  let f : S → Observation J := fun ω => observe J ω.1
  have hm : Measurable f := (measurable_observe J).comp measurable_subtype_coe
  have hi : Function.Injective f := by
    intro ω η he
    apply Subtype.ext
    exact injective_observe J ω.property η.property he
  obtain ⟨g,hg,he⟩ := (hm.measurableEmbedding hi).exists_measurable_extend
    (measurable_subtype_coe : Measurable (Subtype.val : S → Sample J))
    (fun _ => ⟨fun _ => (fun _ => 0, fun _ => 0)⟩)
  exact ⟨g,hg,fun ω hω => congrFun he ⟨ω,hω⟩⟩

/-- A fixed measurable function, with no extra random coordinate. -/
def decode [Countable J] : Observation J → Sample J :=
  (exists_measurable_decoder J).choose

theorem measurable_decode [Countable J] : Measurable (decode J) :=
  (exists_measurable_decoder J).choose_spec.1

theorem decode_observe [Countable J] (ω : Sample J) (hω : Good J ω) :
    decode J (observe J ω) = ω :=
  (exists_measurable_decoder J).choose_spec.2 ω hω

theorem ae_decode_observe [Countable J] : ∀ᵐ ω ∂law J, decode J (observe J ω) = ω :=
  (ae_good J).mono (fun ω hω => decode_observe J ω hω)

/-- Full canonical law is recovered from the actual observed counting measures. -/
theorem decode_observe_map [Countable J] :
    ((law J).map (observe J)).map (decode J) = law J := by
  rw [Measure.map_map (measurable_decode J) (measurable_observe J)]
  change (law J).map (fun ω => decode J (observe J ω)) = law J
  rw [Measure.map_congr (ae_decode_observe J)]
  exact Measure.map_id

/-- Almost every observation reconstructs a good sample and all its observed masses. -/
theorem ae_good_decode [Countable J] :
    ∀ᵐ y ∂(law J).map (observe J),
      Good J (decode J y) ∧ observe J (decode J y) = y := by
  apply (ae_map_iff (measurable_observe J).aemeasurable ?_).mpr
  · filter_upwards [ae_good J] with ω hω
    rw [decode_observe J ω hω]
    exact ⟨hω, rfl⟩
  · exact ((measurableSet_good J).preimage (measurable_decode J)).inter
      (measurableSet_eq_fun' ((measurable_observe J).comp (measurable_decode J)) measurable_id)

/-- Equality of the observable laws suffices to recover the canonical noise law. -/
theorem decode_map_of_observation_map [Countable J]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → Observation J) (hY : Measurable Y)
    (hlaw : P.map Y = (law J).map (observe J)) :
    P.map (fun ω => decode J (Y ω)) = law J := by
  change P.map (decode J ∘ Y) = law J
  rw [← Measure.map_map (measurable_decode J) hY, hlaw]
  exact decode_observe_map J

/-- The decoder recovers the actual supplied measures, not only their distribution.
Finiteness on bounded boxes is itself inherited from the observed law. -/
theorem ae_countingMeasure_decode_eq [Countable J]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → J → Measure (ℝ × ℝ)) (hM : Measurable M)
    (hlaw : P.map (fun ω => observeMeasures J (M ω)) = (law J).map (observe J)) :
    ∀ᵐ ω ∂P, ∀ j,
      countingMeasure j (decode J (observeMeasures J (M ω))) = M ω j := by
  have hgood : ∀ᵐ ω ∂P, Good J (decode J (observeMeasures J (M ω))) ∧
      observe J (decode J (observeMeasures J (M ω))) = observeMeasures J (M ω) := by
    have h := ae_good_decode J
    rw [← hlaw] at h
    exact ae_of_ae_map ((measurable_observeMeasures J).comp hM).aemeasurable h
  filter_upwards [hgood] with ω hω
  intro j
  apply measure_eq_of_observations _ _ (fun n => (hω.1.2 j n).ne)
  intro n I
  exact congrFun hω.2 (j,n,I)

end CarryingCapacity.MarkedNoiseObservation
