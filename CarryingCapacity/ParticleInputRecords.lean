import CarryingCapacity.ParticleNoiseProjection
import CarryingCapacity.CommonInitialNoise

/-!
# Exact independent particle input records

A measurable array extracted from an arbitrary initial record may have an iid
marginal while retaining dependence with the rest of that record. Pairing this
array with the corresponding disjoint blocks of the actual parent marked
noise gives exactly a product of the single-particle initial/noise laws.
Independence of the particle records is derived from this full array law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal

namespace CarryingCapacity.ParticleInputRecords
open CommonInitialNoise

variable {A E I J : Type*} [MeasurableSpace A] [MeasurableSpace E]

/-- The actual input for particle `i`: its extracted initial state and its
complete projected marked-noise sample. -/
def record (initial : A → I → E) (i : I) (p : Sample A (I × J)) : Sample E J :=
  (initial p.1 i, ParticleNoiseProjection.project i p.2)

/-- Measurability of an actual particle input, with no countability restriction
on the state or noise-label spaces. -/
theorem measurable_record (initial : A → I → E) (hInitial : Measurable initial) (i : I) :
    Measurable (record (J := J) initial i) :=
  ((measurable_pi_apply i).comp (hInitial.comp measurable_fst)).prodMk
    ((ParticleNoiseProjection.measurable_project i).comp measurable_snd)

/-- The full input record is measurable in the corresponding raw history.
The initial state is known at zero; the projected noise reveals only past arrivals. -/
theorem measurable_record_at (initial : A → I → E) (hInitial : Measurable initial)
    (i : I) (t : ℝ) :
    @Measurable (Sample A (I × J)) (Sample E J)
      (filtration A (I × J) t) (filtration E J t) (record initial i) := by
  have hfirst : Measurable[filtration A (I × J) t]
      (fun p : Sample A (I × J) => initial p.1 i) :=
    (measurable_pi_apply i).comp (hInitial.comp (measurable_initial_at t))
  have hsecond : @Measurable (Sample A (I × J)) (MarkedNoise.Sample J)
      (filtration A (I × J) t) (CommonNoiseFiltration.filtration J t)
      (fun p => ParticleNoiseProjection.project i p.2) :=
    (ParticleNoiseProjection.measurable_project_at i t).comp (measurable_noise_at t)
  exact hfirst.prodMk hsecond

variable [Fintype I]

/-- Coordinate projection from a finite iid array retains its prescribed law. -/
theorem pi_coordinate_map (ν : Measure E) [IsProbabilityMeasure ν] (i : I) :
    (Measure.pi (fun _ : I => ν)).map (fun a => a i) = ν := by
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  have he : (fun a : I → E => a i) ⁻¹' s =
      Set.pi Set.univ (Function.update (fun _ : I => Set.univ) i s) := by
    ext a
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro ha k
      by_cases hk : k = i
      · subst k
        simpa using ha
      · simp [Function.update_of_ne hk]
    · intro ha
      simpa using ha i
  rw [he, Measure.pi_pi]
  simp [Function.update, apply_ite]

/-- Exact full joint law of all actual particle input records. Only the
extracted initial array has an iid marginal; the rest of the initial record
is unrestricted. Independence from the noise comes from the actual product law. -/
theorem array_map (γ : Measure A) [IsProbabilityMeasure γ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (initial : A → I → E) (hInitial : Measurable initial)
    (hright : γ.map initial = Measure.pi (fun _ : I => ν)) :
    (law γ (I × J)).map (fun p i => record initial i p) =
      Measure.pi (fun _ : I => law ν J) := by
  let noiseArray : MarkedNoise.Sample (I × J) → I → MarkedNoise.Sample J :=
    fun ω i => ParticleNoiseProjection.project i ω
  have hm : Measurable noiseArray := measurable_pi_lambda _
    (fun i => ParticleNoiseProjection.measurable_project i)
  let split : Sample A (I × J) → (I → E) × (I → MarkedNoise.Sample J) :=
    Prod.map initial noiseArray
  have hs : Measurable split := hInitial.prodMap hm
  have he : (law γ (I × J)).map split =
      (Measure.pi (fun _ : I => ν)).prod (Measure.pi (fun _ : I => MarkedNoise.law J)) := by
    change (γ.prod (MarkedNoise.law (I × J))).map (Prod.map initial noiseArray) = _
    rw [← Measure.map_prod_map γ (MarkedNoise.law (I × J)) hInitial hm, hright]
    rw [show (MarkedNoise.law (I × J)).map noiseArray =
      Measure.pi (fun _ : I => MarkedNoise.law J) from ParticleNoiseProjection.array_map]
  let e := MeasurableEquiv.arrowProdEquivProdArrow E (MarkedNoise.Sample J) I
  change (law γ (I × J)).map (e.symm ∘ split) = _
  rw [← Measure.map_map e.symm.measurable hs, he]
  exact (MeasurePreserving.symm e
    (measurePreserving_arrowProdEquivProdArrow E (MarkedNoise.Sample J) I
      (fun _ => ν) (fun _ => MarkedNoise.law J))).map_eq

/-- Each actual particle record has exactly the single-particle initial/noise law. -/
theorem record_map (γ : Measure A) [IsProbabilityMeasure γ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (initial : A → I → E) (hInitial : Measurable initial)
    (hright : γ.map initial = Measure.pi (fun _ : I => ν)) (i : I) :
    (law γ (I × J)).map (record initial i) = law ν J := by
  have hm : Measurable (fun p : Sample A (I × J) => fun k => record initial k p) :=
    measurable_pi_lambda _ (measurable_record initial hInitial)
  calc
    _ = ((law γ (I × J)).map (fun p k => record initial k p)).map (fun a => a i) :=
      (Measure.map_map (measurable_pi_apply i) hm).symm
    _ = _ := by
      rw [array_map γ ν initial hInitial hright, pi_coordinate_map]

/-- Whole particle inputs are mutually independent, not merely pairwise
independent or independent at selected times. -/
theorem independent_records (γ : Measure A) [IsProbabilityMeasure γ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (initial : A → I → E) (hInitial : Measurable initial)
    (hright : γ.map initial = Measure.pi (fun _ : I => ν)) :
    iIndepFun (record (J := J) initial) (law γ (I × J)) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_record initial hInitial i).aemeasurable)).mpr
  simp_rw [record_map γ ν initial hInitial hright]
  exact array_map γ ν initial hInitial hright

section PairedInitialArray

variable {N : ℕ}

/-- The right states of a coupled initial array, retaining the full paired
array as the actual initial record. -/
def pairedRight (a : Fin N → E × E) (i : Fin N) : E := (a i).2

theorem measurable_pairedRight : Measurable (pairedRight (N := N) (E := E)) :=
  measurable_pi_lambda _ (fun i => (measurable_pi_apply i).snd)

/-- Concrete initialization bridge for a coupled array with iid right marginal. -/
theorem paired_array_map (γ : Measure (Fin N → E × E)) [IsProbabilityMeasure γ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hright : γ.map pairedRight = Measure.pi (fun _ : Fin N => ν)) :
    (law γ (Fin N × J)).map (fun p i => ((p.1 i).2, ParticleNoiseProjection.project i p.2)) =
      Measure.pi (fun _ : Fin N => law ν J) :=
  array_map γ ν pairedRight measurable_pairedRight hright

/-- Each right-particle input has its exact initial/noise law even when the
left initial array is dependent on the full right initial array. -/
theorem paired_record_map (γ : Measure (Fin N → E × E)) [IsProbabilityMeasure γ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hright : γ.map pairedRight = Measure.pi (fun _ : Fin N => ν)) (i : Fin N) :
    (law γ (Fin N × J)).map (fun p => ((p.1 i).2, ParticleNoiseProjection.project i p.2)) =
      law ν J := record_map γ ν pairedRight measurable_pairedRight hright i

/-- Full joint independence of the concrete coupled-array right-particle inputs. -/
theorem paired_independent_records (γ : Measure (Fin N → E × E)) [IsProbabilityMeasure γ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hright : γ.map pairedRight = Measure.pi (fun _ : Fin N => ν)) :
    iIndepFun (fun i p => ((p.1 i).2, ParticleNoiseProjection.project i p.2)) (law γ (Fin N × J)) :=
  independent_records γ ν pairedRight measurable_pairedRight hright

end PairedInitialArray
end CarryingCapacity.ParticleInputRecords
