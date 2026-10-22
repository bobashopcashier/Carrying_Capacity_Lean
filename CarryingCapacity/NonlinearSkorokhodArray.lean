import CarryingCapacity.CanonicalSkorokhodPaths
import CarryingCapacity.AdaptedStateSpace
import CarryingCapacity.NonlinearParticleArray
import CarryingCapacity.ParticleInputRecords
import CarryingCapacity.CoupledPathLawConvergence

/-!
# Independent nonlinear vectors in the genuine J1 path space

The target is one path with values in a finite vector of adapted states, so all
coordinates use the same time change. Its Borel measurability is proved from
finite activity of the actual coordinate paths, not from a product-of-paths
measurability assertion. The comparison law comes from the exact joint law of
full particle input records.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal NNReal

namespace CarryingCapacity.NonlinearSkorokhodArray
open CommonInitialNoise ConfigurationLocalization SkorokhodJ1

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}

/-- The product of k full single-particle initial/noise input laws. -/
def inputLaw (ν : MomentLaw κ D) (k : ℕ) : Measure (Fin k → Sample (State D) (Jump D)) :=
  Measure.pi (fun _ => law ν.measure (Jump D))

instance inputLaw_probability (ν : MomentLaw κ D) (k : ℕ) : IsProbabilityMeasure (inputLaw ν k) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact ⟨by simp only [inputLaw, Measure.pi_univ, measure_univ, Finset.prod_const_one]⟩

theorem input_coordinate_preserving (ν : MomentLaw κ D) (k : ℕ) (i : Fin k) :
    MeasurePreserving (fun a : Fin k → Sample (State D) (Jump D) => a i)
      (inputLaw ν k) (law ν.measure (Jump D)) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  exact ⟨measurable_pi_apply i, ParticleInputRecords.pi_coordinate_map _ i⟩

variable (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ≥0) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)

/-- All coordinates are actual nonlinear realizations on their full records. -/
def rawVector (k : ℕ) (a : Fin k → Sample (State D) (Jump D)) (t : ℝ) : Configuration k D :=
  fun i => NonlinearFixedPoint.process control hActivity ν T T.coe_nonneg hCoupling hMoment (a i) t

theorem measurable_rawVector (k : ℕ) (t : ℝ) :
    Measurable (fun a => rawVector control hActivity ν T hCoupling hMoment k a t) :=
  measurable_pi_lambda _ (fun i =>
    (NonlinearFixedPoint.measurable_process control hActivity ν T T.coe_nonneg hCoupling hMoment
      |>.of_uncurry_right).comp (measurable_pi_apply i))

theorem ae_rawVector_cadlag (k : ℕ) : ∀ᵐ a ∂inputLaw ν k,
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt
      (rawVector control hActivity ν T hCoupling hMoment k a) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : Configuration k D, Tendsto
      (rawVector control hActivity ν T hCoupling hMoment k a) (𝓝[<] t) (𝓝 y)) := by
  have hc : ∀ᵐ a ∂inputLaw ν k, ∀ i : Fin k,
      (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt
        (NonlinearFixedPoint.process control hActivity ν T T.coe_nonneg hCoupling hMoment (a i)) (Ici t) t) ∧
      (∀ t : ℝ, 0 < t → ∃ y : State D, Tendsto
        (NonlinearFixedPoint.process control hActivity ν T T.coe_nonneg hCoupling hMoment (a i))
        (𝓝[<] t) (𝓝 y)) := by
    apply ae_all_iff.mpr
    intro i
    exact (input_coordinate_preserving ν k i).quasiMeasurePreserving.ae
      (NonlinearFixedPoint.ae_process_cadlag control hActivity ν T T.coe_nonneg hCoupling hMoment)
  filter_upwards [hc] with a ha
  constructor
  · intro t ht
    exact continuousWithinAt_pi.mpr (fun i => (ha i).1 t ht)
  · intro t ht
    choose y hy using fun i => (ha i).2 t ht
    exact ⟨y, tendsto_pi_nhds.mpr hy⟩

theorem ae_rawVector_finite_activity (k : ℕ) : ∀ᵐ a ∂inputLaw ν k,
    ∃ F : Finset ℝ, (∀ r ∈ F, r ∈ Ioc 0 (T : ℝ)) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        (∀ r ∈ F, r ∉ Ioc s t) →
        rawVector control hActivity ν T hCoupling hMoment k a s =
          rawVector control hActivity ν T hCoupling hMoment k a t := by
  have hc : ∀ᵐ a ∂inputLaw ν k, ∀ i : Fin k, ∃ F : Finset ℝ,
      (∀ r ∈ F, r ∈ Ioc 0 (T : ℝ)) ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        (∀ r ∈ F, r ∉ Ioc s t) →
          NonlinearFixedPoint.process control hActivity ν T T.coe_nonneg hCoupling hMoment (a i) s =
            NonlinearFixedPoint.process control hActivity ν T T.coe_nonneg hCoupling hMoment (a i) t := by
    apply ae_all_iff.mpr
    intro i
    exact (input_coordinate_preserving ν k i).quasiMeasurePreserving.ae
      (CanonicalSkorokhodPaths.ae_nonlinear_finite_activity control hActivity ν T hCoupling hMoment)
  filter_upwards [hc] with a ha
  choose F hF hconst using ha
  refine ⟨Finset.univ.biUnion F, ?_, ?_⟩
  · intro r hr
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hr
    exact hF i r hi
  · intro s t hs hst ht hno
    funext i
    exact hconst i s t hs hst ht (fun r hr => hno r (Finset.mem_biUnion.mpr ⟨i, by simp, hr⟩))

/-- The actual vector trajectory with one common J1 time change. -/
def path (k : ℕ) (a : Fin k → Sample (State D) (Jump D)) : Path T (Fin k → AdaptedState κ D) :=
  (realPathOrConst T 0 (rawVector control hActivity ν T hCoupling hMoment k a)).map
    (AdaptedState.piUniformEquiv κ D k).symm
    (AdaptedState.piUniformEquiv κ D k).symm.uniformContinuous.continuous

theorem aemeasurable_path (k : ℕ) :
    AEMeasurable (path control hActivity ν T hCoupling hMoment k) (inputLaw ν k) :=
  (measurable_path_map (AdaptedState.piUniformEquiv κ D k).symm
    (AdaptedState.piUniformEquiv κ D k).symm.uniformContinuous).comp_aemeasurable
      (SkorokhodStepApproximation.aemeasurable_realPathOrConst (inputLaw ν k) T 0 _
        (measurable_rawVector control hActivity ν T hCoupling hMoment k)
        (ae_rawVector_cadlag control hActivity ν T hCoupling hMoment k)
        (ae_rawVector_finite_activity control hActivity ν T hCoupling hMoment k))

theorem ae_path_apply (k : ℕ) : ∀ᵐ a ∂inputLaw ν k, ∀ t : Time T, ∀ i : Fin k,
    path control hActivity ν T hCoupling hMoment k a t i =
      AdaptedState.ofState κ D (rawVector control hActivity ν T hCoupling hMoment k a t i) := by
  filter_upwards [ae_rawVector_cadlag control hActivity ν T hCoupling hMoment k] with a ha
  intro t i
  change (AdaptedState.piUniformEquiv κ D k).symm (realPathOrConst T 0
    (rawVector control hActivity ν T hCoupling hMoment k a) t) i = _
  rw [realPathOrConst_apply _ _ ha.1 ha.2]
  rfl

/-- The joint trajectory law of k independent nonlinear particles, in a single
vector-valued J1 space. -/
def pathLaw (k : ℕ) : ProbabilityMeasure (Path T (Fin k → AdaptedState κ D)) :=
  CoupledPathLawConvergence.imageLaw (inputLaw ν k)
    (path control hActivity ν T hCoupling hMoment k)
    (aemeasurable_path control hActivity ν T hCoupling hMoment k)

/-- One actual nonlinear path with the adapted state metric. -/
def singlePath (p : Sample (State D) (Jump D)) : Path T (AdaptedState κ D) :=
  (CanonicalSkorokhodPaths.nonlinearPath control hActivity ν T hCoupling hMoment p).map
    (AdaptedState.ofState κ D) (AdaptedState.uniformContinuous_ofState κ D).continuous

theorem aemeasurable_singlePath :
    AEMeasurable (singlePath control hActivity ν T hCoupling hMoment) (law ν.measure (Jump D)) :=
  (measurable_path_map (AdaptedState.ofState κ D) (AdaptedState.uniformContinuous_ofState κ D)).comp_aemeasurable
    (CanonicalSkorokhodPaths.aemeasurable_nonlinearPath control hActivity ν T hCoupling hMoment)

/-- Projection of the actual vector-valued path retains its full coordinate
trajectory, including both endpoints. -/
def coordinatePath (k : ℕ) (i : Fin k) (a : Fin k → Sample (State D) (Jump D)) :
    Path T (AdaptedState κ D) :=
  (path control hActivity ν T hCoupling hMoment k a).map (fun z => z i) (continuous_apply i)

theorem ae_coordinatePath_eq (k : ℕ) (i : Fin k) : ∀ᵐ a ∂inputLaw ν k,
    coordinatePath control hActivity ν T hCoupling hMoment k i a =
      singlePath control hActivity ν T hCoupling hMoment (a i) := by
  filter_upwards [ae_path_apply control hActivity ν T hCoupling hMoment k,
    (input_coordinate_preserving ν k i).quasiMeasurePreserving.ae
      (CanonicalSkorokhodPaths.ae_nonlinearPath_apply control hActivity ν T hCoupling hMoment)] with a ha hi
  apply SkorokhodJ1.Path.ext
  intro t
  change path control hActivity ν T hCoupling hMoment k a t i =
    AdaptedState.ofState κ D (CanonicalSkorokhodPaths.nonlinearPath control hActivity ν T hCoupling hMoment (a i) t)
  rw [ha t i, hi t]
  rfl

/-- The coordinate trajectories of the vector-valued J1 random path are
mutually independent as full paths, not only at selected times. -/
theorem independent_coordinatePaths (k : ℕ) :
    iIndepFun (coordinatePath control hActivity ν T hCoupling hMoment k) (inputLaw ν k) := by
  have hm (i : Fin k) := (input_coordinate_preserving ν k i).map_eq
  have hind : iIndepFun (fun i : Fin k => fun a : Fin k → Sample (State D) (Jump D) => a i)
      (inputLaw ν k) := by
    apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_apply i).aemeasurable)).mpr
    simp_rw [hm]
    exact Measure.map_id
  have hc := hind.comp₀ (fun _ => singlePath control hActivity ν T hCoupling hMoment)
    (fun i => (measurable_pi_apply i).aemeasurable)
    (fun i => by rw [hm i]; exact aemeasurable_singlePath control hActivity ν T hCoupling hMoment)
  exact hc.congr (fun i => (ae_coordinatePath_eq control hActivity ν T hCoupling hMoment k i).mono (fun _ ha => ha.symm))

/-- Every coordinate trajectory has exactly the same actual nonlinear path law. -/
theorem coordinatePath_map (k : ℕ) (i : Fin k) :
    (inputLaw ν k).map (coordinatePath control hActivity ν T hCoupling hMoment k i) =
      (law ν.measure (Jump D)).map (singlePath control hActivity ν T hCoupling hMoment) := by
  have hp := input_coordinate_preserving ν k i
  have hm : AEMeasurable (singlePath control hActivity ν T hCoupling hMoment)
      ((inputLaw ν k).map (fun a => a i)) := by
    rw [hp.map_eq]
    exact aemeasurable_singlePath control hActivity ν T hCoupling hMoment
  rw [Measure.map_congr (ae_coordinatePath_eq control hActivity ν T hCoupling hMoment k i)]
  change (inputLaw ν k).map ((singlePath control hActivity ν T hCoupling hMoment) ∘ (fun a => a i)) = _
  rw [← AEMeasurable.map_map_of_aemeasurable hm hp.measurable.aemeasurable, hp.map_eq]

section Records
variable {A : Type*} [MeasurableSpace A] {N k : ℕ}

/-- The first k full input records, for a population containing k particles. -/
def selectedRecords (initial : A → Configuration N D) (hkn : k ≤ N)
    (p : Sample A (Label N D)) : Fin k → Sample (State D) (Jump D) :=
  fun i => ParticleInputRecords.record initial (Fin.castLE hkn i) p

theorem measurable_selectedRecords (initial : A → Configuration N D)
    (hinit : Measurable initial) (hkn : k ≤ N) : Measurable (selectedRecords initial hkn) :=
  measurable_pi_lambda _ (fun i => ParticleInputRecords.measurable_record initial hinit (Fin.castLE hkn i))

theorem selectedRecords_preserving (initial : A → Configuration N D)
    (hinit : Measurable initial) (γ : Measure A) [IsProbabilityMeasure γ]
    (hright : γ.map initial = Measure.pi (fun _ : Fin N => ν.measure)) (hkn : k ≤ N) :
    MeasurePreserving (selectedRecords initial hkn) (law γ (Label N D)) (inputLaw ν k) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  refine ⟨measurable_selectedRecords initial hinit hkn, ?_⟩
  have hind := (ParticleInputRecords.independent_records (J := Jump D) γ ν.measure initial hinit hright).precomp
    (Fin.castLE_injective hkn)
  change (law γ (Label N D)).map (fun p i => ParticleInputRecords.record initial (Fin.castLE hkn i) p) = _
  rw [(iIndepFun_iff_map_fun_eq_pi_map (fun i =>
    (ParticleInputRecords.measurable_record initial hinit (Fin.castLE hkn i)).aemeasurable)).mp hind]
  simp_rw [ParticleInputRecords.record_map γ ν.measure initial hinit hright]
  rfl

/-- First-k comparison paths, with a fixed zero path for the finitely many
population rows containing fewer than k particles. -/
def comparison (initial : A → Configuration N D) (k : ℕ)
    (p : Sample A (Label N D)) : Path T (Fin k → AdaptedState κ D) :=
  if hkn : k ≤ N then path control hActivity ν T hCoupling hMoment k (selectedRecords initial hkn p)
  else Path.const T (fun _ => AdaptedState.ofState κ D 0)

theorem aemeasurable_comparison (initial : A → Configuration N D)
    (hinit : Measurable initial) (γ : Measure A) [IsProbabilityMeasure γ]
    (hright : γ.map initial = Measure.pi (fun _ : Fin N => ν.measure)) (k : ℕ) :
    AEMeasurable (comparison control hActivity ν T hCoupling hMoment initial k) (law γ (Label N D)) := by
  change AEMeasurable (fun p => comparison control hActivity ν T hCoupling hMoment initial k p) _
  by_cases hkn : k ≤ N
  · simp only [comparison, dif_pos hkn]
    exact (aemeasurable_path control hActivity ν T hCoupling hMoment k).comp_quasiMeasurePreserving
      (selectedRecords_preserving ν initial hinit γ hright hkn).quasiMeasurePreserving
  · simp only [comparison, dif_neg hkn]
    exact aemeasurable_const

theorem comparison_map (initial : A → Configuration N D)
    (hinit : Measurable initial) (γ : Measure A) [IsProbabilityMeasure γ]
    (hright : γ.map initial = Measure.pi (fun _ : Fin N => ν.measure)) (hkn : k ≤ N) :
    (law γ (Label N D)).map (comparison control hActivity ν T hCoupling hMoment initial k) =
      (pathLaw control hActivity ν T hCoupling hMoment k).toMeasure := by
  have hp := selectedRecords_preserving ν initial hinit γ hright hkn
  have hm : AEMeasurable (path control hActivity ν T hCoupling hMoment k)
      ((law γ (Label N D)).map (selectedRecords initial hkn)) := by
    rw [hp.map_eq]
    exact aemeasurable_path control hActivity ν T hCoupling hMoment k
  change (law γ (Label N D)).map (fun p => comparison control hActivity ν T hCoupling hMoment initial k p) = _
  simp only [comparison, dif_pos hkn]
  change (law γ (Label N D)).map ((path control hActivity ν T hCoupling hMoment k) ∘
    selectedRecords initial hkn) = _
  rw [← AEMeasurable.map_map_of_aemeasurable hm hp.measurable.aemeasurable, hp.map_eq]
  rfl

theorem ae_comparison_apply (initial : A → Configuration N D)
    (hinit : Measurable initial) (γ : Measure A) [IsProbabilityMeasure γ]
    (hright : γ.map initial = Measure.pi (fun _ : Fin N => ν.measure)) (hkn : k ≤ N) :
    ∀ᵐ p ∂law γ (Label N D), ∀ t : Time T, ∀ i : Fin k,
      comparison control hActivity ν T hCoupling hMoment initial k p t i =
        AdaptedState.ofState κ D (NonlinearParticleArray.process control hActivity ν T T.coe_nonneg
          hCoupling hMoment initial (Fin.castLE hkn i) p t) := by
  have hp := (selectedRecords_preserving ν initial hinit γ hright hkn).quasiMeasurePreserving.ae
    (ae_path_apply control hActivity ν T hCoupling hMoment k)
  filter_upwards [hp] with p hp
  intro t i
  simpa only [comparison, dif_pos hkn, rawVector, selectedRecords,
    NonlinearParticleArray.process] using hp t i

end Records
end CarryingCapacity.NonlinearSkorokhodArray
