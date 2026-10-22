import CarryingCapacity.CommonFrozenStopping

/-!
# An arbitrary initial law independent of the common marked noise

The actual product probability space contains an initial record with its
prescribed full law and an independent copy of the full marked-noise sample.
Its filtration contains the initial record and only the arrived noise history.
A measurable map from the initial record to the process state allows a paired
initial array to be used directly, including either marginal projection.

The actual shared-noise frozen paths are jointly measurable, adapted, and
almost surely cadlag on this product space. Pathwise first-exit compatibility
also lifts. This file does not identify a compensator or assert a stopping-time
property for the product filtration's first exits.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Classical ENNReal Topology

namespace CarryingCapacity.CommonInitialNoise

/-- A whole initial record and an independent marked-noise sample. -/
abbrev Sample (A J : Type*) := A × MarkedNoise.Sample J

variable {A J : Type*} [MeasurableSpace A]

/-- The actual probability law, with independence supplied by its construction. -/
def law (μ : Measure A) (J : Type*) : Measure (Sample A J) :=
  μ.prod (MarkedNoise.law J)

instance law_probability (μ : Measure A) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (law μ J) := inferInstanceAs
      (IsProbabilityMeasure (μ.prod (MarkedNoise.law J)))

/-- The entire original initial record retains its prescribed law. -/
theorem map_initial (μ : Measure A) [IsProbabilityMeasure μ] :
    (law μ J).map Prod.fst = μ := by
  rw [law, Measure.map_fst_prod, measure_univ, one_smul]

/-- The entire noise coordinate retains the constructed marked-noise law. -/
theorem map_noise (μ : Measure A) [IsProbabilityMeasure μ] :
    (law μ J).map Prod.snd = MarkedNoise.law J := by
  rw [law, Measure.map_snd_prod, measure_univ, one_smul]

/-- The complete initial record is independent of the complete noise sample,
not just of an individual future mark or coordinate. -/
theorem independent_initial_noise (μ : Measure A) [IsProbabilityMeasure μ] :
    IndepFun (Prod.fst : Sample A J → A) Prod.snd (law μ J) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
    measurable_snd.aemeasurable).mpr
  rw [map_initial, map_noise]
  change (law μ J).map id = law μ J
  exact Measure.map_id

/-- Any measurable state extracted from the initial record is independent of
the entire future noise sample. This includes either projection of a paired array. -/
theorem independent_mapped_initial_noise {E : Type*} [MeasurableSpace E]
    (μ : Measure A) [IsProbabilityMeasure μ] (initial : A → E) (hi : Measurable initial) :
    IndepFun (fun p : Sample A J => initial p.1) Prod.snd (law μ J) :=
  (independent_initial_noise μ).comp hi (measurable_id : Measurable (id : MarkedNoise.Sample J → _))

/-- Every almost-sure property of the original noise lifts to the actual
product sample, without needing measurability of the property itself. -/
theorem ae_noise (μ : Measure A) {P : MarkedNoise.Sample J → Prop}
    (hP : ∀ᵐ ω ∂MarkedNoise.law J, P ω) : ∀ᵐ p ∂law μ J, P p.2 :=
  Measure.quasiMeasurePreserving_snd.ae hP

/-- At time `t`, the initial record is known and the noise coordinate reveals
exactly its raw history. This filtration is independent of the chosen process. -/
def filtration (A J : Type*) [MeasurableSpace A] :
    Filtration ℝ (inferInstance : MeasurableSpace (Sample A J)) where
  seq t := (inferInstance : MeasurableSpace A).prod (CommonNoiseFiltration.filtration J t)
  mono' := by
    intro s t hst
    exact sup_le_sup le_rfl (MeasurableSpace.comap_mono
      ((CommonNoiseFiltration.filtration J).mono hst))
  le' t := sup_le_sup le_rfl (MeasurableSpace.comap_mono
    ((CommonNoiseFiltration.filtration J).le t))

/-- The entire initial record is measurable at time zero and at every time. -/
theorem measurable_initial_at (t : ℝ) :
    Measurable[filtration A J t] (Prod.fst : Sample A J → A) :=
  @measurable_fst A (MarkedNoise.Sample J) _ (CommonNoiseFiltration.filtration J t)

/-- The lifted noise coordinate is measurable into its raw history sigma algebra. -/
theorem measurable_noise_at (t : ℝ) :
    @Measurable (Sample A J) (MarkedNoise.Sample J) (filtration A J t)
      (CommonNoiseFiltration.filtration J t) Prod.snd :=
  @measurable_snd A (MarkedNoise.Sample J) _ (CommonNoiseFiltration.filtration J t)

/-- The arrived labelled marks are visible in the initial-plus-noise filtration. -/
theorem measurable_view_at (t : ℝ) :
    Measurable[filtration A J t]
      (fun p : Sample A J => CommonNoiseFiltration.view t p.2) :=
  (CommonNoiseFiltration.measurable_view_at t).comp (measurable_noise_at t)

section Process

variable {E : Type*} [DecidableEq E]
  (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)
  (initial : A → E)

/-- The actual frozen path initialized from the product's first coordinate. -/
def process (C : ℝ) (p : Sample A J) (t : ℝ) : E :=
  CommonFrozenProcess.process active jump rate C (initial p.1) p.2 t

/-- Its genuine first exit, with infinity if the path never leaves. -/
def firstExit (C : ℝ) (p : Sample A J) : ℝ≥0∞ :=
  CommonFrozenExit.firstExit active jump rate C (initial p.1) p.2

variable [Fintype J]

omit [MeasurableSpace A] in
/-- Every sample path stays in its finite one-jump enlargement together with
its initial state, including initial records whose state lies outside `active`. -/
theorem process_mem_or_eq_initial (C : ℝ) (p : Sample A J) (t : ℝ) :
    process active jump rate initial C p t ∈ Freezing.oneStepEnlargement active jump ∨
      process active jump rate initial C p t = initial p.1 :=
  CommonFrozenProcess.process_mem_or_eq_initial active jump rate C (initial p.1) p.2 t

/-- The actual prescribed initial value holds simultaneously for all cutoffs. -/
theorem ae_process_zero (μ : Measure A) : ∀ᵐ p ∂law μ J, ∀ C,
    process active jump rate initial C p 0 = initial p.1 := by
  filter_upwards [ae_noise μ (CommonFrozenRegularity.ae_process_zero active jump rate)] with p hp
  exact fun C => hp C (initial p.1)

/-- A positive interval of the initialized path is constant at its initial state. -/
theorem ae_process_initial_interval (μ : Measure A) : ∀ᵐ p ∂law μ J, ∀ C,
    ∃ δ > 0, ∀ t ∈ Ico 0 δ, process active jump rate initial C p t = initial p.1 := by
  filter_upwards [ae_noise μ (CommonFrozenRegularity.ae_process_initial_interval active jump rate)]
    with p hp
  exact fun C => hp C (initial p.1)

/-- Cadlag regularity is derived for the actual independently initialized path. -/
theorem ae_process_cadlag [TopologicalSpace E] (μ : Measure A) : ∀ᵐ p ∂law μ J, ∀ C,
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (process active jump rate initial C p) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : E,
      Tendsto (process active jump rate initial C p) (nhdsWithin t (Iio t)) (nhds y)) := by
  filter_upwards [ae_noise μ (CommonFrozenRegularity.ae_process_cadlag active jump rate)] with p hp
  exact fun C => hp C (initial p.1)

/-- Permanent freezing survives the independent-initial-law extension. -/
theorem ae_process_frozen (μ : Measure A) : ∀ᵐ p ∂law μ J, ∀ C s t,
    s ≤ t → process active jump rate initial C p s ∉ active →
      process active jump rate initial C p t = process active jump rate initial C p s := by
  filter_upwards [ae_noise μ (CommonFrozenProcess.ae_process_frozen active jump rate)] with p hp
  exact fun C => hp C (initial p.1)

/-- Nested actual paths with the same independently sampled initial record
have ordered genuine exit times. -/
theorem ae_firstExit_mono (μ : Measure A) (large : Finset E) (hsets : active ⊆ large)
    (C₁ C₂ : ℝ) (h₁ : ∀ x ∈ active, ∀ j, rate j x ≤ C₁)
    (h₂ : ∀ x ∈ large, ∀ j, rate j x ≤ C₂) : ∀ᵐ p ∂law μ J,
    firstExit active jump rate initial C₁ p ≤ firstExit large jump rate initial C₂ p := by
  filter_upwards [ae_noise μ (CommonFrozenExit.ae_firstExit_mono
    active jump rate large hsets C₁ C₂ h₁ h₂)] with p hp
  exact hp (initial p.1)

/-- Stopping the larger initialized path at the smaller actual exit recovers
the smaller path, including the accepted exit jump. -/
theorem ae_stopped_nested (μ : Measure A) (large : Finset E) (hsets : active ⊆ large)
    (C₁ C₂ : ℝ) (h₁ : ∀ x ∈ active, ∀ j, rate j x ≤ C₁)
    (h₂ : ∀ x ∈ large, ∀ j, rate j x ≤ C₂) : ∀ᵐ p ∂law μ J, ∀ t, 0 ≤ t →
    CommonFrozenExit.stopped (firstExit active jump rate initial C₁ p)
      (process large jump rate initial C₂ p) t = process active jump rate initial C₁ p t := by
  filter_upwards [ae_noise μ (CommonFrozenExit.ae_stopped_nested
    active jump rate large hsets C₁ C₂ h₁ h₂)] with p hp
  exact hp (initial p.1)

section Measurability

variable [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  (hinit : Measurable initial)
include hinit

/-- The initialized process is jointly measurable in sample and time. -/
theorem measurable_process (C : ℝ) : Measurable
    (fun p : Sample A J × ℝ => process active jump rate initial C p.1 p.2) :=
  (CommonFrozenProcess.measurable_runBox active jump rate).comp
    ((measurable_fst.snd.prodMk (measurable_snd.prodMk measurable_const)).prodMk
      (hinit.comp measurable_fst.fst))

/-- Every evaluation is measurable in the actual initial-plus-noise history,
by reconstruction from the known initial state and the arrived point view. -/
theorem measurable_process_at (C t : ℝ) :
    Measurable[filtration A J t] (fun p => process active jump rate initial C p t) := by
  have h := (CommonNoiseFiltration.measurable_runObserved active jump rate t C).comp
    ((measurable_view_at t).prodMk (hinit.comp (measurable_initial_at t)))
  simpa only [Function.comp_def, process, CommonNoiseFiltration.process_eq_runObserved_view] using h

omit [Countable E] [MeasurableSingletonClass E] in
/-- The actual state at zero has exactly the pushed-forward initial law. -/
theorem process_zero_law (μ : Measure A) [IsProbabilityMeasure μ] (C : ℝ) :
    (law μ J).map (fun p => process active jump rate initial C p 0) = μ.map initial := by
  rw [Measure.map_congr ((ae_process_zero active jump rate initial μ).mono (fun _ h => h C))]
  change (law μ J).map (initial ∘ Prod.fst) = μ.map initial
  rw [← Measure.map_map hinit measurable_fst, map_initial]

omit hinit [Countable E] [MeasurableSingletonClass E] in
/-- For the identity initial map the prescribed full state law is retained. -/
theorem process_zero_law_id (μ : Measure E) [IsProbabilityMeasure μ] (C : ℝ) :
    (law μ J).map (fun p => process active jump rate id C p 0) = μ := by
  simpa only [Measure.map_id] using
    process_zero_law active jump rate id measurable_id μ C

/-- The initialized actual frozen process is adapted. No independence or
adaptedness conclusion is included as an input assumption. -/
theorem adapted_process [TopologicalSpace E] [PseudoMetrizableSpace E]
    [SecondCountableTopology E] [OpensMeasurableSpace E] (C : ℝ) :
    Adapted (filtration A J) (fun t p => process active jump rate initial C p t) :=
  fun t => (measurable_process_at active jump rate initial hinit C t).stronglyMeasurable

end Measurability
end Process

end CarryingCapacity.CommonInitialNoise
