import CarryingCapacity.GlobalFiniteSupportDrift

/-!
# Raw-history measurability of actual global time integrals

The global path up to T is reconstructed, on every sample, from the initial
record and the marked history at T. This gives joint terminal-history
measurability before integration. No completion or almost-sure modification
argument is used to obtain adaptedness of the current-state drift integral.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical Topology

namespace CarryingCapacity.GlobalHistoryIntegral
open CommonNoiseFiltration ChronologicalEvents

section Observed
variable {J E : Type*} [Countable J] [DecidableEq E] [Countable E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
  (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)

local instance : MeasurableSpace (Finset (Event J)) := ⊤
local instance : MeasurableSingletonClass (Finset (Event J)) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (List (Event J)) := ⊤
local instance : MeasurableSingletonClass (List (Event J)) := ⟨fun _ => trivial⟩

omit [Countable J] in
/-- The selected observed event set is measurable even when the horizon varies. -/
theorem measurable_observedSet_time (C : ℝ) : Measurable
    (fun p : EventView J × ℝ => observedSet p.2 C p.1) := by
  apply measurable_set_iff.mpr
  intro e
  apply measurable_to_prop
  rw [preimage_singleton_true]
  change MeasurableSet ({p : EventView J × ℝ | (p.1 e).1 ≤ p.2} ∩
    {p : EventView J × ℝ | (p.1 e).2 ≤ C})
  exact (measurableSet_le ((measurable_pi_apply e).comp measurable_fst).fst measurable_snd).inter
    (measurableSet_le ((measurable_pi_apply e).comp measurable_fst).snd measurable_const)

/-- Chronological sorting remains jointly measurable in the history and horizon. -/
theorem measurable_observedList_time (C : ℝ) : Measurable
    (fun p : EventView J × ℝ => observedList p.2 C p.1) :=
  measurable_chronologicalList (fun e (p : EventView J × ℝ) => (p.1 e).1)
    (fun e => ((measurable_pi_apply e).comp measurable_fst).fst)
    (fun p => observedSet p.2 C p.1) (measurable_observedSet_time C)

/-- The same finite recursion allows a variable observation time. -/
theorem measurable_runObserved_time (C : ℝ) : Measurable
    (fun p : (EventView J × E) × ℝ => runObserved active jump rate p.2 C p.1.2 p.1.1) := by
  have hr : Measurable (fun p : (EventView J × E) × List (Event J) =>
      Freezing.run active jump (observedDecode rate p.1.1) p.1.2 p.2) := by
    apply measurable_from_prod_countable
    exact measurable_observedRun_fixed active jump rate
  exact hr.comp (measurable_fst.prodMk
    ((measurable_observedList_time C).comp (measurable_fst.fst.prodMk measurable_snd)))

omit [Countable J] [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- A later observed history contains the entire earlier finite recursion,
including the total construction on exceptional samples. -/
theorem process_eq_runObserved_later [Fintype J] (C : ℝ) (x : E)
    (ω : MarkedNoise.Sample J) {s T : ℝ} (hs : s ≤ T) :
    CommonFrozenProcess.process active jump rate C x ω s =
      runObserved active jump rate s C x (view T ω) := by
  rw [process_eq_runObserved_view]
  rw [← censor_view hs ω, runObserved_censor]

end Observed

section Global
variable {A E J : Type*} [MeasurableSpace A] [DecidableEq E] [Fintype J]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → E → ℝ) (initial : A → E) (e : E)
  (hinit : Measurable initial)
include hinit

omit [TopologicalSpace E] [PolishSpace E] [BorelSpace E] in
/-- Each frozen path stopped at a deterministic horizon is jointly measurable
in that horizon's raw history and the evaluation time. -/
theorem measurable_frozen_at_min (active : Finset E) (C T : ℝ) :
    @Measurable (CommonInitialNoise.Sample A J × ℝ) E
      ((CommonInitialNoise.filtration A J T).prod inferInstance) _
      (fun p => CommonInitialNoise.process active jump rate initial C p.1 (min p.2 T)) := by
  have hv := (CommonInitialNoise.measurable_view_at (A := A) (J := J) T).comp
    (@measurable_fst (CommonInitialNoise.Sample A J) ℝ
      (CommonInitialNoise.filtration A J T) inferInstance)
  have hx := (hinit.comp (CommonInitialNoise.measurable_initial_at (J := J) T)).comp
    (@measurable_fst (CommonInitialNoise.Sample A J) ℝ
      (CommonInitialNoise.filtration A J T) inferInstance)
  have ht : @Measurable (CommonInitialNoise.Sample A J × ℝ) ℝ
      ((CommonInitialNoise.filtration A J T).prod inferInstance) _
      (fun p => min p.2 T) := measurable_snd.min measurable_const
  have hm := (measurable_runObserved_time active jump rate C).comp ((hv.prodMk hx).prodMk ht)
  convert hm using 1
  funext p
  exact process_eq_runObserved_later active jump rate C (initial p.1.1) p.1.2 (min_le_right _ _)

/-- Joint raw-history measurability of the actual all-sample global path
truncated at a deterministic horizon. -/
theorem measurable_process_at_min (T : ℝ) :
    @Measurable (CommonInitialNoise.Sample A J × ℝ) E
      ((CommonInitialNoise.filtration A J T).prod inferInstance) _
      (fun p => GlobalLocalizedProcess.process V hfinite jump rate initial e p.1 (min p.2 T)) := by
  letI : MeasurableSpace (CommonInitialNoise.Sample A J) := CommonInitialNoise.filtration A J T
  letI : Nonempty E := ⟨e⟩
  exact (StronglyMeasurable.limUnder (l := atTop) (fun n =>
    (measurable_frozen_at_min jump rate initial hinit (LyapunovLocalization.active V hfinite n)
      (LyapunovLocalization.rateBound V hfinite rate n) T).stronglyMeasurable)).measurable

/-- Integrating an arbitrary measurable state observable over a past window
is measurable in its terminal raw history. This holds on every sample. -/
theorem measurable_timeIntegral (f : E → ℝ) (ν : Measure ℝ) [SFinite ν] (s T : ℝ) :
    Measurable[CommonInitialNoise.filtration A J T]
      (fun p => ∫ t in Ioc s T, f (GlobalLocalizedProcess.process
        V hfinite jump rate initial e p t) ∂ν) := by
  letI : MeasurableSpace (CommonInitialNoise.Sample A J) := CommonInitialNoise.filtration A J T
  have hm : Measurable (fun p : CommonInitialNoise.Sample A J × ℝ =>
      (Ioc s T).indicator (fun t => f (GlobalLocalizedProcess.process
        V hfinite jump rate initial e p.1 (min t T))) p.2) :=
    ((measurable_of_countable f).comp
      (measurable_process_at_min V hfinite jump rate initial e hinit T)).piecewise
        (measurableSet_Ioc.preimage measurable_snd) measurable_const
  have hi := hm.stronglyMeasurable.integral_prod_right' (ν := ν)
  convert hi.measurable using 1
  funext p
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Ioc s T
  · simp [ht, min_eq_left ht.2]
  · simp [ht]

end Global

section Configuration
open ConfigurationLocalization MarkedIntensity
variable {A : Type*} [MeasurableSpace A] {N D : ℕ}
  {κ : MomentScale} {q : Rates D (MomentLaw κ D)} (control : LyapunovControl κ q)
  (hN : 0 < N) (initial : A → Configuration N D) (hinit : Measurable initial)
include hinit

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

/-- The classical actual current-state generator integral is raw-adapted.
Finite support and initial moments are unnecessary for this measurability fact. -/
theorem measurable_timeGenerator (F : Configuration N D → ℝ) (s T : ℝ) :
    Measurable[CommonInitialNoise.filtration A (Label N D) T]
      (fun p => ∫ t in Ioc s T, generator κ q hN F
        (ConfigurationNonexplosion.process control hN initial p t) ∂positiveVolume) :=
  measurable_timeIntegral (lyapunov control) (finite_sublevel control hN) jump
    (rate κ q hN) initial 0 hinit (generator κ q hN F) positiveVolume s T

end Configuration
end CarryingCapacity.GlobalHistoryIntegral
