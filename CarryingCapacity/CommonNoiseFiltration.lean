import CarryingCapacity.CommonFrozenProcess

/-!
# Adaptedness to the actual marked-noise history

The filtration observes the arrival time and height of each arrived event,
and a deterministic censored value for every event that has not yet arrived.
It is defined from the noise, independently of the frozen process. The process
factors through the observed history on every sample, including the exceptional
samples where an infinite selected set is assigned the empty event list.
-/

noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped Classical NNReal

namespace CarryingCapacity.CommonNoiseFiltration
open ChronologicalEvents Freezing

variable {J : Type*}

/-- Labelled marked points; event identifiers retain their strip and index. -/
abbrev EventView (J : Type*) := Event J → ℝ × ℝ

/-- Unarrived points reveal only a deterministic sentinel beyond the horizon. -/
def censor (t : ℝ) (v : EventView J) : EventView J :=
  fun e => if (v e).1 ≤ t then v e else (t + 1, 0)

theorem measurable_censor (t : ℝ) : Measurable (censor (J := J) t) := by
  apply measurable_pi_lambda
  intro e
  exact (measurable_pi_apply e).ite
    (measurableSet_le (measurable_pi_apply e).fst measurable_const) measurable_const

/-- Censoring a later observed history recovers exactly an earlier history. -/
theorem censor_censor {s t : ℝ} (hst : s ≤ t) (v : EventView J) :
    censor s (censor t v) = censor s v := by
  funext e
  by_cases hs : (v e).1 ≤ s
  · simp [censor, hs, hs.trans hst]
  · by_cases ht : (v e).1 ≤ t
    · simp [censor, hs, ht]
    · have hsent : ¬t + 1 ≤ s := by linarith
      simp [censor, hs, ht, hsent]

/-- The full labelled point family obtained from the actual common noise. -/
def points (ω : MarkedNoise.Sample J) : EventView J :=
  fun e => MarkedNoise.point e.1 ω e.2

theorem measurable_points : Measurable (points : MarkedNoise.Sample J → EventView J) :=
  measurable_pi_lambda _ (fun e => MarkedNoise.measurable_point e.1 e.2)

/-- The information revealed by the marked noise up to time `t`. -/
def view (t : ℝ) (ω : MarkedNoise.Sample J) : EventView J := censor t (points ω)

theorem measurable_view (t : ℝ) : Measurable (view (J := J) t) :=
  (measurable_censor t).comp measurable_points

theorem censor_view {s t : ℝ} (hst : s ≤ t) (ω : MarkedNoise.Sample J) :
    censor s (view t ω) = view s ω := censor_censor hst (points ω)

/-- The natural observation filtration, as genuine increasing sub-σ-algebras
of the common sample space. It does not refer to the constructed process. -/
def filtration (J : Type*) : Filtration ℝ (inferInstance : MeasurableSpace (MarkedNoise.Sample J)) where
  seq t := (inferInstance : MeasurableSpace (EventView J)).comap (view t)
  mono' := by
    intro s t hst
    change MeasurableSpace.comap (view (J := J) s) _ ≤
      MeasurableSpace.comap (view (J := J) t) _
    have he : view (J := J) s = censor s ∘ view t :=
      funext (fun ω => (censor_view hst ω).symm)
    rw [he, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_censor s).comap_le
  le' t := (measurable_view t).comap_le

/-- The observed history is measurable in precisely the observation σ-algebra. -/
theorem measurable_view_at (t : ℝ) : Measurable[filtration J t] (view t) :=
  comap_measurable _

section Lists

variable [Countable J]

local instance : MeasurableSpace (List (Event J)) := ⊤
local instance : MeasurableSingletonClass (List (Event J)) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (Finset (Event J)) := ⊤
local instance : MeasurableSingletonClass (Finset (Event J)) := ⟨fun _ => trivial⟩

/-- Events visible in the time-height box of an arbitrary point family. -/
def observedSet (t C : ℝ) (v : EventView J) : Set (Event J) :=
  {e | (v e).1 ≤ t ∧ (v e).2 ≤ C}

omit [Countable J] in
theorem measurable_observedSet (t C : ℝ) : Measurable (observedSet (J := J) t C) := by
  apply measurable_set_iff.mpr
  intro e
  apply measurable_to_prop
  rw [preimage_singleton_true]
  change MeasurableSet ({v : EventView J | (v e).1 ≤ t} ∩
    {v : EventView J | (v e).2 ≤ C})
  exact (measurableSet_le (measurable_pi_apply e).fst measurable_const).inter
    (measurableSet_le (measurable_pi_apply e).snd measurable_const)

/-- The chronological recursion can be run using only a point family. -/
def observedList (t C : ℝ) (v : EventView J) : List (Event J) :=
  chronologicalList (fun e (w : EventView J) => (w e).1) (observedSet t C) v

theorem measurable_observedList (t C : ℝ) : Measurable (observedList (J := J) t C) :=
  measurable_chronologicalList _ (fun e => (measurable_pi_apply e).fst) _
    (measurable_observedSet t C)

omit [Countable J] in
/-- Censoring removes none of the events in the current time-height box. -/
theorem observedSet_censor (t C : ℝ) (v : EventView J) :
    observedSet t C (censor t v) = observedSet t C v := by
  ext e
  by_cases ht : (v e).1 ≤ t
  · simp [observedSet, censor, ht]
  · have hs : ¬t + 1 ≤ t := by linarith
    simp [observedSet, censor, ht, hs]

omit [Countable J] in
/-- The censor is literally unchanged at every selected event. -/
theorem censor_eq_of_mem {t C : ℝ} {v : EventView J} {e : Event J}
    (he : e ∈ observedSet t C v) : censor t v e = v e :=
  if_pos he.1

omit [Countable J] in
theorem selectedFinset_subset (A : EventView J → Set (Event J)) (v : EventView J)
    {e : Event J} (he : e ∈ selectedFinset A v) : e ∈ A v := by
  by_cases h : (A v).Finite
  · exact (mem_selectedFinset A v h e).mp he
  · simp [selectedFinset, h] at he

end Lists

section SortingCongruence

variable {I : Type*}

/-- Insertion depends only on the time values of events in the input list. -/
theorem orderedInsert_time_congr (f g : I → ℝ) (i : I) (l : List I)
    (hi : f i = g i) (hl : ∀ j ∈ l, f j = g j) :
    l.orderedInsert (fun a b => f a ≤ f b) i =
      l.orderedInsert (fun a b => g a ≤ g b) i := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have hj := hl j (by simp)
    have hh := ih (fun k hk => hl k (by simp [hk]))
    simp only [List.orderedInsert, hi, hj, hh]

/-- The actual stable sorting operation ignores time values outside its list;
this requires no no-collision or almost-sure ordering assumption. -/
theorem insertionSort_time_congr (f g : I → ℝ) (l : List I)
    (hl : ∀ j ∈ l, f j = g j) :
    l.insertionSort (fun a b => f a ≤ f b) =
      l.insertionSort (fun a b => g a ≤ g b) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.insertionSort]
    rw [ih (fun j hj => hl j (by simp [hj]))]
    apply orderedInsert_time_congr
    · exact hl i (by simp)
    · intro j hj
      exact hl j (by simpa only [List.mem_cons, List.mem_insertionSort] using Or.inr hj)

end SortingCongruence

section Factorization

variable [Countable J]

omit [Countable J] in
/-- Censoring preserves the full actual event list on every sample, even when
the selected set is infinite and the total construction returns an empty list. -/
theorem observedList_censor (t C : ℝ) (v : EventView J) :
    observedList t C (censor t v) = observedList t C v := by
  have hset : selectedFinset (observedSet t C) (censor t v) =
      selectedFinset (observedSet t C) v := by
    simp only [selectedFinset, observedSet_censor]
  unfold observedList chronologicalList
  rw [hset]
  apply insertionSort_time_congr
  intro e he
  have hm := selectedFinset_subset (observedSet t C) v (Finset.mem_toList.mp he)
  exact congrArg Prod.fst (censor_eq_of_mem hm)

omit [Countable J] in
theorem observedList_points (t C : ℝ) (ω : MarkedNoise.Sample J) :
    observedList t C (points ω) = boxedList (ω, t, C) := rfl

omit [Countable J] in
theorem observedList_mem_subset {t C : ℝ} {v : EventView J} {e : Event J}
    (he : e ∈ observedList t C v) : e ∈ observedSet t C v := by
  simp only [observedList, chronologicalList, List.mem_insertionSort,
    Finset.mem_toList] at he
  exact selectedFinset_subset (observedSet t C) v he

end Factorization

section Runs

variable {E : Type*} [DecidableEq E]

/-- A finite recursion depends only on the decoder values for events in its
input list. It imposes no conditions on unused event identifiers. -/
theorem run_congr_decode {M : Type*} (active : Finset E) (jump : J → E → E)
    (d₁ d₂ : E → M → Option J) (x : E) (l : List M)
    (h : ∀ e ∈ l, ∀ y, d₁ y e = d₂ y e) :
    Freezing.run active jump d₁ x l = Freezing.run active jump d₂ x l := by
  induction l generalizing x with
  | nil => rfl
  | cons e l ih =>
    have hs : frozenStep active jump d₁ x e = frozenStep active jump d₂ x e := by
      simp only [frozenStep, h e (by simp) x]
    simp only [Freezing.run, hs]
    exact ih _ (fun f hf y => h f (by simp [hf]) y)

/-- Acceptance uses the physical marked height in the observed point family. -/
def observedDecode (rate : J → E → ℝ) (v : EventView J) (x : E) (e : Event J) : Option J :=
  if (v e).2 ≤ rate e.1 x then some e.1 else none

/-- Reconstruct the frozen state from a censored history and an initial state. -/
def runObserved (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)
    (t C : ℝ) (x : E) (v : EventView J) : E :=
  Freezing.run active jump (observedDecode rate v) x (observedList t C v)

/-- The reconstruction ignores all future point data, on every sample. -/
theorem runObserved_censor (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)
    (t C : ℝ) (x : E) (v : EventView J) :
    runObserved active jump rate t C x (censor t v) =
      runObserved active jump rate t C x v := by
  unfold runObserved
  rw [observedList_censor]
  apply run_congr_decode
  intro e he y
  simp only [observedDecode, censor_eq_of_mem (observedList_mem_subset he)]

/-- Exact all-sample factorization of the previously constructed frozen process
through the actual noise observed by the evaluation time. -/
theorem process_eq_runObserved_view (active : Finset E) (jump : J → E → E)
    (rate : J → E → ℝ) (C : ℝ) (x : E) (ω : MarkedNoise.Sample J) (t : ℝ) :
    CommonFrozenProcess.process active jump rate C x ω t =
      runObserved active jump rate t C x (view t ω) := by
  rw [view, runObserved_censor]
  rfl

end Runs

section Measurability

variable {E : Type*} [DecidableEq E] [Countable E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [Countable J]
  (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)

local instance : MeasurableSpace (List (Event J)) := ⊤
local instance : MeasurableSingletonClass (List (Event J)) := ⟨fun _ => trivial⟩

omit [Countable J] in
theorem measurable_observedStep (e : Event J) : Measurable
    (fun p : EventView J × E => frozenStep active jump (observedDecode rate p.1) p.2 e) := by
  apply measurable_from_prod_countable
  intro x
  by_cases hx : x ∈ active
  · simp only [frozenStep, hx, ↓reduceIte]
    have hh : Measurable (fun v : EventView J =>
        if (v e).2 ≤ rate e.1 x then jump e.1 x else x) := measurable_const.ite
      (measurableSet_le (measurable_pi_apply e).snd measurable_const) measurable_const
    convert hh using 1
    funext v
    by_cases h : (v e).2 ≤ rate e.1 x <;> simp [observedDecode, h]
  · simpa only [frozenStep, hx, ↓reduceIte] using
      (measurable_const : Measurable (fun _ : EventView J => x))

omit [Countable J] in
theorem measurable_observedRun_fixed (l : List (Event J)) : Measurable
    (fun p : EventView J × E =>
      Freezing.run active jump (observedDecode rate p.1) p.2 l) := by
  induction l with
  | nil => exact measurable_snd
  | cons e l ih =>
    exact ih.comp (measurable_fst.prodMk (measurable_observedStep active jump rate e))

/-- Joint measurability in the observed history and initial state is derived
from the finite recursion and the measurable chronological-list construction. -/
theorem measurable_runObserved (t C : ℝ) : Measurable
    (fun p : EventView J × E => runObserved active jump rate t C p.2 p.1) := by
  have hrun : Measurable (fun p : (EventView J × E) × List (Event J) =>
      Freezing.run active jump (observedDecode rate p.1.1) p.1.2 p.2) := by
    apply measurable_from_prod_countable
    exact measurable_observedRun_fixed active jump rate
  exact hrun.comp (measurable_id.prodMk ((measurable_observedList t C).comp measurable_fst))

/-- The actual process at time `t` is measurable for the history σ-algebra
generated by arrived noise points, not by the process itself. -/
theorem measurable_process_at (C : ℝ) (x : E) (t : ℝ) :
    Measurable[filtration J t]
      (fun ω => CommonFrozenProcess.process active jump rate C x ω t) := by
  have h := (measurable_runObserved active jump rate t C).comp
    ((measurable_view_at t).prodMk
      (measurable_const : Measurable[filtration J t] (fun _ : MarkedNoise.Sample J => x)))
  simpa only [Function.comp_def, process_eq_runObserved_view] using h

/-- A random initial state already known at time zero gives the same genuine
history measurability at every nonnegative time. -/
theorem measurable_process_random_initial_at (C : ℝ) (X : MarkedNoise.Sample J → E)
    (hX : Measurable[filtration J 0] X) (t : ℝ) (ht : 0 ≤ t) :
    Measurable[filtration J t]
      (fun ω => CommonFrozenProcess.process active jump rate C (X ω) ω t) := by
  have hXt : Measurable[filtration J t] X :=
    hX.mono ((filtration J).mono ht) le_rfl
  have h := (measurable_runObserved active jump rate t C).comp
    ((measurable_view_at t).prodMk hXt)
  simpa only [Function.comp_def, process_eq_runObserved_view] using h

end Measurability

/-- The same natural observation filtration indexed by nonnegative times. -/
def nonnegativeFiltration (J : Type*) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (MarkedNoise.Sample J)) where
  seq t := filtration J (t : ℝ)
  mono' := fun _ _ h => (filtration J).mono h
  le' t := (filtration J).le (t : ℝ)

section Adaptedness

variable {E : Type*} [DecidableEq E] [Countable E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [Countable J] [TopologicalSpace E]
  [PseudoMetrizableSpace E] [SecondCountableTopology E] [OpensMeasurableSpace E]
  (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)

/-- The actual common-noise frozen process is adapted to the filtration of
arrived labelled marks. No probability-one restriction is needed. -/
theorem adapted_process (C : ℝ) (x : E) :
    Adapted (filtration J)
      (fun t ω => CommonFrozenProcess.process active jump rate C x ω t) :=
  fun t => (measurable_process_at active jump rate C x t).stronglyMeasurable

/-- Random initial information measurable at time zero is retained by the
nonnegative-time natural filtration, and the resulting process is adapted. -/
theorem adapted_process_random_initial (C : ℝ) (X : MarkedNoise.Sample J → E)
    (hX : Measurable[filtration J 0] X) :
    Adapted (nonnegativeFiltration J)
      (fun t ω => CommonFrozenProcess.process active jump rate C (X ω) ω (t : ℝ)) :=
  fun t => (measurable_process_random_initial_at active jump rate C X hX
    (t : ℝ) t.property).stronglyMeasurable

end Adaptedness

end CarryingCapacity.CommonNoiseFiltration
