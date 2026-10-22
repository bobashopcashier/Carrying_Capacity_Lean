import CarryingCapacity.TimeDependentFrozenProcess
import CarryingCapacity.CommonNoiseFiltration
import CarryingCapacity.CommonInitialNoise

/-!
# Actual histories for time-dependent frozen rates

The event-time rate is evaluated from the observed point itself. Censoring
therefore preserves each selected event's time, height, and acceptance decision.
The actual time-inhomogeneous recursion is measurable in the same noise history
as the autonomous construction, with no proposed-process filtration premise.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical

namespace CarryingCapacity.TimeDependentHistory
open ChronologicalEvents Freezing CommonNoiseFiltration

variable {J E : Type*} [DecidableEq E]

/-- Acceptance reads both time and height from the observed event. -/
def observedDecode (rate : J → ℝ → E → ℝ) (v : EventView J)
    (x : E) (e : Event J) : Option J :=
  if (v e).2 ≤ rate e.1 (v e).1 x then some e.1 else none

/-- The actual finite recursion reconstructed from an observed marked history. -/
def runObserved (active : Finset E) (jump : J → E → E)
    (rate : J → ℝ → E → ℝ) (t C : ℝ) (x : E) (v : EventView J) : E :=
  Freezing.run active jump (observedDecode rate v) x (observedList t C v)

theorem runObserved_censor (active : Finset E) (jump : J → E → E)
    (rate : J → ℝ → E → ℝ) (t C : ℝ) (x : E) (v : EventView J) :
    runObserved active jump rate t C x (censor t v) =
      runObserved active jump rate t C x v := by
  unfold runObserved
  rw [observedList_censor]
  apply run_congr_decode
  intro e he y
  simp only [observedDecode, censor_eq_of_mem (observedList_mem_subset he)]

/-- Exact factorization on every sample, including total-definition fallbacks. -/
theorem process_eq_runObserved_view (active : Finset E) (jump : J → E → E)
    (rate : J → ℝ → E → ℝ) (C : ℝ) (x : E) (ω : MarkedNoise.Sample J) (t : ℝ) :
    TimeDependentFrozenProcess.process active jump rate C x ω t =
      runObserved active jump rate t C x (view t ω) := by
  rw [view, runObserved_censor]
  rfl

section Measurability
variable [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [Countable J]
  (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (hRate : ∀ j x, Measurable (fun t => rate j t x))
include hRate

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
        if (v e).2 ≤ rate e.1 (v e).1 x then jump e.1 x else x) := measurable_const.ite
      (measurableSet_le (measurable_pi_apply e).snd
        ((hRate e.1 x).comp (measurable_pi_apply e).fst)) measurable_const
    convert hh using 1
    funext v
    by_cases h : (v e).2 ≤ rate e.1 (v e).1 x <;> simp [observedDecode, h]
  · simpa only [frozenStep, hx, ↓reduceIte] using
      (measurable_const : Measurable (fun _ : EventView J => x))

omit [Countable J] in
theorem measurable_observedRun_fixed (l : List (Event J)) : Measurable
    (fun p : EventView J × E =>
      Freezing.run active jump (observedDecode rate p.1) p.2 l) := by
  induction l with
  | nil => exact measurable_snd
  | cons e l ih =>
    exact ih.comp (measurable_fst.prodMk (measurable_observedStep active jump rate hRate e))

/-- Joint history/initial-state measurability with merely measurable time rates. -/
theorem measurable_runObserved (t C : ℝ) : Measurable
    (fun p : EventView J × E => runObserved active jump rate t C p.2 p.1) := by
  have hrun : Measurable (fun p : (EventView J × E) × List (Event J) =>
      Freezing.run active jump (observedDecode rate p.1.1) p.1.2 p.2) := by
    apply measurable_from_prod_countable
    exact measurable_observedRun_fixed active jump rate hRate
  exact hrun.comp (measurable_id.prodMk ((measurable_observedList t C).comp measurable_fst))

/-- The actual frozen state at t is measurable in the noise observed by t. -/
theorem measurable_process_at (C : ℝ) (x : E) (t : ℝ) :
    Measurable[filtration J t]
      (fun ω => TimeDependentFrozenProcess.process active jump rate C x ω t) := by
  have h := (measurable_runObserved active jump rate hRate t C).comp
    ((measurable_view_at t).prodMk
      (measurable_const : Measurable[filtration J t] (fun _ : MarkedNoise.Sample J => x)))
  simpa only [Function.comp_def, process_eq_runObserved_view] using h

/-- An arbitrary measurable independent initial record is known in the
initial-record/noise history, also for the time-dependent recursion. -/
theorem measurable_initial_process_at {A : Type*} [MeasurableSpace A]
    (initial : A → E) (hinit : Measurable initial) (C t : ℝ) :
    Measurable[CommonInitialNoise.filtration A J t]
      (fun p : CommonInitialNoise.Sample A J =>
        TimeDependentFrozenProcess.process active jump rate C (initial p.1) p.2 t) := by
  have h := (measurable_runObserved active jump rate hRate t C).comp
    ((CommonInitialNoise.measurable_view_at t).prodMk
      (hinit.comp (CommonInitialNoise.measurable_initial_at t)))
  simpa only [Function.comp_def, process_eq_runObserved_view] using h

end Measurability
end CarryingCapacity.TimeDependentHistory
