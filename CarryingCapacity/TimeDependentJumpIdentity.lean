import CarryingCapacity.TimeDependentFrozenProcess
import CarryingCapacity.FrozenJumpIdentity

/-!
# Chronological jump identities with event-time rates

The same finite telescoping theorem applies to the actual event-time decoder.
Its prefix states are identified with the strict-past states of the constructed
time-dependent path, retaining the exit jump and rejecting subsequent proposals.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology

namespace CarryingCapacity.TimeDependentJumpIdentity
open Freezing TimeDependentFrozenProcess CommonFrozenRegularity ChronologicalEvents
open FrozenJumpIdentity (run_telescope filter_before_get_eq_take)

variable {E J : Type*} [DecidableEq E] [Fintype J]
  (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)

/-- The actual thinning increment, retaining the first exit jump. -/
def acceptedIncrement (V : E → ℝ) (ω : MarkedNoise.Sample J) (x : E) (e : Event J) : ℝ :=
  if x ∈ active ∧ (MarkedNoise.point e.1 ω e.2).2 ≤ rate e.1 (MarkedNoise.point e.1 ω e.2).1 x then
    V (jump e.1 x) - V x else 0

omit [Fintype J] in
theorem frozenStep_increment (V : E → ℝ) (ω : MarkedNoise.Sample J) (x : E) (e : Event J) :
    V (frozenStep active jump (eventDecode rate ω) x e) - V x =
      acceptedIncrement active jump rate V ω x e := by
  by_cases hx : x ∈ active <;>
    by_cases hh : (MarkedNoise.point e.1 ω e.2).2 ≤ rate e.1 (MarkedNoise.point e.1 ω e.2).1 x <;>
    simp [frozenStep, eventDecode, acceptedIncrement, hx, hh]

omit [Fintype J] in
/-- Exact identity for the defined process, including exceptional samples where
the construction assigns the empty list to an infinite selected event set. -/
theorem process_telescope (V : E → ℝ) (C : ℝ) (x : E)
    (ω : MarkedNoise.Sample J) (t : ℝ) :
    V (process active jump rate C x ω t) - V x =
      ∑ n : Fin (boxedList (ω,t,C)).length,
        acceptedIncrement active jump rate V ω
          (run active jump (eventDecode rate ω) x ((boxedList (ω,t,C)).take n.val))
          ((boxedList (ω,t,C)).get n) := by
  change V (run active jump (eventDecode rate ω) x (boxedList (ω,t,C))) - V x = _
  rw [run_telescope]
  exact Finset.sum_congr rfl (fun n _ => frozenStep_increment active jump rate V ω _ _)

/-- Explicit strict-past state; no choice of a limit or initial topology is used. -/
def leftProcess (C : ℝ) (x : E) (ω : MarkedNoise.Sample J) (t : ℝ) : E :=
  run active jump (eventDecode rate ω) x ((boxedList (ω,t,C)).filter
    (fun e => decide ((MarkedNoise.point e.1 ω e.2).1 < t)))

/-- The actual frozen path equals its explicit strict-past state throughout
some interval immediately to the left of every time. -/
theorem ae_process_eq_leftProcess_on_left : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C x t, ∃ b, b < t ∧ ∀ u ∈ Ico b t,
      process active jump rate C x ω u = leftProcess active jump rate C x ω t := by
  filter_upwards [ae_boxedList_time_filter (J := J)] with ω hω
  intro C x t
  obtain ⟨b, hb, hl⟩ := filter_time_left_constant
    (fun e : Event J => (MarkedNoise.point e.1 ω e.2).1) (boxedList (ω,t,C)) t
  refine ⟨b, hb, ?_⟩
  intro u hu
  unfold process runBox leftProcess
  rw [← hω u t C hu.2.le, hl u hu]

/-- At an actual proposal time, the strict-past state is exactly its preceding
prefix run, simultaneously for all cutoffs, initial states and horizons. -/
theorem ae_leftProcess_at_event : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C x T (n : Fin (boxedList (ω,T,C)).length),
      leftProcess active jump rate C x ω
          (MarkedNoise.point ((boxedList (ω,T,C)).get n).1 ω
            ((boxedList (ω,T,C)).get n).2).1 =
        run active jump (eventDecode rate ω) x ((boxedList (ω,T,C)).take n.val) := by
  filter_upwards [ae_boxedList_time_filter (J := J), ae_boxedList_mem (J := J),
    ae_boxedList_strict (J := J)] with ω hfilter hmem hstrict
  intro C x T n
  let l := boxedList (ω,T,C)
  let e := l.get n
  let τ := (MarkedNoise.point e.1 ω e.2).1
  have hτ : τ ≤ T := ((hmem T C e).mp (List.get_mem l n)).1
  change run active jump (eventDecode rate ω) x ((boxedList (ω,τ,C)).filter
    (fun e => decide ((MarkedNoise.point e.1 ω e.2).1 < τ))) = _
  rw [← hfilter τ T C hτ, List.filter_filter]
  have he : (fun e' : Event J =>
      decide ((MarkedNoise.point e'.1 ω e'.2).1 < τ) &&
        decide ((MarkedNoise.point e'.1 ω e'.2).1 ≤ τ)) =
      (fun e' => decide ((MarkedNoise.point e'.1 ω e'.2).1 < τ)) := by
    funext e'
    by_cases hh : (MarkedNoise.point e'.1 ω e'.2).1 < τ
    · simp [hh, hh.le]
    · simp [hh]
  rw [he]
  congr 1
  exact filter_before_get_eq_take _ l (hstrict T C) n.val n.isLt

/-- Pathwise change is the sum of accepted increments evaluated at actual
left states, over the actual chronological event list. -/
theorem ae_process_telescope_left (V : E → ℝ) : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C x t, V (process active jump rate C x ω t) - V (process active jump rate C x ω 0) =
      ∑ n : Fin (boxedList (ω,t,C)).length,
        let e := (boxedList (ω,t,C)).get n
        acceptedIncrement active jump rate V ω
          (leftProcess active jump rate C x ω (MarkedNoise.point e.1 ω e.2).1) e := by
  filter_upwards [ae_leftProcess_at_event active jump rate, ae_process_zero active jump rate]
    with ω hleft hzero
  intro C x t
  rw [hzero C x, process_telescope]
  apply Finset.sum_congr rfl
  intro n _
  dsimp only
  rw [hleft C x t n]

end CarryingCapacity.TimeDependentJumpIdentity
