import CarryingCapacity.TimeDependentInitial
import CarryingCapacity.GlobalHistoryIntegral

/-!
# Raw-history measurability of time-dependent frozen path integrals

The actual initialized path up to a deterministic horizon is reconstructed
from that horizon's raw marked history and the initial record, on every sample.
Joint history/time measurability then gives measurability of time integrals
of arbitrary observables measurable in time at each countable state. Neither
a completed filtration nor an almost-sure path modification is needed.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical

namespace CarryingCapacity.TimeDependentHistoryIntegral
open CommonNoiseFiltration ChronologicalEvents TimeDependentHistory

section Observed
variable {J E : Type*} [Countable J] [DecidableEq E] [Countable E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
  (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (hRate : ∀ j x, Measurable (fun t => rate j t x))
include hRate

local instance : MeasurableSpace (List (Event J)) := ⊤
local instance : MeasurableSingletonClass (List (Event J)) := ⟨fun _ => trivial⟩

/-- The event-time recursion is jointly measurable in observed history,
initial state, and evaluation horizon. -/
theorem measurable_runObserved_time (C : ℝ) : Measurable
    (fun p : (EventView J × E) × ℝ => runObserved active jump rate p.2 C p.1.2 p.1.1) := by
  have hr : Measurable (fun p : (EventView J × E) × List (Event J) =>
      Freezing.run active jump (observedDecode rate p.1.1) p.1.2 p.2) := by
    apply measurable_from_prod_countable
    exact measurable_observedRun_fixed active jump rate hRate
  exact hr.comp (measurable_fst.prodMk
    ((GlobalHistoryIntegral.measurable_observedList_time C).comp
      (measurable_fst.fst.prodMk measurable_snd)))

omit [Countable J] [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] hRate in
/-- A later raw history contains the exact earlier recursion, including
the total-definition fallbacks on exceptional samples. -/
theorem process_eq_runObserved_later (C : ℝ) (x : E)
    (ω : MarkedNoise.Sample J) {s T : ℝ} (hs : s ≤ T) :
    TimeDependentFrozenProcess.process active jump rate C x ω s =
      runObserved active jump rate s C x (view T ω) := by
  rw [TimeDependentHistory.process_eq_runObserved_view]
  rw [← censor_view hs ω, TimeDependentHistory.runObserved_censor]

end Observed

section Initialized
variable {A E J : Type*} [MeasurableSpace A] [DecidableEq E] [Countable J]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (initial : A → E) (hRate : ∀ j x, Measurable (fun t => rate j t x))
  (hinit : Measurable initial)
include hRate hinit

/-- The actual initialized process stopped at a deterministic horizon is
jointly measurable in its raw terminal history and evaluation time. -/
theorem measurable_process_at_min (C T : ℝ) :
    @Measurable (CommonInitialNoise.Sample A J × ℝ) E
      ((CommonInitialNoise.filtration A J T).prod inferInstance) _
      (fun p => TimeDependentInitial.process active jump rate initial C p.1 (min p.2 T)) := by
  have hv := (CommonInitialNoise.measurable_view_at (A := A) (J := J) T).comp
    (@measurable_fst (CommonInitialNoise.Sample A J) ℝ
      (CommonInitialNoise.filtration A J T) inferInstance)
  have hx := (hinit.comp (CommonInitialNoise.measurable_initial_at (J := J) T)).comp
    (@measurable_fst (CommonInitialNoise.Sample A J) ℝ
      (CommonInitialNoise.filtration A J T) inferInstance)
  have ht : @Measurable (CommonInitialNoise.Sample A J × ℝ) ℝ
      ((CommonInitialNoise.filtration A J T).prod inferInstance) _
      (fun p => min p.2 T) := measurable_snd.min measurable_const
  have hm := (measurable_runObserved_time active jump rate hRate C).comp ((hv.prodMk hx).prodMk ht)
  convert hm using 1
  funext p
  exact process_eq_runObserved_later active jump rate C (initial p.1.1) p.1.2 (min_le_right _ _)

/-- An arbitrary separately time-measurable state observable has a raw-history
measurable Bochner time integral. Integrability is not needed for measurability
of this total integral; no expectation or Dynkin identity is asserted here. -/
theorem measurable_timeIntegral (C : ℝ) (f : ℝ → E → ℝ)
    (hf : ∀ x, Measurable (fun t => f t x)) (ν : Measure ℝ) [SFinite ν] (s T : ℝ) :
    Measurable[CommonInitialNoise.filtration A J T]
      (fun p => ∫ t in Ioc s T, f t (TimeDependentInitial.process
        active jump rate initial C p t) ∂ν) := by
  letI : MeasurableSpace (CommonInitialNoise.Sample A J) := CommonInitialNoise.filtration A J T
  have hm : Measurable (fun p : CommonInitialNoise.Sample A J × ℝ =>
      (Ioc s T).indicator (fun t => f t (TimeDependentInitial.process
        active jump rate initial C p.1 (min t T))) p.2) :=
    ((PredictableTime.measurable_coefficient f hf).comp
      (measurable_snd.prodMk
        (measurable_process_at_min active jump rate initial hRate hinit C T))).piecewise
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

end Initialized
end CarryingCapacity.TimeDependentHistoryIntegral
