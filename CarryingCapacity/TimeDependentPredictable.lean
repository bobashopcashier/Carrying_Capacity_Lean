import CarryingCapacity.TimeDependentHistory
import CarryingCapacity.PredictableTime

/-!
# Predictable event-time acceptance fields

The pre-jump state is the strict-past measurable limit of the actual adapted
frozen recursion. A merely measurable deterministic time coefficient is
predictable when evaluated at that state. No continuity of the rates or
predictability of the proposed process is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Classical

namespace CarryingCapacity.TimeDependentPredictable
open PredictableSets PredictableStepApproximation PredictableTime TimeDependentFrozenProcess

variable {J E : Type*} [Fintype J] [DecidableEq E]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)

/-- Predictable strict-past state of the actual time-dependent frozen process. -/
def preState (C : ℝ) (x : E) (ω : MarkedNoise.Sample J) (t : ℝ) : E :=
  pastLimit (fun s ω => process active jump rate C x ω s) x ω t

theorem measurable_preState (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (C : ℝ) (x : E) :
    Measurable[predictable (CommonNoiseFiltration.filtration J)]
      (fun p : MarkedNoise.Sample J × (ℝ × ℝ) => preState active jump rate C x p.1 p.2.1) :=
  measurable_pastLimit (CommonNoiseFiltration.filtration J) _
    (fun s _ => TimeDependentHistory.measurable_process_at active jump rate hRate C x s) x

omit [Fintype J] [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
theorem preState_eq_of_left_constant (C : ℝ) (x : E) (ω : MarkedNoise.Sample J)
    (t : ℝ) (ht : 0 < t) (b : ℝ) (hb : b < t) (y : E)
    (hy : ∀ s ∈ Ico b t, process active jump rate C x ω s = y) :
    preState active jump rate C x ω t = y :=
  pastLimit_eq_of_left_constant _ x ω t ht b hb y hy

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
/-- The predictable candidate is the genuine constant left state at every
positive time on one common event. -/
theorem ae_process_eq_preState_on_left : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C x t, 0 < t → ∃ b, b < t ∧ ∀ s ∈ Ico b t,
      process active jump rate C x ω s = preState active jump rate C x ω t := by
  filter_upwards [ae_process_left_constant active jump rate] with ω hω
  intro C x t ht
  obtain ⟨b, y, hb, hy⟩ := hω C x t
  refine ⟨b, hb, ?_⟩
  rw [preState_eq_of_left_constant active jump rate C x ω t ht b hb y hy]
  exact hy

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
/-- The actual time-dependent path converges to its predictable pre-state from the left. -/
theorem ae_tendsto_preState : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C x t, 0 < t → Tendsto (process active jump rate C x ω) (𝓝[<] t)
      (𝓝 (preState active jump rate C x ω t)) := by
  filter_upwards [ae_process_eq_preState_on_left active jump rate] with ω hω
  intro C x t ht
  obtain ⟨b, hb, hy⟩ := hω C x t ht
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hb)] with s hs hbs
  exact (hy s ⟨hbs.le, hs⟩).symm

/-- The actual frozen acceptance rule evaluates the coefficient at event time. -/
def jumpIncrement (C : ℝ) (x : E) (V : E → ℝ) (j : J)
    (p : MarkedNoise.Sample J × (ℝ × ℝ)) : ℝ :=
  if 0 < p.2.1 ∧ preState active jump rate C x p.1 p.2.1 ∈ active ∧
      p.2.2 ≤ C ∧ p.2.2 ≤ rate j p.2.1 (preState active jump rate C x p.1 p.2.1)
    then V (jump j (preState active jump rate C x p.1 p.2.1)) -
      V (preState active jump rate C x p.1 p.2.1)
    else 0

/-- The actual accepted jump field is predictable under merely measurable time rates. -/
theorem measurable_jumpIncrement (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (C : ℝ) (x : E) (V : E → ℝ) (j : J) :
    Measurable[predictable (CommonNoiseFiltration.filtration J)]
      (jumpIncrement active jump rate C x V j) := by
  let F := CommonNoiseFiltration.filtration J
  have hz := measurable_preState active jump rate hRate C x
  have hr := measurable_evaluation F (rate j) (hRate j) _ hz
  have hh := measurable_positiveHeight F
  have hd := ((measurable_of_countable (fun y => V (jump j y))).comp hz).sub
    ((measurable_of_countable V).comp hz)
  have hm : Measurable[predictable F] (fun p : MarkedNoise.Sample J × (ℝ × ℝ) =>
      if 0 < p.2.1 ∧ preState active jump rate C x p.1 p.2.1 ∈ active ∧
          positiveHeight p ≤ C ∧ positiveHeight p ≤ rate j (positiveTime p)
            (preState active jump rate C x p.1 p.2.1)
      then V (jump j (preState active jump rate C x p.1 p.2.1)) -
        V (preState active jump rate C x p.1 p.2.1) else 0) := by
    exact hd.ite ((measurableSet_positive F).inter
      (((Finset.measurableSet active).preimage hz).inter
        ((measurableSet_le hh measurable_const).inter (measurableSet_le hh hr)))) measurable_const
  convert hm using 1
  funext p
  by_cases ht : 0 < p.2.1 <;> simp [jumpIncrement, positiveHeight, positiveTime, ht]

end CarryingCapacity.TimeDependentPredictable
