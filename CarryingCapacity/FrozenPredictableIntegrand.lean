import CarryingCapacity.PredictableStepApproximation
import CarryingCapacity.CommonFrozenRegularity
import Mathlib.Topology.Order.LeftRightLim

/-!
# Predictable pre-jump states of the actual frozen process

The pre-jump state is constructed from the measurable strict-past grid limit.
It is predictable on every sample. The actual path's proved local constancy
identifies it with its left limit, simultaneously at every positive time, on
one event of probability one. No regularity of exceptional paths is assumed.

The marked test-function increment includes the finite height cutoff used in
the actual frozen construction. Its predictable measurability is proved from
the pre-jump state and the positive-time mark coordinate.
-/

noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology

namespace CarryingCapacity.FrozenPredictableIntegrand
open PredictableSets PredictableStepApproximation CommonFrozenProcess

variable {J E : Type*} [Fintype J] [DecidableEq E]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)

/-- A predictable version of the actual frozen path immediately before time
`t`. Nonpositive times take the initial value. -/
def preState (C : ℝ) (x : E) (ω : MarkedNoise.Sample J) (t : ℝ) : E :=
  pastLimit (fun s ω => process active jump rate C x ω s) x ω t

theorem measurable_preState (C : ℝ) (x : E) :
    Measurable[predictable (CommonNoiseFiltration.filtration J)]
      (fun p : MarkedNoise.Sample J × (ℝ × ℝ) => preState active jump rate C x p.1 p.2.1) :=
  measurable_pastLimit (CommonNoiseFiltration.filtration J) _
    (fun s _ => CommonNoiseFiltration.measurable_process_at active jump rate C x s) x

omit [Fintype J] [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
theorem preState_eq_of_left_constant (C : ℝ) (x : E) (ω : MarkedNoise.Sample J)
    (t : ℝ) (ht : 0 < t) (b : ℝ) (hb : b < t) (y : E)
    (hy : ∀ s ∈ Ico b t, process active jump rate C x ω s = y) :
    preState active jump rate C x ω t = y :=
  pastLimit_eq_of_left_constant _ x ω t ht b hb y hy

omit [Fintype J] [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
theorem preState_nonpositive (C : ℝ) (x : E) (ω : MarkedNoise.Sample J)
    (t : ℝ) (ht : t ≤ 0) : preState active jump rate C x ω t = x :=
  pastLimit_nonpositive _ x ω t ht

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
/-- On one common event, every positive time has a constant left interval
whose value is exactly the constructed predictable pre-jump state. -/
theorem ae_process_eq_preState_on_left : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C x t, 0 < t → ∃ b, b < t ∧ ∀ s ∈ Ico b t,
      process active jump rate C x ω s = preState active jump rate C x ω t := by
  filter_upwards [CommonFrozenRegularity.ae_process_left_constant active jump rate]
    with ω hω
  intro C x t ht
  obtain ⟨b, y, hb, hy⟩ := hω C x t
  refine ⟨b, hb, ?_⟩
  rw [preState_eq_of_left_constant active jump rate C x ω t ht b hb y hy]
  exact hy

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
/-- The predictable version is the actual left limit at every positive time,
simultaneously for all cutoffs and initial states. -/
theorem ae_tendsto_preState : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C x t, 0 < t →
      Tendsto (process active jump rate C x ω) (𝓝[<] t)
        (𝓝 (preState active jump rate C x ω t)) := by
  filter_upwards [ae_process_eq_preState_on_left active jump rate] with ω hω
  intro C x t ht
  obtain ⟨b, hb, hy⟩ := hω C x t ht
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hb)] with s hs hbs
  exact (hy s ⟨hbs.le, hs⟩).symm

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
theorem ae_preState_eq_leftLim : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C x t, 0 < t →
      preState active jump rate C x ω t = Function.leftLim (process active jump rate C x ω) t := by
  filter_upwards [ae_tendsto_preState active jump rate] with ω hω
  intro C x t ht
  exact (leftLim_eq_of_tendsto (neBot_iff.mp inferInstance) (hω C x t ht)).symm

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
/-- The same deterministic finite enclosure controls every actual pre-jump
state almost surely, including initial states outside the active region. -/
theorem ae_preState_mem_or_eq_initial : ∀ᵐ ω ∂MarkedNoise.law J,
    ∀ C x t, 0 < t →
      preState active jump rate C x ω t ∈ Freezing.oneStepEnlargement active jump ∨
        preState active jump rate C x ω t = x := by
  filter_upwards [ae_process_eq_preState_on_left active jump rate] with ω hω
  intro C x t ht
  obtain ⟨b, hb, hy⟩ := hω C x t ht
  rw [← hy b ⟨le_rfl, hb⟩]
  exact process_mem_or_eq_initial active jump rate C x ω b

/-- Any measurable function of pre-jump state and mark, restricted to positive
time, is predictable. -/
theorem measurable_marked_function {A : Type*} [MeasurableSpace A]
    (C : ℝ) (x : E) (f : E × ℝ → A) (hf : Measurable f) (a : A) :
    Measurable[predictable (CommonNoiseFiltration.filtration J)]
      (fun p : MarkedNoise.Sample J × (ℝ × ℝ) =>
        if 0 < p.2.1 then f (preState active jump rate C x p.1 p.2.1, p.2.2) else a) := by
  classical
  letI : MeasurableSpace (MarkedNoise.Sample J × (ℝ × ℝ)) :=
    predictable (CommonNoiseFiltration.filtration J)
  have hm : Measurable (fun p : MarkedNoise.Sample J × (ℝ × ℝ) =>
      if 0 < p.2.1 then f (preState active jump rate C x p.1 p.2.1, positiveHeight p) else a) :=
    (hf.comp ((measurable_preState active jump rate C x).prodMk
    (measurable_positiveHeight (CommonNoiseFiltration.filtration J)))).ite
      (measurableSet_positive (CommonNoiseFiltration.filtration J)) measurable_const
  convert hm using 1
  funext p
  by_cases hp : 0 < p.2.1 <;> simp [positiveHeight, hp]

/-- The actual cutoff and acceptance rule applied to a test-function jump. -/
def jumpIncrement (C : ℝ) (x : E) (V : E → ℝ) (j : J)
    (p : MarkedNoise.Sample J × (ℝ × ℝ)) : ℝ :=
  if 0 < p.2.1 ∧ preState active jump rate C x p.1 p.2.1 ∈ active ∧
      p.2.2 ≤ C ∧ p.2.2 ≤ rate j (preState active jump rate C x p.1 p.2.1)
    then V (jump j (preState active jump rate C x p.1 p.2.1)) -
      V (preState active jump rate C x p.1 p.2.1)
    else 0

theorem measurable_jumpIncrement (C : ℝ) (x : E) (V : E → ℝ) (j : J) :
    Measurable[predictable (CommonNoiseFiltration.filtration J)]
      (jumpIncrement active jump rate C x V j) := by
  classical
  have hf : Measurable (fun p : E × ℝ =>
      if p.1 ∈ active ∧ p.2 ≤ C ∧ p.2 ≤ rate j p.1
      then V (jump j p.1) - V p.1 else 0) := by
    apply Measurable.ite
    · exact ((Finset.measurableSet active).preimage measurable_fst).inter
        ((measurableSet_le measurable_snd measurable_const).inter
          (measurableSet_le measurable_snd ((measurable_of_countable (rate j)).comp measurable_fst)))
    · exact ((measurable_of_countable (fun y => V (jump j y))).comp measurable_fst).sub
        ((measurable_of_countable V).comp measurable_fst)
    · exact measurable_const
  have hm := measurable_marked_function active jump rate C x _ hf (0 : ℝ)
  convert hm using 1
  funext p
  simp only [jumpIncrement, ite_and]

end CarryingCapacity.FrozenPredictableIntegrand
