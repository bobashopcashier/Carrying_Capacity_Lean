import CarryingCapacity.FrozenPredictableIntegrand
import CarryingCapacity.CommonInitialNoise

/-!
# Predictable frozen increments with an arbitrary initial record

Strict-past approximations of the actual initialized process define a
predictable pre-jump state on every sample. Its fallback at nonpositive times
is fixed, as required by the positive-time predictable sigma algebra. On one
event of probability one, it agrees at every positive time with the base
construction at the sampled initial state and with the actual left limit.

The signed marked increment uses the same active-set, cutoff and rate
acceptance rule as the base frozen process. No Dynkin formula is asserted.
-/

noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology

namespace CarryingCapacity.InitialFrozenPredictable
open CommonInitialNoise PredictableSets PredictableStepApproximation

variable {A J E : Type*} [MeasurableSpace A] [Fintype J] [DecidableEq E]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ) (initial : A → E)

/-- A fixed fallback makes the entire version predictable, including exceptional
samples and nonpositive times. Positive-time values identify the actual left limit. -/
def preState (C : ℝ) (e : E) (p : Sample A J) (t : ℝ) : E :=
  pastLimit (fun s p => process active jump rate initial C p s) e p t

theorem measurable_preState (hinit : Measurable initial) (C : ℝ) (e : E) :
    Measurable[predictable (filtration A J)]
      (fun p : Sample A J × (ℝ × ℝ) => preState active jump rate initial C e p.1 p.2.1) :=
  measurable_pastLimit (filtration A J) _
    (fun s _ => measurable_process_at active jump rate initial hinit C s) e

omit [MeasurableSpace A] [Fintype J] [Countable E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [BorelSpace E] in
theorem preState_nonpositive (C : ℝ) (e : E) (p : Sample A J) (t : ℝ) (ht : t ≤ 0) :
    preState active jump rate initial C e p t = e :=
  pastLimit_nonpositive _ e p t ht

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
/-- One product-law event identifies every positive-time version with the
base pre-jump state at the actually sampled initial state. -/
theorem ae_preState_eq_base (μ : Measure A) : ∀ᵐ p ∂law μ J,
    ∀ C e t, 0 < t → preState active jump rate initial C e p t =
      FrozenPredictableIntegrand.preState active jump rate C (initial p.1) p.2 t := by
  filter_upwards [ae_noise μ
    (FrozenPredictableIntegrand.ae_tendsto_preState active jump rate)] with p hp
  intro C e t ht
  exact pastLimit_eq_of_tendsto _ e p t ht _ (hp C (initial p.1) t ht)

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
/-- The actual initialized path is constant on a left interval with value equal
to its constructed predictable pre-jump state, simultaneously at all positive times. -/
theorem ae_process_eq_preState_on_left (μ : Measure A) : ∀ᵐ p ∂law μ J,
    ∀ C e t, 0 < t → ∃ b, b < t ∧ ∀ s ∈ Ico b t,
      process active jump rate initial C p s = preState active jump rate initial C e p t := by
  filter_upwards [ae_preState_eq_base active jump rate initial μ,
    ae_noise μ (FrozenPredictableIntegrand.ae_process_eq_preState_on_left active jump rate)]
    with p he hp
  intro C e t ht
  rw [he C e t ht]
  exact hp C (initial p.1) t ht

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
theorem ae_tendsto_preState (μ : Measure A) : ∀ᵐ p ∂law μ J,
    ∀ C e t, 0 < t → Tendsto (process active jump rate initial C p) (𝓝[<] t)
      (𝓝 (preState active jump rate initial C e p t)) := by
  filter_upwards [ae_preState_eq_base active jump rate initial μ,
    ae_noise μ (FrozenPredictableIntegrand.ae_tendsto_preState active jump rate)] with p he hp
  intro C e t ht
  rw [he C e t ht]
  exact hp C (initial p.1) t ht

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
theorem ae_preState_eq_leftLim (μ : Measure A) : ∀ᵐ p ∂law μ J,
    ∀ C e t, 0 < t → preState active jump rate initial C e p t =
      Function.leftLim (process active jump rate initial C p) t := by
  filter_upwards [ae_tendsto_preState active jump rate initial μ] with p hp
  intro C e t ht
  exact (leftLim_eq_of_tendsto (neBot_iff.mp inferInstance) (hp C e t ht)).symm

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
theorem ae_preState_mem_or_eq_initial (μ : Measure A) : ∀ᵐ p ∂law μ J,
    ∀ C e t, 0 < t →
      preState active jump rate initial C e p t ∈ Freezing.oneStepEnlargement active jump ∨
        preState active jump rate initial C e p t = initial p.1 := by
  filter_upwards [ae_preState_eq_base active jump rate initial μ,
    ae_noise μ (FrozenPredictableIntegrand.ae_preState_mem_or_eq_initial active jump rate)]
    with p he hp
  intro C e t ht
  rw [he C e t ht]
  exact hp C (initial p.1) t ht

/-- Measurable functions of pre-jump state and positive-time mark are predictable. -/
theorem measurable_marked_function {V : Type*} [MeasurableSpace V]
    (hinit : Measurable initial) (C : ℝ) (e : E) (f : E × ℝ → V)
    (hf : Measurable f) (v : V) :
    Measurable[predictable (filtration A J)]
      (fun p : Sample A J × (ℝ × ℝ) => if 0 < p.2.1 then
        f (preState active jump rate initial C e p.1 p.2.1, p.2.2) else v) := by
  classical
  letI : MeasurableSpace (Sample A J × (ℝ × ℝ)) := predictable (filtration A J)
  have hm : Measurable (fun p : Sample A J × (ℝ × ℝ) => if 0 < p.2.1 then
      f (preState active jump rate initial C e p.1 p.2.1, positiveHeight p) else v) :=
    (hf.comp ((measurable_preState active jump rate initial hinit C e).prodMk
      (measurable_positiveHeight (filtration A J)))).ite
        (measurableSet_positive (filtration A J)) measurable_const
  convert hm using 1
  funext p
  by_cases hp : 0 < p.2.1 <;> simp [positiveHeight, hp]

/-- The signed test-function increment with the actual frozen acceptance rule. -/
def jumpIncrement (C : ℝ) (e : E) (V : E → ℝ) (j : J)
    (p : Sample A J × (ℝ × ℝ)) : ℝ :=
  if 0 < p.2.1 ∧ preState active jump rate initial C e p.1 p.2.1 ∈ active ∧
      p.2.2 ≤ C ∧ p.2.2 ≤ rate j (preState active jump rate initial C e p.1 p.2.1)
    then V (jump j (preState active jump rate initial C e p.1 p.2.1)) -
      V (preState active jump rate initial C e p.1 p.2.1)
    else 0

theorem measurable_jumpIncrement (hinit : Measurable initial)
    (C : ℝ) (e : E) (V : E → ℝ) (j : J) :
    Measurable[predictable (filtration A J)]
      (jumpIncrement active jump rate initial C e V j) := by
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
  have hm := measurable_marked_function active jump rate initial hinit C e _ hf (0 : ℝ)
  convert hm using 1
  funext p
  simp only [jumpIncrement, ite_and]

theorem stronglyMeasurable_jumpIncrement (hinit : Measurable initial)
    (C : ℝ) (e : E) (V : E → ℝ) (j : J) :
    StronglyMeasurable[predictable (filtration A J)]
      (jumpIncrement active jump rate initial C e V j) :=
  (measurable_jumpIncrement active jump rate initial hinit C e V j).stronglyMeasurable

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
/-- The initialized signed integrand is the original actual frozen integrand
at the sampled initial state, simultaneously for every marked point and test function. -/
theorem ae_jumpIncrement_eq_base (μ : Measure A) : ∀ᵐ p ∂law μ J,
    ∀ C e V j t u,
      jumpIncrement active jump rate initial C e V j (p, (t, u)) =
        FrozenPredictableIntegrand.jumpIncrement active jump rate C (initial p.1) V j
          (p.2, (t, u)) := by
  filter_upwards [ae_preState_eq_base active jump rate initial μ] with p hp
  intro C e V j t u
  by_cases ht : 0 < t
  · simp only [jumpIncrement, FrozenPredictableIntegrand.jumpIncrement, hp C e t ht]
  · simp only [jumpIncrement, FrozenPredictableIntegrand.jumpIncrement, ht, false_and, if_false]

end CarryingCapacity.InitialFrozenPredictable
