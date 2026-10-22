import CarryingCapacity.TimeDependentPredictable

/-!
# Predictable time-dependent increments with an arbitrary initial record

Strict-past approximations of the actual initialized process define a
predictable pre-jump state on every sample. Its fallback at nonpositive times
is fixed, as required by the positive-time predictable sigma algebra. On one
event of probability one, it agrees at every positive time with the base
construction at the sampled initial state and with the actual left limit.

The signed marked increment uses the same active-set, cutoff and event-time rate
acceptance rule as the base frozen process. No Dynkin formula is asserted.
-/

noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology

namespace CarryingCapacity.TimeDependentInitial
open CommonInitialNoise PredictableSets PredictableStepApproximation PredictableTime

variable {A J E : Type*} [MeasurableSpace A] [Fintype J] [DecidableEq E]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ) (initial : A → E)

/-- The actual event-time recursion at the independently sampled initial state. -/
def process (C : ℝ) (p : Sample A J) (t : ℝ) : E :=
  TimeDependentFrozenProcess.process active jump rate C (initial p.1) p.2 t

omit [TopologicalSpace E] [PolishSpace E] [BorelSpace E] in
/-- Joint measurability of the actual initialized process. -/
theorem measurable_process (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) : Measurable
    (fun p : Sample A J × ℝ => process active jump rate initial C p.1 p.2) :=
  (TimeDependentFrozenProcess.measurable_runBox active jump rate hRate).comp
    ((measurable_fst.snd.prodMk (measurable_snd.prodMk measurable_const)).prodMk
      (hinit.comp measurable_fst.fst))

omit [TopologicalSpace E] [PolishSpace E] [BorelSpace E] in
/-- The actual path uses only the known initial record and arrived marks. -/
theorem measurable_process_at (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C t : ℝ) :
    Measurable[filtration A J t] (fun p => process active jump rate initial C p t) :=
  TimeDependentHistory.measurable_initial_process_at active jump rate hRate initial hinit C t

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E] in
/-- The prescribed initial value holds for every cutoff on one event. -/
theorem ae_process_zero (μ : Measure A) : ∀ᵐ p ∂law μ J, ∀ C,
    process active jump rate initial C p 0 = initial p.1 := by
  filter_upwards [ae_noise μ (TimeDependentFrozenProcess.ae_process_zero active jump rate)]
    with p hp
  exact fun C => hp C (initial p.1)

/-- A fixed fallback makes the entire version predictable, including exceptional
samples and nonpositive times. Positive-time values identify the actual left limit. -/
def preState (C : ℝ) (e : E) (p : Sample A J) (t : ℝ) : E :=
  pastLimit (fun s p => process active jump rate initial C p s) e p t

theorem measurable_preState (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) :
    Measurable[predictable (filtration A J)]
      (fun p : Sample A J × (ℝ × ℝ) => preState active jump rate initial C e p.1 p.2.1) :=
  measurable_pastLimit (filtration A J) _
    (fun s _ => measurable_process_at active jump rate initial hRate hinit C s) e

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
      TimeDependentPredictable.preState active jump rate C (initial p.1) p.2 t := by
  filter_upwards [ae_noise μ
    (TimeDependentPredictable.ae_tendsto_preState active jump rate)] with p hp
  intro C e t ht
  exact pastLimit_eq_of_tendsto _ e p t ht _ (hp C (initial p.1) t ht)

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
/-- The actual initialized path is constant on a left interval with value equal
to its constructed predictable pre-jump state, simultaneously at all positive times. -/
theorem ae_process_eq_preState_on_left (μ : Measure A) : ∀ᵐ p ∂law μ J,
    ∀ C e t, 0 < t → ∃ b, b < t ∧ ∀ s ∈ Ico b t,
      process active jump rate initial C p s = preState active jump rate initial C e p t := by
  filter_upwards [ae_preState_eq_base active jump rate initial μ,
    ae_noise μ (TimeDependentPredictable.ae_process_eq_preState_on_left active jump rate)]
    with p he hp
  intro C e t ht
  rw [he C e t ht]
  exact hp C (initial p.1) t ht

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
theorem ae_tendsto_preState (μ : Measure A) : ∀ᵐ p ∂law μ J,
    ∀ C e t, 0 < t → Tendsto (process active jump rate initial C p) (𝓝[<] t)
      (𝓝 (preState active jump rate initial C e p t)) := by
  filter_upwards [ae_preState_eq_base active jump rate initial μ,
    ae_noise μ (TimeDependentPredictable.ae_tendsto_preState active jump rate)] with p he hp
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

/-- The signed test-function increment with the actual frozen acceptance rule. -/
def jumpIncrement (C : ℝ) (e : E) (V : E → ℝ) (j : J)
    (p : Sample A J × (ℝ × ℝ)) : ℝ :=
  if 0 < p.2.1 ∧ preState active jump rate initial C e p.1 p.2.1 ∈ active ∧
      p.2.2 ≤ C ∧ p.2.2 ≤ rate j p.2.1 (preState active jump rate initial C e p.1 p.2.1)
    then V (jump j (preState active jump rate initial C e p.1 p.2.1)) -
      V (preState active jump rate initial C e p.1 p.2.1)
    else 0

theorem measurable_jumpIncrement (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (j : J) :
    Measurable[predictable (filtration A J)]
      (jumpIncrement active jump rate initial C e V j) := by
  let F := filtration A J
  have hz := measurable_preState active jump rate initial hRate hinit C e
  have hr := measurable_evaluation F (rate j) (hRate j) _ hz
  have hh := measurable_positiveHeight F
  have hd := ((measurable_of_countable (fun y => V (jump j y))).comp hz).sub
    ((measurable_of_countable V).comp hz)
  have hm : Measurable[predictable F] (fun p : Sample A J × (ℝ × ℝ) =>
      if 0 < p.2.1 ∧ preState active jump rate initial C e p.1 p.2.1 ∈ active ∧
          positiveHeight p ≤ C ∧ positiveHeight p ≤ rate j (positiveTime p)
            (preState active jump rate initial C e p.1 p.2.1)
      then V (jump j (preState active jump rate initial C e p.1 p.2.1)) -
        V (preState active jump rate initial C e p.1 p.2.1) else 0) := by
    exact hd.ite ((measurableSet_positive F).inter
      (((Finset.measurableSet active).preimage hz).inter
        ((measurableSet_le hh measurable_const).inter (measurableSet_le hh hr)))) measurable_const
  convert hm using 1
  funext p
  by_cases ht : 0 < p.2.1 <;> simp [jumpIncrement, positiveHeight, positiveTime, ht]


theorem stronglyMeasurable_jumpIncrement (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial)
    (C : ℝ) (e : E) (V : E → ℝ) (j : J) :
    StronglyMeasurable[predictable (filtration A J)]
      (jumpIncrement active jump rate initial C e V j) :=
  (measurable_jumpIncrement active jump rate initial hRate hinit C e V j).stronglyMeasurable

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
/-- The initialized signed integrand is the original actual frozen integrand
at the sampled initial state, simultaneously for every marked point and test function. -/
theorem ae_jumpIncrement_eq_base (μ : Measure A) : ∀ᵐ p ∂law μ J,
    ∀ C e V j t u,
      jumpIncrement active jump rate initial C e V j (p, (t, u)) =
        TimeDependentPredictable.jumpIncrement active jump rate C (initial p.1) V j
          (p.2, (t, u)) := by
  filter_upwards [ae_preState_eq_base active jump rate initial μ] with p hp
  intro C e V j t u
  by_cases ht : 0 < t
  · simp only [jumpIncrement, TimeDependentPredictable.jumpIncrement, hp C e t ht]
  · simp only [jumpIncrement, TimeDependentPredictable.jumpIncrement, ht, false_and, if_false]

end CarryingCapacity.TimeDependentInitial
