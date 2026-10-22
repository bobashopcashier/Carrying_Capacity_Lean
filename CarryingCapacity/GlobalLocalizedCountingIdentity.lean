import CarryingCapacity.GlobalLocalizedProcess
import CarryingCapacity.InitialFrozenCountingIdentity

/-!
# The global accepted-increment counting equation

The global pre-jump state is a measurable strict-past limit of the actual
adapted global path. Before a localized exit it agrees with the frozen
pre-state and belongs to that level's active set. Consequently the localized
acceptance rule agrees with the unrestricted rate threshold on the whole
time-height horizon. Exhaustion then transfers actual pathwise integrability
and the test-function counting equation, with no freezing indicator or height
cutoff in the global integrand.

Exhaustion is a premise about the genuine constructed exits, supplied by the
separate Lyapunov nonexplosion theorem. No counting equation, increment
agreement, or pathwise uniqueness conclusion is assumed.
-/

noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped Classical ENNReal NNReal Topology BigOperators

namespace CarryingCapacity.GlobalLocalizedCountingIdentity
open CommonInitialNoise LyapunovLocalization PredictableSets PredictableStepApproximation

variable {A E J : Type*} [DecidableEq E] [Fintype J]
  [TopologicalSpace E] [PolishSpace E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → E → ℝ) (initial : A → E) (e : E)

/-- The global predictable pre-jump version, with a fixed nonpositive-time fallback. -/
def preState (p : Sample A J) (t : ℝ) : E :=
  pastLimit (fun s p => GlobalLocalizedProcess.process V hfinite jump rate initial e p s) e p t

/-- The genuine rate-threshold increment, without an active region or cap. -/
def jumpIncrement (f : E → ℝ) (j : J) (p : Sample A J × (ℝ × ℝ)) : ℝ :=
  if 0 < p.2.1 ∧ p.2.2 ≤ rate j (preState V hfinite jump rate initial e p.1 p.2.1)
    then f (jump j (preState V hfinite jump rate initial e p.1 p.2.1)) -
      f (preState V hfinite jump rate initial e p.1 p.2.1)
    else 0

/-- Restriction to a deterministic time horizon, with no height restriction. -/
def horizonIncrement (f : E → ℝ) (j : J) (T : ℝ) : Sample A J × (ℝ × ℝ) → ℝ :=
  (rectangle univ 0 T univ).indicator (jumpIncrement V hfinite jump rate initial e f j)

section Measurability
variable [MeasurableSpace A] [Countable E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [BorelSpace E] (hinit : Measurable initial)
include hinit

theorem measurable_preState : Measurable[predictable (filtration A J)]
    (fun p : Sample A J × (ℝ × ℝ) => preState V hfinite jump rate initial e p.1 p.2.1) :=
  measurable_pastLimit (filtration A J) _
    (fun s _ => GlobalLocalizedProcess.measurable_process_at V hfinite jump rate initial e hinit s) e

theorem measurable_jumpIncrement (f : E → ℝ) (j : J) :
    Measurable[predictable (filtration A J)] (jumpIncrement V hfinite jump rate initial e f j) := by
  letI : MeasurableSpace (Sample A J × (ℝ × ℝ)) := predictable (filtration A J)
  have hz := measurable_preState V hfinite jump rate initial e hinit
  have hr := (measurable_of_countable (rate j)).comp hz
  have hf := ((measurable_of_countable (fun x => f (jump j x))).comp hz).sub
    ((measurable_of_countable f).comp hz)
  have hm : Measurable (fun p : Sample A J × (ℝ × ℝ) =>
      if 0 < p.2.1 ∧ positiveHeight p ≤ rate j (preState V hfinite jump rate initial e p.1 p.2.1)
      then f (jump j (preState V hfinite jump rate initial e p.1 p.2.1)) -
        f (preState V hfinite jump rate initial e p.1 p.2.1) else 0) :=
    hf.ite ((measurableSet_positive (filtration A J)).inter
      (measurableSet_le (measurable_positiveHeight (filtration A J)) hr)) measurable_const
  convert hm using 1
  funext p
  by_cases ht : 0 < p.2.1 <;> simp [jumpIncrement, positiveHeight, ht]

theorem measurable_horizonIncrement (f : E → ℝ) (j : J) (T : ℝ) :
    Measurable[predictable (filtration A J)]
      (horizonIncrement V hfinite jump rate initial e f j T) :=
  (measurable_jumpIncrement V hfinite jump rate initial e hinit f j).indicator
    (measurableSet_predictable_rectangle (filtration A J) 0 T le_rfl
      univ MeasurableSet.univ univ MeasurableSet.univ)

end Measurability

variable [MeasurableSpace A] (μ : Measure A)

/-- Under actual exit exhaustion, the predictable version is the actual left
limit of the global path at every positive time, on one probability-one event. -/
theorem ae_tendsto_preState
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rate initial n p) :
    ∀ᵐ p ∂law μ J, ∀ t : ℝ, 0 < t → Tendsto
      (GlobalLocalizedProcess.process V hfinite jump rate initial e p)
      (𝓝[<] t) (𝓝 (preState V hfinite jump rate initial e p t)) := by
  filter_upwards [GlobalLocalizedProcess.ae_process_cadlag
    V hfinite jump rate initial e μ hexhaust] with p hp
  intro t ht
  obtain ⟨y, hy⟩ := hp.2 t ht
  have he : preState V hfinite jump rate initial e p t = y :=
    pastLimit_eq_of_tendsto _ e p t ht y hy
  rwa [he]

/-- Strictly before a level's exit, global pre-states agree with its actual
frozen pre-states and remain in that active region. -/
theorem ae_preState_eq_level : ∀ᵐ p ∂law μ J, ∀ n : ℕ, ∀ T : ℝ≥0,
    (T : ℝ≥0∞) < exit V hfinite jump rate initial n p →
    ∀ t ∈ Ioc (0 : ℝ) T,
      preState V hfinite jump rate initial e p t =
        InitialFrozenPredictable.preState (active V hfinite n) jump rate initial
          (rateBound V hfinite rate n) e p t ∧
      preState V hfinite jump rate initial e p t ∈ active V hfinite n := by
  have hl : ∀ n : ℕ, ∀ᵐ p ∂law μ J, ∀ C e t, 0 < t → ∃ b, b < t ∧ ∀ s ∈ Ico b t,
      CommonInitialNoise.process (active V hfinite n) jump rate initial C p s =
        InitialFrozenPredictable.preState (active V hfinite n) jump rate initial C e p t :=
    fun n => InitialFrozenPredictable.ae_process_eq_preState_on_left
      (active V hfinite n) jump rate initial μ
  filter_upwards [GlobalLocalizedProcess.ae_eq_path V hfinite jump rate initial e μ,
    ae_all_iff.mpr hl] with p hp hleft
  intro n T hT t ht
  obtain ⟨b, hb, hy⟩ := hleft n (rateBound V hfinite rate n) e t ht.1
  have hb' : max b 0 < t := max_lt hb ht.1
  have hbefore (s : ℝ) (hs : s ≤ T) : ENNReal.ofReal s < exit V hfinite jump rate initial n p :=
    (show ENNReal.ofReal s ≤ (T : ℝ≥0∞) by
      simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hs).trans_lt hT
  have he : preState V hfinite jump rate initial e p t =
      InitialFrozenPredictable.preState (active V hfinite n) jump rate initial
        (rateBound V hfinite rate n) e p t := by
    apply pastLimit_eq_of_left_constant _ e p t ht.1 (max b 0) hb'
    intro s hs
    exact (hp n s ((le_max_right b 0).trans hs.1)
      (hbefore s (hs.2.le.trans ht.2)).le).trans
        (hy s ⟨(le_max_left b 0).trans hs.1, hs.2⟩)
  refine ⟨he, ?_⟩
  rw [he, ← hy (max b 0) ⟨le_max_left _ _, hb'⟩]
  exact CommonFrozenExit.process_mem_before_firstExit (active V hfinite n) jump rate
    (rateBound V hfinite rate n) (initial p.1) p.2 (le_max_right _ _)
      (hbefore (max b 0) (hb'.le.trans ht.2))

omit μ [PolishSpace E] [MeasurableSpace A] in
theorem horizonIncrement_apply (f : E → ℝ) (j : J) (T : ℝ)
    (p : Sample A J) (q : ℝ × ℝ) :
    horizonIncrement V hfinite jump rate initial e f j T (p,q) =
      if q.1 ∈ Ioc 0 T ∧ q.2 ≤ rate j (preState V hfinite jump rate initial e p q.1)
      then f (jump j (preState V hfinite jump rate initial e p q.1)) -
        f (preState V hfinite jump rate initial e p q.1) else 0 := by
  by_cases ht : q.1 ∈ Ioc 0 T
  · simp [horizonIncrement, rectangle, jumpIncrement, Set.indicator_apply, ht, ht.1]
  · have ht' : ¬ (0 < q.1 ∧ q.1 ≤ T) := ht
    simp [horizonIncrement, rectangle, Set.indicator_apply, ht']

/-- On a horizon before a genuine exit, the global and localized integrands
are equal at every time-height pair, not merely almost everywhere. -/
theorem ae_horizonIncrement_eq_level : ∀ᵐ p ∂law μ J, ∀ n : ℕ, ∀ T : ℝ≥0,
    (T : ℝ≥0∞) < exit V hfinite jump rate initial n p →
    ∀ (f : E → ℝ) (j : J),
      (fun q => horizonIncrement V hfinite jump rate initial e f j T (p,q)) =
        (fun q => InitialFrozenCompensation.horizonIncrement (active V hfinite n)
          jump rate initial (rateBound V hfinite rate n) e f j T (p,q)) := by
  filter_upwards [ae_preState_eq_level V hfinite jump rate initial e μ] with p hp
  intro n T hT f j
  funext q
  rw [horizonIncrement_apply,
    InitialFrozenCompensation.horizonIncrement_eq_localizedIncrement]
  dsimp only [FrozenIntensity.localizedIncrement]
  by_cases ht : q.1 ∈ Ioc (0 : ℝ) T
  · obtain ⟨he, ha⟩ := hp n T hT q.1 ht
    have ha' : InitialFrozenPredictable.preState (active V hfinite n) jump rate initial
        (rateBound V hfinite rate n) e p q.1 ∈ active V hfinite n := he ▸ ha
    have hcap := rate_le_bound V hfinite rate n _ ha' j
    rw [he]
    have hh : q.2 ≤ rateBound V hfinite rate n ∧ q.2 ≤ rate j
        (InitialFrozenPredictable.preState (active V hfinite n) jump rate initial
          (rateBound V hfinite rate n) e p q.1) ↔ q.2 ≤ rate j
        (InitialFrozenPredictable.preState (active V hfinite n) jump rate initial
          (rateBound V hfinite rate n) e p q.1) :=
      ⟨And.right, fun h => ⟨h.trans hcap, h⟩⟩
    simp only [ht, ha', true_and, hh]
  · simp only [ht, false_and, ↓reduceIte]

/-- Finite-horizon pathwise integrability is inherited from the actual finite
proposal list selected by exit exhaustion. No expected-activity bound is needed. -/
theorem ae_integrable_horizonIncrement
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rate initial n p) :
    ∀ᵐ p ∂law μ J, ∀ (T : ℝ≥0) (f : E → ℝ) (j : J),
      Integrable (fun q => horizonIncrement V hfinite jump rate initial e f j T (p,q))
        (MarkedNoise.countingMeasure j p.2) := by
  have hi := ae_all_iff.mpr (fun n : ℕ =>
    InitialFrozenCountingIdentity.ae_integrable_horizonIncrement
      (active V hfinite n) jump rate initial μ)
  filter_upwards [ae_horizonIncrement_eq_level V hfinite jump rate initial e μ, hi, hexhaust]
    with p he hi hx
  intro T f j
  obtain ⟨n, hn⟩ := hx T
  rw [he n T hn f j]
  exact hi n (rateBound V hfinite rate n) e T f j

/-- The global path solves the actual accepted-increment counting equation
for every real test function, with no active-set indicator or cutoff remaining. -/
theorem ae_testFunction_counting_identity (f : E → ℝ)
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rate initial n p) :
    ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0,
      f (GlobalLocalizedProcess.process V hfinite jump rate initial e p T) -
        f (initial p.1) =
      ∑ j : J, ∫ q, horizonIncrement V hfinite jump rate initial e f j T (p,q)
        ∂MarkedNoise.countingMeasure j p.2 := by
  have hid := ae_all_iff.mpr (fun n : ℕ =>
    InitialFrozenCountingIdentity.ae_testFunction_counting_identity
      (active V hfinite n) jump rate initial μ f)
  have hz := ae_all_iff.mpr (fun n : ℕ =>
    CommonInitialNoise.ae_process_zero (active V hfinite n) jump rate initial μ)
  filter_upwards [GlobalLocalizedProcess.ae_eq_path V hfinite jump rate initial e μ,
    ae_horizonIncrement_eq_level V hfinite jump rate initial e μ, hid, hz, hexhaust]
    with p hp he hid hz hx
  intro T
  obtain ⟨n, hn⟩ := hx T
  rw [hp n T T.coe_nonneg (by simpa only [ENNReal.ofReal_coe_nnreal] using hn.le)]
  change f (CommonInitialNoise.process (active V hfinite n) jump rate initial
    (rateBound V hfinite rate n) p T) - f (initial p.1) = _
  rw [← hz n (rateBound V hfinite rate n), hid n (rateBound V hfinite rate n) e T]
  apply Finset.sum_congr rfl
  intro j _
  rw [he n T hn f j]

end CarryingCapacity.GlobalLocalizedCountingIdentity
