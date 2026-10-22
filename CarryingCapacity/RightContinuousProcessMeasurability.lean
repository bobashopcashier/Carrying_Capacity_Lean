import CarryingCapacity.PredictableStepApproximation
import CarryingCapacity.StoppedPathMeasurability
import CarryingCapacity.DiscreteCausalUniqueness
import Mathlib.MeasureTheory.Function.Floor

/-!
# Joint measurability from right-continuous sample paths

Countable right-grid observations define a jointly measurable version. On the
single event of right-continuity it equals the original process at every
nonnegative time. This justifies actual stopped-supremum measurability without
adding joint measurability as an assumption on a competing solution.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical Topology ENNReal

namespace CarryingCapacity.RightContinuousProcessMeasurability

def rightGrid (n : ℕ) (t : ℝ) : ℝ := (⌈t * (n + 1)⌉₊ : ℝ) / (n + 1)

theorem rightGrid_nonnegative (n : ℕ) (t : ℝ) : 0 ≤ rightGrid n t := by
  unfold rightGrid
  positivity

theorem le_rightGrid (n : ℕ) (t : ℝ) : t ≤ rightGrid n t := by
  unfold rightGrid
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr (Nat.le_ceil _)

theorem tendsto_rightGrid (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n => rightGrid n t) atTop (𝓝[≥] t) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((tendsto_nat_ceil_mul_div_atTop ht).comp hn)
    (Eventually.of_forall (fun n => le_rightGrid n t))

/-- The manuscript's nonnegative-time stopping sublevels already imply
ambient measurability of the extended stopping time. -/
theorem measurable_of_stopping_sublevels {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ mΩ) (σ : Ω → ℝ≥0∞)
    (hσ : ∀ t : ℝ, 0 ≤ t → MeasurableSet[F t] {ω | σ ω ≤ ENNReal.ofReal t}) :
    Measurable σ := by
  apply measurable_of_Iic
  intro a
  by_cases ha : a = ⊤
  · simpa only [ha,Iic_top,preimage_univ] using MeasurableSet.univ
  · have hm := (F.le a.toReal) _ (hσ a.toReal ENNReal.toReal_nonneg)
    simpa only [ENNReal.ofReal_toReal ha] using hm

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

def rightStep (X : ℝ → Ω → E) (e : E) (n : ℕ) (p : Ω × ℝ) : E :=
  if 0 ≤ p.2 then X (rightGrid n p.2) p.1 else e

theorem measurable_rightStep (X : ℝ → Ω → E)
    (hX : ∀ t, 0 ≤ t → Measurable (X t)) (e : E) (n : ℕ) :
    Measurable (rightStep X e n) := by
  have hm : Measurable (fun p : Ω × ℕ => X ((p.2 : ℝ) / (n + 1)) p.1) :=
    measurable_from_prod_countable (fun k : ℕ => hX ((k : ℝ) / (n + 1)) (by positivity))
  have hg : Measurable (fun p : Ω × ℝ => ⌈p.2 * (n + 1)⌉₊) :=
    (measurable_snd.mul_const _).nat_ceil
  exact (hm.comp (measurable_fst.prodMk hg)).ite
    (measurableSet_le measurable_const measurable_snd) measurable_const

variable [TopologicalSpace E] [PolishSpace E] [BorelSpace E]

/-- A jointly measurable candidate, defined even on exceptional paths where
the grid observations have no limit. -/
def version (X : ℝ → Ω → E) (e : E) (ω : Ω) (t : ℝ) : E :=
  letI : Nonempty E := ⟨e⟩
  limUnder atTop (fun n : ℕ => rightStep X e n (ω,t))

theorem measurable_version (X : ℝ → Ω → E)
    (hX : ∀ t, 0 ≤ t → Measurable (X t)) (e : E) :
    Measurable (fun p : Ω × ℝ => version X e p.1 p.2) := by
  letI : Nonempty E := ⟨e⟩
  exact (StronglyMeasurable.limUnder (l := atTop)
    (fun n => (measurable_rightStep X hX e n).stronglyMeasurable)).measurable

omit [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] in
theorem version_eq (X : ℝ → Ω → E) (e : E) (ω : Ω) (t : ℝ) (ht : 0 ≤ t)
    (hright : ContinuousWithinAt (fun s => X s ω) (Ici t) t) :
    version X e ω t = X t ω := by
  unfold version
  simp only [rightStep,ht,if_true]
  exact (Filter.Tendsto.comp hright (tendsto_rightGrid t ht)).limUnder_eq

omit [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] in
theorem version_eq_default (X : ℝ → Ω → E) (e : E) (ω : Ω) (t : ℝ) (ht : t < 0) :
    version X e ω t = e := by
  unfold version
  simp only [rightStep,not_le.mpr ht,if_false]
  exact tendsto_const_nhds.limUnder_eq

omit [MeasurableSpace E] [BorelSpace E] in
/-- Equality is simultaneous over all nonnegative times, rather than a
separate almost-sure equality at each fixed time. -/
theorem ae_version_eq (X : ℝ → Ω → E) (e : E) (P : Measure Ω)
    (hright : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t →
      ContinuousWithinAt (fun s => X s ω) (Ici t) t) :
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → version X e ω t = X t ω := by
  filter_upwards [hright] with ω hω
  exact fun t ht => version_eq X e ω t ht (hω t ht)

omit [MeasurableSpace Ω] [MeasurableSpace E] [TopologicalSpace E] [PolishSpace E]
  [BorelSpace E] in
theorem stopped_eq_of_eq_nonnegative (f g : ℝ → E) (σ : ℝ≥0∞)
    (he : ∀ t, 0 ≤ t → f t = g t) (t : ℝ) (ht : 0 ≤ t) :
    CommonFrozenExit.stopped σ f t = CommonFrozenExit.stopped σ g t := by
  by_cases hσ : σ = ⊤
  · simpa only [CommonFrozenExit.stopped,hσ,if_true] using he t ht
  · simpa only [CommonFrozenExit.stopped,hσ,if_false] using
      he (min t σ.toReal) (le_min ht ENNReal.toReal_nonneg)

variable [Countable E] [MeasurableSingletonClass E] [DiscreteTopology E]

/-- The genuine stopped running supremum of a countable-state candidate
is AE measurable from measurable evaluations and AE right continuity. -/
theorem aemeasurable_intervalSup_stopped (X : ℝ → Ω → E)
    (hX : ∀ t, 0 ≤ t → Measurable (X t)) (e : E) (P : Measure Ω)
    (hright : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t →
      ContinuousWithinAt (fun s => X s ω) (Ici t) t)
    (σ : Ω → ℝ≥0∞) (hσ : AEMeasurable σ P)
    (cost : E → ℝ≥0∞) (T : ℝ) (hT : 0 ≤ T) :
    AEMeasurable (fun ω => SynchronousRunningSupremum.intervalSup
      (fun t => cost (CommonFrozenExit.stopped (σ ω) (fun s => X s ω) t)) T) P := by
  have he := ae_version_eq X e P hright
  have hvright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∃ b, t < b ∧
      ∀ u ∈ Ico t b, version X e ω u = version X e ω t := by
    filter_upwards [hright,he] with ω hr hω
    intro t ht
    obtain ⟨b,hb,hlocal⟩ := DiscreteCausalUniqueness.exists_right_constant
      (fun s => X s ω) t (hr t ht)
    refine ⟨b,hb,fun u hu => ?_⟩
    rw [hω u (ht.trans hu.1),hω t ht]
    exact hlocal u hu
  have hm := StoppedPathMeasurability.aemeasurable_intervalSup_stopped
    (version X e) (measurable_version X hX e) σ P hσ hvright cost T hT
  apply hm.congr
  filter_upwards [he] with ω hω
  unfold SynchronousRunningSupremum.intervalSup
  apply iSup_congr
  intro t
  exact congrArg cost (stopped_eq_of_eq_nonnegative
    (version X e ω) (fun s => X s ω) (σ ω) hω t t.property.1)

end CarryingCapacity.RightContinuousProcessMeasurability
