import CarryingCapacity.FrozenForwardMinimality
import CarryingCapacity.TimeDependentFrozenLawLimit

/-!
# Forward-law uniqueness from actual nonexplosion

Every probability-valued weak solution dominates the actual frozen masses
inside each finite active set. Genuine exit exhaustion gives convergence to
the constructed global law. Since both laws have total mass one, pointwise
atomic domination forces equality. This proves uniqueness without assuming
a Markov property, jump-series formula, or law-identification conclusion.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace CarryingCapacity.TimeDependentForwardUniqueness
open CommonInitialNoise LyapunovLocalization TimeDependentLocalization
open FiniteJumpForward TimeDependentFrozenLawLimit

variable {E J : Type*} [DecidableEq E] [Fintype J] [Countable E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (hbounded : ∀ n : ℕ, ∃ C : ℝ,
    ∀ x ∈ active V hfinite n, ∀ j t, rate j t x ≤ C)
  (e : E) (μ : Measure E) [IsProbabilityMeasure μ]
  (hRate : ∀ j x, Measurable (fun t => rate j t x))
  (hfiber : ∀ j : J, ∀ x : E, {y | jump j y = x}.Finite)
  (hq : ∀ j t x, 0 ≤ t → 0 ≤ rate j t x)
  (hexhaust : ∀ᵐ p ∂law μ J, ∀ S : ℝ≥0, ∃ n,
    (S : ℝ≥0∞) < TimeDependentLocalization.exit V hfinite jump rate hbounded id n p)
  (T : ℝ) (hT : 0 ≤ T)
  (hCont : ∀ j x, ContinuousOn (fun t => rate j t x) (Icc 0 T))

include e hRate hfiber hq hexhaust hT hCont

/-- Any probability-valued weak forward solution is the actual global
pushforward law. No moment bound on the candidate is needed for uniqueness. -/
theorem globalLaw_eq_solution (p : ℝ → Measure E)
    (hp : IsSolution jump rate μ p T) (t : ℝ) (ht : t ∈ Icc 0 T) :
    globalLaw V hfinite jump rate hbounded e μ t = p t := by
  letI : IsProbabilityMeasure (p t) := hp.probability t ht
  letI : IsProbabilityMeasure (globalLaw V hfinite jump rate hbounded e μ t) :=
    globalLaw_probability V hfinite jump rate hbounded e μ hRate t
  apply probability_eq_of_real_atom_le
  intro x
  obtain ⟨n, hn⟩ := exists_active V hfinite x
  apply le_of_tendsto (tendsto_mass V hfinite jump rate hbounded e μ hRate hexhaust t ht.1 x)
  filter_upwards [eventually_ge_atTop n] with m hm
  have hx : x ∈ active V hfinite m := active_mono V hfinite hm hn
  exact FrozenForwardMinimality.mass_le_solution (active V hfinite m) jump rate hfiber
    μ p T hT hp hRate hCont (TimeDependentLocalization.rateBound V hfinite rate hbounded m)
    (TimeDependentLocalization.rateBound_pos V hfinite rate hbounded m).le hq
    (fun y hy j s _ => TimeDependentLocalization.rate_le_bound V hfinite rate hbounded m y hy j s)
    e t ht ⟨x,hx⟩

/-- Two probability-valued weak forward solutions with the same initial
law coincide at every time, as a consequence of the actual construction. -/
theorem solution_unique (p r : ℝ → Measure E)
    (hp : IsSolution jump rate μ p T) (hr : IsSolution jump rate μ r T)
    (t : ℝ) (ht : t ∈ Icc 0 T) : p t = r t :=
  (globalLaw_eq_solution V hfinite jump rate hbounded e μ hRate hfiber hq hexhaust T hT hCont p hp t ht).symm.trans
    (globalLaw_eq_solution V hfinite jump rate hbounded e μ hRate hfiber hq hexhaust T hT hCont r hr t ht)

end CarryingCapacity.TimeDependentForwardUniqueness
