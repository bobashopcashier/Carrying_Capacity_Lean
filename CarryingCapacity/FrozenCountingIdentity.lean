import CarryingCapacity.FrozenJumpIdentity
import CarryingCapacity.FrozenPredictableIntegrand

/-!
# Finite chronological sums are actual counting-measure integrals

Local finiteness supplies finite support, hence genuine Bochner integrability,
for arbitrary real weights restricted to a bounded time-height box. The
integrals are evaluated at the actual constructed atoms and then identified
with the chronological list. No stochastic integral identity is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal

namespace CarryingCapacity.FrozenCountingIdentity
open MarkedNoise ChronologicalEvents FrozenJumpIdentity

/-- An arbitrary real function is integrable against countably many atoms
when only finitely many indexed atoms have nonzero weight. -/
theorem integrable_atomic_of_finite_support {I X : Type*} [Countable I]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (a : I → X) (f : X → ℝ) (hfin : {i | f (a i) ≠ 0}.Finite) :
    Integrable f (Measure.sum (fun i => Measure.dirac (a i))) := by
  refine ⟨aestronglyMeasurable_sum_measure_iff.mpr (fun i =>
    (integrable_dirac : Integrable f (Measure.dirac (a i))).aestronglyMeasurable), ?_⟩
  rw [HasFiniteIntegral, lintegral_sum_measure]
  simp only [lintegral_dirac]
  rw [tsum_eq_sum (s := hfin.toFinset) (fun i hi => by
    have hz : f (a i) = 0 := by simpa using hi
    simp [hz])]
  simp

theorem integral_atomic_of_finite_support {I X : Type*} [Countable I]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (a : I → X) (f : X → ℝ) (hfin : {i | f (a i) ≠ 0}.Finite) :
    (∫ p, f p ∂Measure.sum (fun i => Measure.dirac (a i))) = ∑' i, f (a i) := by
  rw [integral_sum_measure (integrable_atomic_of_finite_support a f hfin)]
  simp only [integral_dirac]

variable {J : Type*} [Fintype J]

/-- Integrability is obtained from the actual finite set of atoms in the box. -/
theorem ae_integrable_box_weights : ∀ᵐ ω ∂law J,
    ∀ T C : ℝ, ∀ j : J, ∀ f : ℝ × ℝ → ℝ,
      Integrable ((Iic T ×ˢ Iic C).indicator f) (countingMeasure j ω) := by
  filter_upwards [MarkedNoise.ae_finite_total_points (J := J)] with ω hω
  intro T C j f
  apply integrable_atomic_of_finite_support
  have hsub : {p : ℕ × ℕ | ((Iic T ×ˢ Iic C).indicator f) (point j ω p) ≠ 0} ⊆
      (fun p : ℕ × ℕ => (j,p)) ⁻¹' {e : Event J | point e.1 ω e.2 ∈ Iic T ×ˢ Iic C} := by
    intro p hp
    by_contra hnot
    change point j ω p ∉ Iic T ×ˢ Iic C at hnot
    exact hp (Set.indicator_of_not_mem hnot f)
  exact ((hω T C).preimage (fun _ _ _ _ h => Prod.mk.inj h |>.2)).subset hsub

/-- The finite-list and finite-set enumerations of a duplicate-free list agree. -/
theorem sum_get_eq_sum_toFinset {I V : Type*} [DecidableEq I] [AddCommMonoid V]
    (l : List I) (hl : l.Nodup) (f : I → V) :
    (∑ n : Fin l.length, f (l.get n)) = ∑ e ∈ l.toFinset, f e := by
  rw [List.sum_toFinset f hl, ← List.sum_ofFn]
  congr 1
  change List.ofFn (f ∘ l.get) = List.map f l
  rw [← List.map_ofFn, List.ofFn_get]

/-- Every real weighted integral over the actual bounded box equals the sum
over its genuine chronological events. The weights need not be measurable:
the finite atomic restriction itself supplies Bochner integrability. -/
theorem ae_integral_box_eq_sum : ∀ᵐ ω ∂law J,
    ∀ T C : ℝ, ∀ f : J → (ℝ × ℝ) → ℝ,
      (∑ j : J, ∫ p, (Iic T ×ˢ Iic C).indicator (f j) p ∂countingMeasure j ω) =
        ∑ n : Fin (boxedList (ω,T,C)).length,
          let e := (boxedList (ω,T,C)).get n
          f e.1 (point e.1 ω e.2) := by
  filter_upwards [ae_boxedList_mem (J := J), MarkedNoise.ae_finite_total_points (J := J)]
    with ω hmem hfin
  intro T C f
  let g : Event J → ℝ := fun e => (Iic T ×ˢ Iic C).indicator (f e.1) (point e.1 ω e.2)
  have hgfin : {e | g e ≠ 0}.Finite := (hfin T C).subset (by
    intro e he
    by_contra hn
    change point e.1 ω e.2 ∉ Iic T ×ˢ Iic C at hn
    exact he (Set.indicator_of_not_mem hn _))
  have hsub (j : J) : {p : ℕ × ℕ | g (j,p) ≠ 0}.Finite :=
    hgfin.preimage (fun _ _ _ _ h => Prod.mk.inj h |>.2)
  have hi (j : J) :
      (∫ p, (Iic T ×ˢ Iic C).indicator (f j) p ∂countingMeasure j ω) = ∑' p, g (j,p) :=
    integral_atomic_of_finite_support (point j ω) _ (hsub j)
  simp_rw [hi]
  have hsum : Summable g := summable_of_finite_support hgfin
  rw [← tsum_fintype, ← hsum.tsum_prod' (fun j => summable_of_finite_support (hsub j))]
  have hzero : ∀ e ∉ (boxedList (ω,T,C)).toFinset, g e = 0 := by
    intro e he
    have hn : point e.1 ω e.2 ∉ Iic T ×ˢ Iic C := by
      simpa only [List.mem_toFinset, hmem T C e] using he
    exact Set.indicator_of_not_mem hn _
  rw [tsum_eq_sum hzero, sum_get_eq_sum_toFinset (boxedList (ω,T,C))
    (chronologicalList_nodup _ _ _) (fun e => f e.1 (point e.1 ω e.2))]
  apply Finset.sum_congr rfl
  intro e he
  exact Set.indicator_of_mem ((hmem T C e).mp (List.mem_toFinset.mp he)) _

section Frozen
open CommonFrozenProcess FrozenPredictableIntegrand

variable {E : Type*} [DecidableEq E] [TopologicalSpace E] [PolishSpace E]
  (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)

/-- The predictable pre-state agrees with the explicit chronological left
state at every positive time on one event of probability one. -/
theorem ae_preState_eq_leftProcess : ∀ᵐ ω ∂law J,
    ∀ C x t, 0 < t → preState active jump rate C x ω t =
      leftProcess active jump rate C x ω t := by
  filter_upwards [ae_process_eq_leftProcess_on_left active jump rate] with ω hω
  intro C x t ht
  obtain ⟨b, hb, hy⟩ := hω C x t
  exact preState_eq_of_left_constant active jump rate C x ω t ht b hb _ hy

omit [Fintype J] [PolishSpace E] in
/-- The predictable jump integrand already vanishes at nonpositive times and
above the construction's height cutoff. -/
theorem jumpIncrement_box_indicator (C : ℝ) (x : E) (V : E → ℝ)
    (j : J) (ω : Sample J) (T : ℝ) :
    (Iic T ×ˢ Iic C).indicator (fun p => jumpIncrement active jump rate C x V j (ω,p)) =
      (Ioc 0 T ×ˢ univ).indicator (fun p => jumpIncrement active jump rate C x V j (ω,p)) := by
  funext p
  simp only [Set.indicator_apply, Set.mem_prod, Set.mem_Iic, Set.mem_Ioc, Set.mem_univ, and_true]
  by_cases hT : p.1 ≤ T <;> by_cases hC : p.2 ≤ C <;> by_cases hp : 0 < p.1 <;>
    simp [jumpIncrement, hT, hC, hp]

omit [PolishSpace E] in
/-- Actual pathwise Bochner integrability is a consequence of finite event
support, not an integrability hypothesis imposed on the jump equation. -/
theorem ae_integrable_jumpIncrement : ∀ᵐ ω ∂law J,
    ∀ C x T (V : E → ℝ) (j : J),
      IntegrableOn (fun p => jumpIncrement active jump rate C x V j (ω,p))
        (Ioc 0 T ×ˢ univ) (countingMeasure j ω) := by
  filter_upwards [ae_integrable_box_weights (J := J)] with ω hω
  intro C x T V j
  rw [← integrable_indicator_iff (measurableSet_Ioc.prod MeasurableSet.univ),
    ← jumpIncrement_box_indicator active jump rate C x V j ω T]
  exact hω T C j _

/-- The actual frozen path solves the test-function jump equation with the
proved predictable pre-state and the original common counting measures. -/
theorem ae_testFunction_counting_identity (V : E → ℝ) : ∀ᵐ ω ∂law J,
    ∀ C x T,
      V (process active jump rate C x ω T) - V (process active jump rate C x ω 0) =
        ∑ j : J, ∫ p in Ioc 0 T ×ˢ univ,
          jumpIncrement active jump rate C x V j (ω,p) ∂countingMeasure j ω := by
  filter_upwards [ae_process_telescope_left active jump rate V,
    ae_preState_eq_leftProcess active jump rate, ae_integral_box_eq_sum (J := J),
    ae_boxedList_mem (J := J), MarkedNoise.ae_positive_points (J := J)]
      with ω htel hpre hint hmem hpos
  intro C x T
  rw [htel C x T]
  calc
    _ = ∑ n : Fin (boxedList (ω,T,C)).length,
        let e := (boxedList (ω,T,C)).get n
        jumpIncrement active jump rate C x V e.1 (ω, point e.1 ω e.2) := by
      apply Finset.sum_congr rfl
      intro n _
      let e := (boxedList (ω,T,C)).get n
      have he : e ∈ boxedList (ω,T,C) := List.get_mem _ n
      have heC : (point e.1 ω e.2).2 ≤ C := ((hmem T C e).mp he).2
      have hepos := (hpos e.1 e.2).1
      change acceptedIncrement active jump rate V ω
        (leftProcess active jump rate C x ω (point e.1 ω e.2).1) e =
          jumpIncrement active jump rate C x V e.1 (ω, point e.1 ω e.2)
      simp only [jumpIncrement, hpre C x _ hepos, hepos, heC, true_and]
      rfl
    _ = ∑ j : J, ∫ p, (Iic T ×ˢ Iic C).indicator
        (fun p => jumpIncrement active jump rate C x V j (ω,p)) p ∂countingMeasure j ω :=
      (hint T C (fun j p => jumpIncrement active jump rate C x V j (ω,p))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [jumpIncrement_box_indicator, integral_indicator (measurableSet_Ioc.prod MeasurableSet.univ)]

end Frozen

end CarryingCapacity.FrozenCountingIdentity
