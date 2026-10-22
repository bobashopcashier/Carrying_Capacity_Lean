import CarryingCapacity.FiniteJumpForward
import CarryingCapacity.TimeDependentFrozenForward

/-!
# Restricting a genuine forward law to a finite set

Finite jump fibers make the omitted incoming term a finite sum. The actual
weak forward equation therefore gives a finite inhomogeneous system on any
finite set. Its external inflow is nonnegative, and continuity follows from
the atomic continuity already derived from the weak equation. No finite
restriction equation or comparison conclusion is assumed.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical

namespace CarryingCapacity.FiniteJumpRestriction
open FiniteJumpForward TimeDependentFrozenForward

variable {E J : Type*} [DecidableEq E] [Fintype J]
  [MeasurableSpace E] [MeasurableSingletonClass E]
  (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (hfiber : ∀ j : J, ∀ x : E, {y | jump j y = x}.Finite)

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- The finite set that can contribute to a singleton's generator. -/
def singletonInfluence (x : E) : Finset E :=
  (finite_influenceSet jump hfiber (singletonTest x)
    (by rw [support_singletonTest]; exact finite_singleton x)).toFinset

omit [MeasurableSpace E] [MeasurableSingletonClass E] hfiber in
/-- The matrix used by the actual frozen process is the same singleton
generator used in a candidate weak forward law. -/
theorem matrixEntry_eq_generator (t : ℝ) (y x : E) :
    matrixEntry jump rate t y x = generator jump rate (singletonTest x) t y := rfl

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
theorem matrixEntry_eq_zero_of_not_mem (t : ℝ) (y x : E)
    (hy : y ∉ singletonInfluence jump hfiber x) : matrixEntry jump rate t y x = 0 := by
  rw [matrixEntry_eq_generator]
  apply generator_eq_zero_of_not_mem
  simpa only [singletonInfluence, Set.Finite.mem_toFinset] using hy

/-- The omitted incoming contribution is a finite predecessor sum. -/
def outsideInflow (G : Finset E) (p : ℝ → Measure E) (t : ℝ) (x : E) : ℝ :=
  ∑ y ∈ singletonInfluence jump hfiber x \ G,
    atom (p t) y * matrixEntry jump rate t y x

omit [MeasurableSingletonClass E] in
/-- For a target inside the finite set, every omitted source is distinct
from that target, so the omitted contribution is nonnegative. -/
theorem outsideInflow_nonnegative (G : Finset E) (p : ℝ → Measure E)
    (t : ℝ) (x : E) (hx : x ∈ G) (hq : ∀ j y, 0 ≤ rate j t y) :
    0 ≤ outsideInflow jump rate hfiber G p t x := by
  apply Finset.sum_nonneg
  intro y hy
  have hne : y ≠ x := by
    intro he
    exact (Finset.mem_sdiff.mp hy).2 (he.symm ▸ hx)
  exact mul_nonneg (measureReal_nonneg) (matrixEntry_nonneg_of_ne jump rate t y x hne
    (fun j => hq j y))

/-- At a fixed time, the full singleton drift splits exactly into the
finite internal matrix and the explicit external inflow. -/
theorem integral_generator_split (G : Finset E) (μ : Measure E) [IsFiniteMeasure μ]
    (t : ℝ) (x : E) :
    (∫ y, generator jump rate (singletonTest x) t y ∂μ) =
      (∑ y ∈ G, atom μ y * matrixEntry jump rate t y x) +
        outsideInflow jump rate hfiber G (fun _ => μ) t x := by
  have hsupport : (Function.support (singletonTest x)).Finite := by
    rw [support_singletonTest]
    exact finite_singleton x
  rw [integral_generator_eq_sum jump rate hfiber (singletonTest x) hsupport μ t]
  change (∑ y ∈ singletonInfluence jump hfiber x,
      atom μ y * generator jump rate (singletonTest x) t y) = _
  simp_rw [← matrixEntry_eq_generator]
  let S := singletonInfluence jump hfiber x
  have he : (∑ y ∈ S ∩ G, atom μ y * matrixEntry jump rate t y x) =
      ∑ y ∈ G, atom μ y * matrixEntry jump rate t y x := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro y hy hnot
    have hyS : y ∉ S := fun h => hnot (Finset.mem_inter.mpr ⟨h, hy⟩)
    rw [matrixEntry_eq_zero_of_not_mem jump rate hfiber t y x hyS, mul_zero]
  have hsplit := Finset.sum_inter_add_sum_diff S G
    (fun y => atom μ y * matrixEntry jump rate t y x)
  rw [he] at hsplit
  exact hsplit.symm

omit hfiber [MeasurableSpace E] [MeasurableSingletonClass E] in
theorem continuousOn_matrixEntry (T : ℝ)
    (hrate : ∀ j x, ContinuousOn (fun t => rate j t x) (Icc 0 T)) (y x : E) :
    ContinuousOn (fun t => matrixEntry jump rate t y x) (Icc 0 T) :=
  continuousOn_finset_sum _ (fun j _ => (hrate j y).mul continuousOn_const)

variable (G : Finset E) (α : Measure E) (p : ℝ → Measure E) (T : ℝ)
  (hT : 0 ≤ T) (hp : IsSolution jump rate α p T)
include hT hp

/-- Continuity of the external inflow is derived from the candidate's
actual integrated equation and the finite predecessor geometry. -/
theorem continuousOn_outsideInflow
    (hrate : ∀ j x, ContinuousOn (fun t => rate j t x) (Icc 0 T)) (x : E) :
    ContinuousOn (fun t => outsideInflow jump rate hfiber G p t x) (Icc 0 T) := by
  apply continuousOn_finset_sum
  intro y _
  exact (continuousOn_atom jump rate α p T hT hp y).mul
    (continuousOn_matrixEntry jump rate T hrate y x)

omit hT in
/-- Restricting a weak forward law produces a genuine finite system with
the nonnegative external incoming term retained explicitly. -/
theorem restricted_atom_equation (t : ℝ) (ht : t ∈ Icc 0 T) (x : G) :
    atom (p t) x = atom α x + ∫ s in Ioc 0 t,
      ((∑ y : G, atom (p s) y * matrixEntry jump rate s y x) +
        outsideInflow jump rate hfiber G p s x) := by
  rw [atom_equation jump rate α p T hp x t ht, intervalIntegral.integral_of_le ht.1]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  letI : IsProbabilityMeasure (p s) := hp.probability s ⟨hs.1.le, hs.2.trans ht.2⟩
  dsimp only
  rw [integral_generator_split jump rate hfiber G (p s) s x]
  congr 1
  exact (Finset.sum_attach G (fun y => atom (p s) y * matrixEntry jump rate s y x)).symm

end CarryingCapacity.FiniteJumpRestriction
