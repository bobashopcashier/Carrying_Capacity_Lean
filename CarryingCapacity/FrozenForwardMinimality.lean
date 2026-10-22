import CarryingCapacity.FiniteForwardComparison
import CarryingCapacity.FiniteJumpRestriction
import CarryingCapacity.TimeDependentFrozenForward

/-!
# Actual frozen probabilities are minimal on their active set

The frozen process satisfies its proved finite forward system, including
leakage through exits. Restricting any probability-valued weak forward
solution adds a nonnegative incoming term from the exterior. The finite
comparison theorem therefore orders these two actual laws. Neither a
minimality inequality nor an equation for the constructed process is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace CarryingCapacity.FrozenForwardMinimality
open FiniteJumpForward TimeDependentFrozenForward FiniteJumpRestriction

variable {E J : Type*} [DecidableEq E] [Fintype J] [Countable E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (G : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (hfiber : ∀ j : J, ∀ x : E, {y | jump j y = x}.Finite)
  (α : Measure E) [IsProbabilityMeasure α] (p : ℝ → Measure E)
  (T : ℝ) (hT : 0 ≤ T) (hp : IsSolution jump rate α p T)
  (hRate : ∀ j x, Measurable (fun t => rate j t x))
  (hCont : ∀ j x, ContinuousOn (fun t => rate j t x) (Icc 0 T))
  (C : ℝ) (hC : 0 ≤ C)
  (hq : ∀ j t x, 0 ≤ t → 0 ≤ rate j t x)
  (hbound : ∀ x ∈ G, ∀ j t, 0 ≤ t → rate j t x ≤ C)
  (e : E)

include hfiber e hT hp hRate hCont hC hq hbound

/-- Every probability-valued weak solution dominates each actual frozen
mass at every state still inside the finite active region. -/
theorem mass_le_solution (t : ℝ) (ht : t ∈ Icc 0 T) (x : G) :
    TimeDependentFrozenForward.mass G jump rate id α C t x ≤ atom (p t) x := by
  let Q : ℝ → G → G → ℝ := fun s y z => matrixEntry jump rate s y z
  let u : G → ℝ → ℝ := fun y s => TimeDependentFrozenForward.mass G jump rate id α C s y
  let w : G → ℝ → ℝ := fun y s => atom (p s) y
  let g : G → ℝ → ℝ := fun y s => outsideInflow jump rate hfiber G p s y
  have hu0 (i : G) : u i 0 = atom α i := by
    change TimeDependentFrozenForward.mass G jump rate id α C 0 i = _
    rw [mass_zero]
    exact integral_singletonTest α i
  have hw0 (i : G) : w i 0 = atom α i := by
    have h := atom_equation jump rate α p T hp i 0 ⟨le_rfl, hT⟩
    simpa only [intervalIntegral.integral_same, add_zero] using h
  have huCont (i : G) : ContinuousOn (u i) (Icc 0 T) :=
    (TimeDependentFrozenForward.continuousOn_mass G jump rate id α hRate measurable_id C e i
      (fun y _ j s hs => hq j s y hs) hbound).mono Icc_subset_Ici_self
  have hwCont (i : G) : ContinuousOn (w i) (Icc 0 T) :=
    continuousOn_atom jump rate α p T hT hp i
  have hQCont (i j : G) : ContinuousOn (fun s => Q s i j) (Icc 0 T) :=
    continuousOn_finset_sum _ (fun k _ => (hCont k i).mul continuousOn_const)
  have hgCont (i : G) : ContinuousOn (g i) (Icc 0 T) :=
    continuousOn_outsideInflow jump rate hfiber G α p T hT hp hCont i
  have hQpos (s : ℝ) (hs : s ∈ Icc 0 T) (i j : G) (hij : i ≠ j) :
      0 ≤ Q s i j :=
    matrixEntry_nonneg_of_ne jump rate s i j
      (fun h => hij (Subtype.ext h)) (fun k => hq k s i hs.1)
  have hQbound (s : ℝ) (hs : s ∈ Icc 0 T) (i j : G) :
      Q s i j ≤ (Fintype.card J : ℝ) * C := by
    exact (le_abs_self _).trans (norm_matrixEntry_le jump rate C s i j
      (fun k => hq k s i hs.1) (fun k => hbound i i.property k s hs.1))
  have huEq (i : G) (s : ℝ) (_hs : s ∈ Icc 0 T) :
      u i s = u i 0 + ∫ r in Ioc 0 s, FiniteForwardComparison.forward Q u i r := by
    have h := TimeDependentFrozenForward.mass_forward G jump rate id α hRate measurable_id
      C e i s (fun y _ j r hr => hq j r y hr) hbound
    have h0 : (∫ a, atomTest (i : E) (id a) ∂α) = atom α i := integral_singletonTest α i
    rw [h0] at h
    rw [hu0]
    change TimeDependentFrozenForward.mass G jump rate id α C s i = _
    rw [h]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r _
    calc
      _ = ∑ y : G, TimeDependentFrozenForward.mass G jump rate id α C r y *
          matrixEntry jump rate r y i := (Finset.sum_attach G _).symm
      _ = _ := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hwEq (i : G) (s : ℝ) (hs : s ∈ Icc 0 T) :
      w i s = w i 0 + ∫ r in Ioc 0 s, (FiniteForwardComparison.forward Q w i r + g i r) := by
    have h := restricted_atom_equation jump rate hfiber G α p T hp s hs i
    rw [hw0]
    apply h.trans
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r _
    simp only [FiniteForwardComparison.forward, Q, w, g, mul_comm]
  exact FiniteForwardComparison.le_of_continuous_integral_eq hT huCont hwCont hQCont hgCont
    (mul_nonneg (Nat.cast_nonneg _) hC) hQpos hQbound
    (fun i => (hu0 i).trans (hw0 i).symm |>.le)
    (fun i s hs => outsideInflow_nonnegative jump rate hfiber G p s i i.property
      (fun j y => hq j s y hs.1.le)) huEq hwEq t ht x

end CarryingCapacity.FrozenForwardMinimality
