import CarryingCapacity.TimeDependentGeneratorIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Weak forward laws and their genuine atomic regularity

A weak forward solution records probability measures, the integrated equation
for every finitely supported test, and genuine time integrability. The latter
prevents Lean's default value for a nonintegrable Bochner integral from being
mistaken for a solution. Atomic continuity is derived from the equation.
Finite jump fibers then turn every tested generator into a finite sum, so
continuous coefficients give continuous expected generators as a conclusion.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace CarryingCapacity.FiniteJumpForward

variable {E J : Type*} [DecidableEq E] [Fintype J]
  [MeasurableSpace E] [MeasurableSingletonClass E]

/-- The unrestricted finite-label generator. Self-loops cancel exactly. -/
def generator (jump : J → E → E) (rate : J → ℝ → E → ℝ)
    (f : E → ℝ) (t : ℝ) (x : E) : ℝ :=
  ∑ j, rate j t x * (f (jump j x) - f x)

/-- The ordinary real mass of a singleton. -/
def atom (μ : Measure E) (x : E) : ℝ := μ.real {x}

/-- Singleton tests belong to the actual finitely supported test class. -/
def singletonTest (x y : E) : ℝ := if y = x then 1 else 0

omit [MeasurableSpace E] [MeasurableSingletonClass E] in
theorem support_singletonTest (x : E) : Function.support (singletonTest x) = {x} := by
  ext y
  simp [singletonTest]

theorem integral_singletonTest (μ : Measure E) (x : E) :
    (∫ y, singletonTest x y ∂μ) = atom μ x := by
  have he : singletonTest x = ({x} : Set E).indicator (fun _ => (1 : ℝ)) := by
    funext y
    simp [singletonTest, Set.indicator_apply]
  rw [he, integral_indicator_const _ (measurableSet_singleton x)]
  simp [atom]

/-- A probability-valued weak solution with genuine Lebesgue time integrals.
These are the defining hypotheses on a candidate law, not assumed uniqueness. -/
structure IsSolution (jump : J → E → E) (rate : J → ℝ → E → ℝ)
    (α : Measure E) (p : ℝ → Measure E) (T : ℝ) : Prop where
  probability : ∀ t ∈ Icc 0 T, IsProbabilityMeasure (p t)
  integrable : ∀ f : E → ℝ, (Function.support f).Finite →
    IntervalIntegrable (fun s => ∫ x, generator jump rate f s x ∂p s) volume 0 T
  equation : ∀ f : E → ℝ, (Function.support f).Finite → ∀ t ∈ Icc 0 T,
    (∫ x, f x ∂p t) = (∫ x, f x ∂α) +
      ∫ s in (0 : ℝ)..t, ∫ x, generator jump rate f s x ∂p s

variable (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (α : Measure E) (p : ℝ → Measure E) (T : ℝ) (hT : 0 ≤ T)
  (hp : IsSolution jump rate α p T)

include hT hp

omit [DecidableEq E] [MeasurableSingletonClass E] in
/-- Every tested expectation of a weak solution is continuous, directly from
the genuinely integrable primitive in its defining equation. -/
theorem continuousOn_testExpectation (f : E → ℝ) (hf : (Function.support f).Finite) :
    ContinuousOn (fun t => ∫ x, f x ∂p t) (Icc 0 T) := by
  have hc := intervalIntegral.continuousOn_primitive_interval' (hp.integrable f hf) left_mem_uIcc
  rw [uIcc_of_le hT] at hc
  apply (continuousOn_const.add hc).congr
  intro t ht
  exact hp.equation f hf t ht

/-- No continuity of the candidate measure curve was assumed. -/
theorem continuousOn_atom (x : E) : ContinuousOn (fun t => atom (p t) x) (Icc 0 T) := by
  have hf : (Function.support (singletonTest x)).Finite := by
    rw [support_singletonTest]
    exact finite_singleton x
  simpa only [integral_singletonTest] using
    continuousOn_testExpectation jump rate α p T hT hp (singletonTest x) hf

omit hT in
theorem atom_equation (x : E) (t : ℝ) (ht : t ∈ Icc 0 T) :
    atom (p t) x = atom α x + ∫ s in (0 : ℝ)..t,
      ∫ y, generator jump rate (singletonTest x) s y ∂p s := by
  have hf : (Function.support (singletonTest x)).Finite := by
    rw [support_singletonTest]
    exact finite_singleton x
  simpa only [integral_singletonTest] using hp.equation (singletonTest x) hf t ht

omit hT hp α p T in
/-- Finite influence is purely geometric and does not restrict the rates. -/
def influenceSet (f : E → ℝ) : Set E :=
  Function.support f ∪ ⋃ j : J, jump j ⁻¹' Function.support f

omit hT hp α p T [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
theorem finite_influenceSet
    (hfiber : ∀ j : J, ∀ x : E, {y | jump j y = x}.Finite)
    (f : E → ℝ) (hf : (Function.support f).Finite) :
    (influenceSet jump f).Finite := by
  apply hf.union
  apply Set.finite_iUnion
  intro j
  have hu := hf.biUnion (fun x _ => hfiber j x)
  apply hu.subset
  intro y hy
  exact mem_iUnion.mpr ⟨jump j y, mem_iUnion.mpr ⟨hy, rfl⟩⟩

omit hT hp α p T [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
theorem generator_eq_zero_of_not_mem (f : E → ℝ) (t : ℝ) (x : E)
    (hx : x ∉ influenceSet jump f) : generator jump rate f t x = 0 := by
  have h0 : f x = 0 := by
    by_contra h
    exact hx (Or.inl h)
  have h1 (j : J) : f (jump j x) = 0 := by
    by_contra h
    exact hx (Or.inr (mem_iUnion.mpr ⟨j, h⟩))
  simp [generator, h0, h1]

omit hT hp α p T [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- A finitely supported test's generator is supported on its finite
backward influence set, even with globally unbounded rates. -/
theorem support_generator_subset (f : E → ℝ) (t : ℝ) :
    Function.support (generator jump rate f t) ⊆ influenceSet jump f := by
  intro x hx
  by_contra h
  exact hx (generator_eq_zero_of_not_mem jump rate f t x h)

omit hT hp α p T [DecidableEq E] in
theorem integral_generator_eq_sum
    (hfiber : ∀ j : J, ∀ x : E, {y | jump j y = x}.Finite)
    (f : E → ℝ) (hf : (Function.support f).Finite)
    (μ : Measure E) [IsFiniteMeasure μ] (t : ℝ) :
    (∫ x, generator jump rate f t x ∂μ) =
      ∑ x ∈ (finite_influenceSet jump hfiber f hf).toFinset,
        atom μ x * generator jump rate f t x := by
  let S := (finite_influenceSet jump hfiber f hf).toFinset
  have hs : ∀ x, x ∉ (S : Set E) → generator jump rate f t x = 0 := by
    intro x hx
    exact generator_eq_zero_of_not_mem jump rate f t x (by simpa [S] using hx)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hs,
    integral_finset S _ (IntegrableOn.finset (s := S))]
  rfl

/-- Finite predecessor geometry and the defining equation upgrade expected
generator drifts to continuous functions on the construction horizon. -/
theorem continuousOn_expectedGenerator
    (hfiber : ∀ j : J, ∀ x : E, {y | jump j y = x}.Finite)
    (hrate : ∀ j x, ContinuousOn (fun t => rate j t x) (Icc 0 T))
    (f : E → ℝ) (hf : (Function.support f).Finite) :
    ContinuousOn (fun t => ∫ x, generator jump rate f t x ∂p t) (Icc 0 T) := by
  have hg (x : E) : ContinuousOn (fun t => generator jump rate f t x) (Icc 0 T) := by
    apply continuousOn_finset_sum
    intro j _
    exact (hrate j x).mul continuousOn_const
  have hc : ContinuousOn (fun t =>
      ∑ x ∈ (finite_influenceSet jump hfiber f hf).toFinset,
        atom (p t) x * generator jump rate f t x) (Icc 0 T) := by
    apply continuousOn_finset_sum
    intro x _
    exact (continuousOn_atom jump rate α p T hT hp x).mul (hg x)
  apply hc.congr
  intro t ht
  letI : IsProbabilityMeasure (p t) := hp.probability t ht
  exact integral_generator_eq_sum jump rate hfiber f hf (p t) t

end CarryingCapacity.FiniteJumpForward
