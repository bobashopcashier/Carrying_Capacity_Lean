import CarryingCapacity.CountingEquationUniqueness

/-!
# Uniqueness for actual time-dependent rate-threshold equations

The equation is tested against singleton indicators, a separating family on
the state space. Its integrands use genuine positive-time left limits. Strict
past agreement makes these integrands equal on the whole time-height horizon,
including its terminal time. Discrete right continuity then excludes a first
disagreement. No bound on candidate rates or activity is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical Topology BigOperators

namespace CarryingCapacity.TimeDependentEquationUniqueness
open CountingEquationUniqueness

variable {E J : Type*}

/-- The unrestricted counting integrand on a deterministic time horizon. -/
def increment (jump : J → E → E) (rate : J → ℝ → E → ℝ) (pre : ℝ → E)
    (f : E → ℝ) (j : J) (T : ℝ) (q : ℝ × ℝ) : ℝ :=
  if q.1 ∈ Ioc 0 T ∧ q.2 ≤ rate j q.1 (pre q.1)
    then f (jump j (pre q.1)) - f (pre q.1) else 0

section Uniqueness
variable [Fintype J] [TopologicalSpace E] [DiscreteTopology E]

/-- Any separating family of real test functions suffices. In particular,
finite coordinate projections can be used for configuration-valued paths. -/
theorem eq_of_separating_counting_equations {I : Type*} (test : I → E → ℝ)
    (hseparate : ∀ x y : E, (∀ i, test i x = test i y) → x = y)
    (jump : J → E → E) (rate : J → ℝ → E → ℝ)
    (N : J → Measure (ℝ × ℝ)) (X Y xpre ypre : ℝ → E)
    (hX : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt X (Ici t) t)
    (hY : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt Y (Ici t) t)
    (hx : ∀ t : ℝ, 0 < t → Tendsto X (𝓝[<] t) (𝓝 (xpre t)))
    (hy : ∀ t : ℝ, 0 < t → Tendsto Y (𝓝[<] t) (𝓝 (ypre t)))
    (hzero : X 0 = Y 0)
    (heqX : ∀ (i : I) (T : ℝ), 0 ≤ T →
      test i (X T) - test i (X 0) =
        ∑ j : J, ∫ q, increment jump rate xpre (test i) j T q ∂N j)
    (heqY : ∀ (i : I) (T : ℝ), 0 ≤ T →
      test i (Y T) - test i (Y 0) =
        ∑ j : J, ∫ q, increment jump rate ypre (test i) j T q ∂N j) :
    ∀ t : ℝ, 0 ≤ t → X t = Y t := by
  apply DiscreteCausalUniqueness.eq_of_strictPast X Y hX hY
  intro T hT hprior
  have hpre : ∀ t ∈ Ioc (0 : ℝ) T, xpre t = ypre t :=
    leftLimit_eq_of_strictPast X Y xpre ypre hx hy T hprior
  apply hseparate
  intro i
  have hi (j : J) : increment jump rate xpre (test i) j T =
      increment jump rate ypre (test i) j T := by
    funext q
    by_cases hq : q.1 ∈ Ioc 0 T
    · simp only [increment, hq, true_and, hpre q.1 hq]
    · simp only [increment, hq, false_and, ↓reduceIte]
  have htest : test i (X T) - test i (X 0) = test i (Y T) - test i (Y 0) := by
    rw [heqX i T hT, heqY i T hT]
    apply Finset.sum_congr rfl
    intro j _
    rw [hi j]
  rw [hzero] at htest
  linarith

/-- Two discrete right-continuous paths satisfying the same actual counting
equations, with their genuine left limits and the same initial value, agree.
Only singleton test equations are required. Integrability is not an input to
this uniqueness argument, since the compared integrands are pointwise equal. -/
theorem eq_of_counting_equations (jump : J → E → E) (rate : J → ℝ → E → ℝ)
    (N : J → Measure (ℝ × ℝ)) (X Y xpre ypre : ℝ → E)
    (hX : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt X (Ici t) t)
    (hY : ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt Y (Ici t) t)
    (hx : ∀ t : ℝ, 0 < t → Tendsto X (𝓝[<] t) (𝓝 (xpre t)))
    (hy : ∀ t : ℝ, 0 < t → Tendsto Y (𝓝[<] t) (𝓝 (ypre t)))
    (hzero : X 0 = Y 0)
    (heqX : ∀ (z : E) (T : ℝ), 0 ≤ T →
      stateTest z (X T) - stateTest z (X 0) =
        ∑ j : J, ∫ q, increment jump rate xpre (stateTest z) j T q ∂N j)
    (heqY : ∀ (z : E) (T : ℝ), 0 ≤ T →
      stateTest z (Y T) - stateTest z (Y 0) =
        ∑ j : J, ∫ q, increment jump rate ypre (stateTest z) j T q ∂N j) :
    ∀ t : ℝ, 0 ≤ t → X t = Y t := by
  apply DiscreteCausalUniqueness.eq_of_strictPast X Y hX hY
  intro T hT hprior
  have hpre : ∀ t ∈ Ioc (0 : ℝ) T, xpre t = ypre t :=
    leftLimit_eq_of_strictPast X Y xpre ypre hx hy T hprior
  have hi (z : E) (j : J) : increment jump rate xpre (stateTest z) j T =
      increment jump rate ypre (stateTest z) j T := by
    funext q
    by_cases hq : q.1 ∈ Ioc 0 T
    · simp only [increment, hq, true_and, hpre q.1 hq]
    · simp only [increment, hq, false_and, ↓reduceIte]
  have htest : stateTest (X T) (X T) - stateTest (X T) (X 0) =
      stateTest (X T) (Y T) - stateTest (X T) (Y 0) := by
    rw [heqX (X T) T hT, heqY (X T) T hT]
    apply Finset.sum_congr rfl
    intro j _
    rw [hi (X T) j]
  by_contra hne
  simp only [hzero, stateTest, if_pos rfl, if_neg (Ne.symm hne), ↓reduceIte] at htest
  linarith

end Uniqueness
end CarryingCapacity.TimeDependentEquationUniqueness
