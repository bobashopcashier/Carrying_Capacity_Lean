import Mathlib

/-!
# Deterministic successive-limit arguments

These results formalize the order of limits in Sections 5 and 6 of the revised
paper. Their inputs are real error bounds already obtained elsewhere; they do
not assert the stochastic estimates that provide those bounds.
-/

open Filter Topology

namespace CarryingCapacity.LimitArguments

/-- Remove a cutoff only after taking the population limit at each fixed cutoff.

`b R` is the cutoff error and `e R N` is the finite-population error. No estimate
uniform in `R`, and no diagonal choice `R = R N`, is assumed. The bound itself
may hold only eventually in `N` for each fixed positive cutoff.
-/
theorem successive_limit (a b : ℕ → ℝ) (e : ℕ → ℕ → ℝ)
    (ha : ∀ N, 0 ≤ a N)
    (hbound : ∀ R : ℕ, 0 < R → ∀ᶠ N in atTop, a N ≤ b R + e R N)
    (hb : Tendsto b atTop (𝓝 0))
    (he : ∀ R : ℕ, 0 < R → Tendsto (e R) atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro lower hlower
    exact Filter.Eventually.of_forall fun N => lt_of_lt_of_le hlower (ha N)
  · intro ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    have hb_small : ∀ᶠ R in atTop, b R < ε / 2 :=
      hb.eventually (gt_mem_nhds hhalf)
    obtain ⟨R, hR, hbR⟩ := ((eventually_gt_atTop (0 : ℕ)).and hb_small).exists
    have he_small : ∀ᶠ N in atTop, e R N < ε / 2 :=
      (he R hR).eventually (gt_mem_nhds hhalf)
    filter_upwards [hbound R hR, he_small] with N hN heN
    linarith

/-- The cutoff-removal form with exit probability bounded by `C/(R+1)`.

The same result applies to mesh refinement with deterministic error
`C/(m+1)`, after the empirical error vanishes on each fixed grid.
-/
theorem reciprocal_cutoff_limit (a : ℕ → ℝ) (e : ℕ → ℕ → ℝ) (C : ℝ)
    (ha : ∀ N, 0 ≤ a N)
    (hbound : ∀ R : ℕ, 0 < R → ∀ᶠ N in atTop, a N ≤ C / ((R : ℝ) + 1) + e R N)
    (he : ∀ R : ℕ, 0 < R → Tendsto (e R) atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  apply successive_limit a (fun R => C / ((R : ℝ) + 1)) e ha hbound
  · simpa only [mul_zero, mul_one_div] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul C
  · exact he

/-- The scalar three-region criterion used to upgrade probability errors to
expected errors once a uniform tail estimate is available.

In the paper, `a N` is an expectation, `p δ N` is a probability of an error
exceeding `δ`, and `tail M` bounds the expectation on the region above `M`,
uniformly in `N`. Their measure-theoretic interpretation is not assumed by
this lemma. The proof first fixes `δ`, then a tail cutoff `M`, then sends `N`
to infinity. The threshold condition `δ < M` is retained explicitly.
-/
theorem three_region_limit (a : ℕ → ℝ) (p : ℝ → ℕ → ℝ) (tail : ℕ → ℝ)
    (ha : ∀ N, 0 ≤ a N)
    (hbound : ∀ δ : ℝ, 0 < δ → ∀ M : ℕ, δ < (M : ℝ) →
      ∀ N, a N ≤ δ + (M : ℝ) * p δ N + tail M)
    (hp : ∀ δ : ℝ, 0 < δ → Tendsto (p δ) atTop (𝓝 0))
    (htail : Tendsto tail atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro lower hlower
    exact Filter.Eventually.of_forall fun N => lt_of_lt_of_le hlower (ha N)
  · intro ε hε
    have hthird : 0 < ε / 3 := by linarith
    have htail_small : ∀ᶠ M in atTop, tail M < ε / 3 :=
      htail.eventually (gt_mem_nhds hthird)
    have hMlarge : ∀ᶠ M : ℕ in atTop, ε / 3 < (M : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (ε / 3))
    obtain ⟨M, hM, htailM⟩ := (hMlarge.and htail_small).exists
    have hpM : Tendsto (fun N => (M : ℝ) * p (ε / 3) N) atTop (𝓝 0) := by
      simpa only [mul_zero] using (hp (ε / 3) hthird).const_mul (M : ℝ)
    have hp_small : ∀ᶠ N in atTop, (M : ℝ) * p (ε / 3) N < ε / 3 :=
      hpM.eventually (gt_mem_nhds hthird)
    filter_upwards [hp_small] with N hpN
    have hN := hbound (ε / 3) hthird M hM N
    linarith

/-- A concrete fixed-cutoff error that need not vanish on a growing diagonal. -/
def diagonalExample (R N : ℕ) : ℝ := if N ≤ R then 1 else 0

/-- For every fixed cutoff, the example's error is eventually exactly zero. -/
theorem diagonalExample_fixed (R : ℕ) :
    Tendsto (diagonalExample R) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop R] with N hN
  simp [diagonalExample, not_le.mpr hN]

/-- Along the diagonal `R=N`, the same error equals one for every `N`.
This records why fixed-cutoff convergence supplies no arbitrary diagonal rate. -/
theorem diagonalExample_self (N : ℕ) : diagonalExample N N = 1 := by
  simp [diagonalExample]

end CarryingCapacity.LimitArguments
