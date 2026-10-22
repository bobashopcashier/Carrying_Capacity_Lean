import CarryingCapacity.MarkedBlockProducts

/-!
# Finite past mark products and a deterministic future block

Actual iid mark coordinates factor over disjoint finite index sets. A censored
past cylinder uses mark-dependent factors only below a deterministic boundary;
all later factors are deterministic constants. Its product with a future block
therefore factors under the actual mark law. These results make no assumption
of independence at a random index.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

namespace CarryingCapacity.MarkedPastProducts
open FrozenProcess MarkedNoise MarkedBlockProducts

/-- Two disjoint finite products, allowing a different measurable factor at every index. -/
theorem integral_disjoint_pair_products (K L : Finset ℕ) (hKL : Disjoint K L)
    (f g : ℕ → ℝ → ℂ) (hf : ∀ k, Measurable (f k)) (hg : ∀ k, Measurable (g k)) :
    (∫ u, (∏ k ∈ K, f k (u k)) * (∏ n ∈ L, g n (u n)) ∂unitMarksLaw) =
      (∏ k ∈ K, ∫ x, f k x ∂uniformUnit) * (∏ n ∈ L, ∫ x, g n x ∂uniformUnit) := by
  classical
  let e : K ⊕ L → ℕ := Sum.elim Subtype.val Subtype.val
  let F : K ⊕ L → ℝ → ℂ := Sum.elim (fun k => f k) (fun n => g n)
  have he : Function.Injective e := by
    intro x y h
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg Sum.inl (Subtype.ext h)
    · have hxy : x.val = y.val := h
      exact (Finset.disjoint_left.mp hKL x.property (hxy.symm ▸ y.property)).elim
    · have hxy : x.val = y.val := h
      exact (Finset.disjoint_left.mp hKL y.property (hxy ▸ x.property)).elim
    · exact congrArg Sum.inr (Subtype.ext h)
  have h := integral_distinct_products e he F (by intro p; cases p <;> simp_all [F])
  have hprod (u : ℕ → ℝ) : (∏ p : K ⊕ L, F p (u (e p))) =
      (∏ k ∈ K, f k (u k)) * (∏ n ∈ L, g n (u n)) := by
    rw [Fintype.prod_sum_type]
    simp only [F, e, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.prod_coe_sort K (fun k => f k (u k)),
      Finset.prod_coe_sort L (fun k => g k (u k))]
  have hmean : (∏ p : K ⊕ L, ∫ x, F p x ∂uniformUnit) =
      (∏ k ∈ K, ∫ x, f k x ∂uniformUnit) * (∏ n ∈ L, ∫ x, g n x ∂uniformUnit) := by
    rw [Fintype.prod_sum_type]
    simp only [F, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.prod_coe_sort K (fun k => ∫ x, f k x ∂uniformUnit),
      Finset.prod_coe_sort L (fun k => ∫ x, g k x ∂uniformUnit)]
  simpa only [hprod, hmean] using h

def futureProduct (a b : ℕ) (g : ℝ → ℂ) (u : ℕ → ℝ) : ℂ :=
  ∏ n ∈ Finset.Ico a b, g (u n)

theorem measurable_futureProduct (a b : ℕ) (g : ℝ → ℂ) (hg : Measurable g) :
    Measurable (futureProduct a b g) :=
  Finset.measurable_prod _ (fun n _ => hg.comp (measurable_pi_apply n))

theorem norm_futureProduct_le_one (a b : ℕ) (g : ℝ → ℂ)
    (hg : ∀ x, ‖g x‖ ≤ 1) (u : ℕ → ℝ) : ‖futureProduct a b g u‖ ≤ 1 :=
  (Finset.norm_prod_le _ _).trans
    (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun n _ => hg (u n)))

/-- The future block may be empty: no assumption a ≤ b is needed. -/
theorem integral_past_future (K : Finset ℕ) (a b : ℕ) (hK : K ⊆ Finset.range a)
    (f : ℕ → ℝ → ℂ) (hf : ∀ k, Measurable (f k)) (g : ℝ → ℂ) (hg : Measurable g) :
    (∫ u, (∏ k ∈ K, f k (u k)) * futureProduct a b g u ∂unitMarksLaw) =
      (∏ k ∈ K, ∫ x, f k x ∂uniformUnit) * (∫ x, g x ∂uniformUnit) ^ (b - a) := by
  have hdis : Disjoint K (Finset.Ico a b) := by
    apply Finset.disjoint_left.mpr
    intro k hk hki
    exact (not_le_of_gt (Finset.mem_range.mp (hK hk))) (Finset.mem_Ico.mp hki).1
  simpa only [futureProduct, Finset.prod_const, Nat.card_Ico] using
    integral_disjoint_pair_products K (Finset.Ico a b) hdis f (fun _ => g) hf (fun _ => hg)

/-- A fixed-clock past cylinder: unarrived coordinates contribute deterministic values. -/
def censoredPast (K : Finset ℕ) (a : ℕ) (f : ℕ → ℝ → ℂ) (c : ℕ → ℂ)
    (u : ℕ → ℝ) : ℂ :=
  ∏ k ∈ K, if k < a then f k (u k) else c k

theorem measurable_censoredPast (K : Finset ℕ) (a : ℕ) (f : ℕ → ℝ → ℂ)
    (hf : ∀ k, Measurable (f k)) (c : ℕ → ℂ) : Measurable (censoredPast K a f c) := by
  apply Finset.measurable_prod
  intro k _
  by_cases hk : k < a
  · simp only [hk, if_true]
    exact (hf k).comp (measurable_pi_apply k)
  · simp only [hk, if_false]
    exact measurable_const

theorem norm_censoredPast_le_one (K : Finset ℕ) (a : ℕ) (f : ℕ → ℝ → ℂ)
    (hf : ∀ k x, ‖f k x‖ ≤ 1) (c : ℕ → ℂ) (hc : ∀ k, ‖c k‖ ≤ 1) (u : ℕ → ℝ) :
    ‖censoredPast K a f c u‖ ≤ 1 := by
  apply (Finset.norm_prod_le _ _).trans
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro k _
  split_ifs
  · exact hf k (u k)
  · exact hc k

/-- Censoring removes all mark dependence at indices in the future block. -/
theorem integral_censoredPast_future (K : Finset ℕ) (a b : ℕ)
    (f : ℕ → ℝ → ℂ) (hf : ∀ k, Measurable (f k)) (c : ℕ → ℂ)
    (g : ℝ → ℂ) (hg : Measurable g) :
    (∫ u, censoredPast K a f c u * futureProduct a b g u ∂unitMarksLaw) =
      (∏ k ∈ K, if k < a then ∫ x, f k x ∂uniformUnit else c k) *
        (∫ x, g x ∂uniformUnit) ^ (b - a) := by
  have hK : K.filter (fun k => k < a) ⊆ Finset.range a := by
    intro k hk
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
  simp only [censoredPast, Finset.prod_ite]
  have he (u : ℕ → ℝ) :
      ((∏ k ∈ K.filter (fun k => k < a), f k (u k)) *
        (∏ k ∈ K.filter (fun k => ¬k < a), c k)) * futureProduct a b g u =
      ((∏ k ∈ K.filter (fun k => k < a), f k (u k)) * futureProduct a b g u) *
        (∏ k ∈ K.filter (fun k => ¬k < a), c k) := by ring
  simp_rw [he]
  rw [integral_mul_const, integral_past_future _ a b hK f hf g hg]
  ring

theorem integral_censoredPast (K : Finset ℕ) (a : ℕ)
    (f : ℕ → ℝ → ℂ) (hf : ∀ k, Measurable (f k)) (c : ℕ → ℂ) :
    (∫ u, censoredPast K a f c u ∂unitMarksLaw) =
      ∏ k ∈ K, if k < a then ∫ x, f k x ∂uniformUnit else c k := by
  simpa [futureProduct] using
    integral_censoredPast_future K a a f hf c (fun _ => 1) measurable_const

/-- The same factorization written directly using the past cylinder's own expectation. -/
theorem integral_censoredPast_mul_future (K : Finset ℕ) (a b : ℕ)
    (f : ℕ → ℝ → ℂ) (hf : ∀ k, Measurable (f k)) (c : ℕ → ℂ)
    (g : ℝ → ℂ) (hg : Measurable g) :
    (∫ u, censoredPast K a f c u * futureProduct a b g u ∂unitMarksLaw) =
      (∫ u, censoredPast K a f c u ∂unitMarksLaw) *
        (∫ x, g x ∂uniformUnit) ^ (b - a) := by
  rw [integral_censoredPast_future K a b f hf c g hg, integral_censoredPast K a f hf c]

/-- Unit bounds give genuine integrability for later product-space Fubini arguments. -/
theorem integrable_censoredPast_future (K : Finset ℕ) (a b : ℕ)
    (f : ℕ → ℝ → ℂ) (hf : ∀ k, Measurable (f k)) (hfbound : ∀ k x, ‖f k x‖ ≤ 1)
    (c : ℕ → ℂ) (hc : ∀ k, ‖c k‖ ≤ 1) (g : ℝ → ℂ) (hg : Measurable g)
    (hgbound : ∀ x, ‖g x‖ ≤ 1) :
    Integrable (fun u => censoredPast K a f c u * futureProduct a b g u) unitMarksLaw := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_censoredPast K a f hf c).mul
      (measurable_futureProduct a b g hg)).aestronglyMeasurable
  filter_upwards [] with u
  rw [norm_mul]
  exact (mul_le_mul (norm_censoredPast_le_one K a f hfbound c hc u)
    (norm_futureProduct_le_one a b g hgbound u) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)

end CarryingCapacity.MarkedPastProducts
