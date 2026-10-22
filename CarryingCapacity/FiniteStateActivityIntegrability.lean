import CarryingCapacity.RandomEnvironmentCompensation
import CarryingCapacity.Freezing

/-!
# Finite states and integrable ordinary rates imply integrable comparison cost

A deterministic finite state set and its one-jump enlargement bound every
positive cost increment. The three synchronous regions therefore cost at most
a finite constant times the sum of the two ordinary rates. This discharges the
finite-right-side condition in the real form of Lemma 4.1 from its stated
finite-state and integrable-rate assumptions.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal

namespace CarryingCapacity.FiniteStateActivityIntegrability
open Freezing SynchronousPositiveIncrement RandomEnvironmentCompensation

variable {E J : Type*} [DecidableEq E] [Fintype J]
  (G : Finset E) (jump : J → E → E) (ρ : E → E → ℝ)

/-- An explicit finite bound on all costs in the one-jump enlargement. -/
def costBound : ℝ :=
  ∑ p ∈ (oneStepEnlargement G jump).product (oneStepEnlargement G jump), max (ρ p.1 p.2) 0

theorem costBound_nonnegative : 0 ≤ costBound G jump ρ :=
  Finset.sum_nonneg (fun _ _ => le_max_right _ _)

theorem cost_le_bound {x y : E}
    (hx : x ∈ oneStepEnlargement G jump) (hy : y ∈ oneStepEnlargement G jump) :
    ρ x y ≤ costBound G jump ρ := by
  unfold costBound
  apply (le_max_left (ρ x y) 0).trans
  exact Finset.single_le_sum (s := (oneStepEnlargement G jump).product (oneStepEnlargement G jump))
    (a := (x,y)) (f := fun p : E × E => max (ρ p.1 p.2) 0)
    (fun _ _ => le_max_right _ _) (Finset.mem_product.mpr ⟨hx,hy⟩)

/-- The full shared-plus-one-sided synchronous activity is bounded by the
sum of ordinary rates. The shared-jump term is retained. -/
theorem heightActivity_le (hρ : ∀ x y, 0 ≤ ρ x y) {x y : E}
    (hx : x ∈ G) (hy : y ∈ G) (j : J) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    heightActivity ρ jump j a b x y ≤ costBound G jump ρ * (a + b) := by
  have hx' := active_subset_enlargement G jump hx
  have hy' := active_subset_enlargement G jump hy
  have hjx := jump_mem_enlargement G jump hx j
  have hjy := jump_mem_enlargement G jump hy j
  have hC := costBound_nonnegative G jump ρ
  have h1 : max (ρ (jump j x) (jump j y) - ρ x y) 0 ≤ costBound G jump ρ :=
    max_le (by linarith [cost_le_bound G jump ρ hjx hjy,hρ x y]) hC
  have h2 : max (ρ (jump j x) y - ρ x y) 0 ≤ costBound G jump ρ :=
    max_le (by linarith [cost_le_bound G jump ρ hjx hy',hρ x y]) hC
  have h3 : max (ρ x (jump j y) - ρ x y) 0 ≤ costBound G jump ρ :=
    max_le (by linarith [cost_le_bound G jump ρ hx' hjy,hρ x y]) hC
  have hcoef : min a b + max (a-b) 0 + max (b-a) 0 ≤ a+b := by
    rcases le_total a b with hab | hba
    · rw [min_eq_left hab,max_eq_right (sub_nonpos.mpr hab),max_eq_left (sub_nonneg.mpr hab)]
      linarith
    · rw [min_eq_right hba,max_eq_left (sub_nonneg.mpr hba),max_eq_right (sub_nonpos.mpr hba)]
      linarith
  have hh := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left h1 (le_min ha hb))
    (mul_le_mul_of_nonneg_left h2 (le_max_right (a-b) 0)))
    (mul_le_mul_of_nonneg_left h3 (le_max_right (b-a) 0))
  have hc := mul_le_mul_of_nonneg_left hcoef hC
  unfold heightActivity
  nlinarith

variable {Ω V : Type*} (q : J → E → V → ℝ)
  (X Y : ℝ → Ω → E) (U W : ℝ → Ω → V)

theorem sum_currentActivity_le (hρ : ∀ x y, 0 ≤ ρ x y)
    (hq : ∀ j x u, 0 ≤ q j x u) (ω : Ω) (t : ℝ)
    (hx : X t ω ∈ G) (hy : Y t ω ∈ G) :
    (∑ j, currentActivity jump q X Y U W ρ j ω t) ≤
      costBound G jump ρ *
        ((∑ j, q j (X t ω) (U t ω)) + ∑ j, q j (Y t ω) (W t ω)) := by
  calc
    _ ≤ ∑ j, costBound G jump ρ *
        (q j (X t ω) (U t ω) + q j (Y t ω) (W t ω)) :=
      Finset.sum_le_sum (fun j _ => heightActivity_le G jump ρ hρ hx hy j _ _ (hq j _ _) (hq j _ _))
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_add_distrib]

variable [MeasurableSpace Ω] (P : Measure Ω)

/-- Finiteness of the actual stopped ordinary-rate expectation implies
finiteness of the exact synchronous positive-activity expectation. -/
theorem expected_activity_lt_top_of_rates
    (hρ : ∀ x y, 0 ≤ ρ x y) (hq : ∀ j x u, 0 ≤ q j x u)
    (τ : Ω → ℝ≥0∞) (T : ℝ) (μtime : Measure ℝ)
    (hstates : ∀ᵐ ω ∂P, ∀ t ∈ Ioc 0 T, ENNReal.ofReal t ≤ τ ω → X t ω ∈ G ∧ Y t ω ∈ G)
    (hrates : (∫⁻ ω, ∫⁻ t in Ioc 0 T, if ENNReal.ofReal t ≤ τ ω then
      ENNReal.ofReal ((∑ j, q j (X t ω) (U t ω)) + ∑ j, q j (Y t ω) (W t ω))
      else 0 ∂μtime ∂P) < ⊤) :
    (∫⁻ ω, ∫⁻ t in Ioc 0 T, if ENNReal.ofReal t ≤ τ ω then
      ENNReal.ofReal (∑ j, currentActivity jump q X Y U W ρ j ω t) else 0 ∂μtime ∂P) < ⊤ := by
  have hb : (∫⁻ ω, ∫⁻ t in Ioc 0 T, if ENNReal.ofReal t ≤ τ ω then
      ENNReal.ofReal (∑ j, currentActivity jump q X Y U W ρ j ω t) else 0 ∂μtime ∂P) ≤
      ENNReal.ofReal (costBound G jump ρ) *
        (∫⁻ ω, ∫⁻ t in Ioc 0 T, if ENNReal.ofReal t ≤ τ ω then
          ENNReal.ofReal ((∑ j, q j (X t ω) (U t ω)) + ∑ j, q j (Y t ω) (W t ω))
          else 0 ∂μtime ∂P) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [hstates] with ω hω
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    by_cases hs : ENNReal.ofReal t ≤ τ ω
    · simp only [hs,if_true]
      rw [← ENNReal.ofReal_mul (costBound_nonnegative G jump ρ)]
      exact ENNReal.ofReal_le_ofReal (sum_currentActivity_le G jump ρ q X Y U W hρ hq ω t
        (hω t ht hs).1 (hω t ht hs).2)
    · simp only [hs,if_false,mul_zero]
      exact le_rfl
  exact lt_of_le_of_lt hb (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hrates)

variable [IsProbabilityMeasure P]

include jump in
/-- The expected initial cost is finite for finite-state initial values. -/
theorem initial_cost_lintegral_lt_top (X₀ Y₀ : Ω → E)
    (hinit : ∀ᵐ ω ∂P, X₀ ω ∈ G ∧ Y₀ ω ∈ G) :
    (∫⁻ ω, ENNReal.ofReal (ρ (X₀ ω) (Y₀ ω)) ∂P) < ⊤ := by
  have hb : (∫⁻ ω, ENNReal.ofReal (ρ (X₀ ω) (Y₀ ω)) ∂P) ≤ ENNReal.ofReal (costBound G jump ρ) := by
    calc
      _ ≤ ∫⁻ _ : Ω, ENNReal.ofReal (costBound G jump ρ) ∂P := by
        apply lintegral_mono_ae
        filter_upwards [hinit] with ω hω
        exact ENNReal.ofReal_le_ofReal (cost_le_bound G jump ρ
          (active_subset_enlargement G jump hω.1) (active_subset_enlargement G jump hω.2))
      _ = _ := by simp
  exact lt_of_le_of_lt hb ENNReal.ofReal_lt_top

variable [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

include jump in
/-- Ordinary real integrability of the initial cost follows from its finite
state support and measurable initial states. -/
theorem integrable_initialCost (hρ : ∀ x y, 0 ≤ ρ x y) (X₀ Y₀ : Ω → E)
    (hX₀ : Measurable X₀) (hY₀ : Measurable Y₀)
    (hinit : ∀ᵐ ω ∂P, X₀ ω ∈ G ∧ Y₀ ω ∈ G) :
    Integrable (fun ω => ρ (X₀ ω) (Y₀ ω)) P := by
  apply (integrable_const (costBound G jump ρ)).mono'
    (((measurable_of_countable (fun p : E × E => ρ p.1 p.2)).comp
      (hX₀.prodMk hY₀)).aestronglyMeasurable)
  filter_upwards [hinit] with ω hω
  change ‖ρ (X₀ ω) (Y₀ ω)‖ ≤ costBound G jump ρ
  rw [Real.norm_of_nonneg (hρ _ _)]
  exact cost_le_bound G jump ρ
    (active_subset_enlargement G jump hω.1) (active_subset_enlargement G jump hω.2)

end CarryingCapacity.FiniteStateActivityIntegrability
