import CarryingCapacity.Framework
import CarryingCapacity.MarkedCountMoments

/-!
# Positive increments from a shared Poisson height

The same height decides each coordinate's jump separately. Its positive cost
increment splits into three disjoint height regions: both jumps, the left jump
alone, and the right jump alone. Integration against nonnegative-height Lebesgue
measure gives exactly the manuscript's coupling activity, including the shared
jump term. These are deterministic identities, together with the finite-prefix
inequality used before applying predictable compensation.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ENNReal

namespace CarryingCapacity.SynchronousPositiveIncrement
open MarkedIntensity

variable {E J : Type*}

/-- Two acceptance decisions using the same actual proposal height. -/
def pairUpdate (jump : J → E → E) (j : J) (a b : ℝ) (x y : E) (u : ℝ) : E × E :=
  (if u ≤ a then jump j x else x, if u ≤ b then jump j y else y)

/-- The positive part of the cost increment, including a possible shared jump. -/
def positiveIncrement (ρ : E → E → ℝ) (jump : J → E → E) (j : J)
    (a b : ℝ) (x y : E) (u : ℝ) : ℝ :=
  max (ρ (pairUpdate jump j a b x y u).1 (pairUpdate jump j a b x y u).2 - ρ x y) 0

/-- The three height-region lengths multiplied by their positive increments. -/
def heightActivity (ρ : E → E → ℝ) (jump : J → E → E) (j : J)
    (a b : ℝ) (x y : E) : ℝ :=
  min a b * max (ρ (jump j x) (jump j y) - ρ x y) 0 +
    max (a - b) 0 * max (ρ (jump j x) y - ρ x y) 0 +
    max (b - a) 0 * max (ρ x (jump j y) - ρ x y) 0

theorem positiveIncrement_nonnegative (ρ : E → E → ℝ) (jump : J → E → E) (j : J)
    (a b : ℝ) (x y : E) (u : ℝ) : 0 ≤ positiveIncrement ρ jump j a b x y u :=
  le_max_right _ _

theorem heightActivity_nonnegative (ρ : E → E → ℝ) (jump : J → E → E) (j : J)
    (a b : ℝ) (x y : E) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ heightActivity ρ jump j a b x y :=
  add_nonneg (add_nonneg (mul_nonneg (le_min ha hb) (le_max_right _ _))
    (mul_nonneg (le_max_right _ _) (le_max_right _ _)))
    (mul_nonneg (le_max_right _ _) (le_max_right _ _))

/-- An exact pointwise partition; endpoints belong to the accepted regions. -/
theorem positiveIncrement_eq_indicators (ρ : E → E → ℝ) (jump : J → E → E) (j : J)
    (a b : ℝ) (x y : E) (u : ℝ) :
    positiveIncrement ρ jump j a b x y u =
      (Iic (min a b)).indicator (fun _ => max (ρ (jump j x) (jump j y) - ρ x y) 0) u +
      (Ioc b a).indicator (fun _ => max (ρ (jump j x) y - ρ x y) 0) u +
      (Ioc a b).indicator (fun _ => max (ρ x (jump j y) - ρ x y) 0) u := by
  by_cases hua : u ≤ a
  · by_cases hub : u ≤ b
    · simp [positiveIncrement, pairUpdate, Set.indicator_apply, le_min_iff, hua, hub,
        not_lt_of_ge hua, not_lt_of_ge hub]
    · simp [positiveIncrement, pairUpdate, Set.indicator_apply, le_min_iff, hua, hub,
        not_lt_of_ge hua, lt_of_not_ge hub]
  · by_cases hub : u ≤ b
    · simp [positiveIncrement, pairUpdate, Set.indicator_apply, le_min_iff, hua, hub,
        lt_of_not_ge hua, not_lt_of_ge hub]
    · simp [positiveIncrement, pairUpdate, Set.indicator_apply, le_min_iff, hua, hub]

/-- Height measurability needs no measurable structure on the state type. -/
theorem measurable_positiveIncrement (ρ : E → E → ℝ) (jump : J → E → E) (j : J)
    (a b : ℝ) (x y : E) : Measurable (positiveIncrement ρ jump j a b x y) := by
  have he := funext (positiveIncrement_eq_indicators ρ jump j a b x y)
  rw [he]
  exact ((measurable_const.indicator measurableSet_Iic).add
    (measurable_const.indicator measurableSet_Ioc)).add
      (measurable_const.indicator measurableSet_Ioc)

private theorem integrable_indicator_Iic_const (a c : ℝ) :
    Integrable ((Iic a).indicator (fun _ : ℝ => c)) positiveVolume := by
  rw [integrable_indicator_iff measurableSet_Iic]
  apply integrableOn_const.mpr (Or.inr _)
  rw [positiveVolume_Iic]
  exact ENNReal.ofReal_lt_top

private theorem integrable_indicator_Ioc_const (a b c : ℝ) :
    Integrable ((Ioc a b).indicator (fun _ : ℝ => c)) positiveVolume := by
  rw [integrable_indicator_iff measurableSet_Ioc]
  apply integrableOn_const.mpr (Or.inr _)
  exact (measure_mono Ioc_subset_Iic_self).trans_lt (by
    rw [positiveVolume_Iic]
    exact ENNReal.ofReal_lt_top)

/-- Each fixed-state positive height increment is genuinely integrable. -/
theorem integrable_positiveIncrement (ρ : E → E → ℝ) (jump : J → E → E) (j : J)
    (a b : ℝ) (x y : E) : Integrable (positiveIncrement ρ jump j a b x y) positiveVolume := by
  rw [funext (positiveIncrement_eq_indicators ρ jump j a b x y)]
  exact ((integrable_indicator_Iic_const _ _).add
    (integrable_indicator_Ioc_const _ _ _)).add (integrable_indicator_Ioc_const _ _ _)

/-- Integrating the actual shared-height decision gives all three terms of
the synchronous positive activity exactly. -/
theorem integral_positiveIncrement (ρ : E → E → ℝ) (jump : J → E → E) (j : J)
    (a b : ℝ) (x y : E) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ u, positiveIncrement ρ jump j a b x y u ∂positiveVolume) =
      heightActivity ρ jump j a b x y := by
  let fs : ℝ → ℝ := (Iic (min a b)).indicator
    (fun _ => max (ρ (jump j x) (jump j y) - ρ x y) 0)
  let fl : ℝ → ℝ := (Ioc b a).indicator (fun _ => max (ρ (jump j x) y - ρ x y) 0)
  let fr : ℝ → ℝ := (Ioc a b).indicator (fun _ => max (ρ x (jump j y) - ρ x y) 0)
  have hs : Integrable fs positiveVolume := integrable_indicator_Iic_const _ _
  have hl : Integrable fl positiveVolume := integrable_indicator_Ioc_const _ _ _
  have hr : Integrable fr positiveVolume := integrable_indicator_Ioc_const _ _ _
  rw [funext (positiveIncrement_eq_indicators ρ jump j a b x y)]
  change (∫ u, (fs u + fl u) + fr u ∂positiveVolume) = _
  rw [integral_add (f := fun u => fs u + fl u) (g := fr) (hs.add hl) hr,
    integral_add hs hl]
  simp only [fs, fl, fr, integral_indicator_const _ measurableSet_Iic,
    integral_indicator_const _ measurableSet_Ioc, measureReal_def, positiveVolume_Iic,
    MarkedCountMoments.positiveVolume_Ioc _ _ ha, MarkedCountMoments.positiveVolume_Ioc _ _ hb,
    ENNReal.toReal_ofReal (le_min ha hb), ENNReal.toReal_ofReal', smul_eq_mul]
  rfl

/-- The nonnegative integral form is suitable for predictable compensation
without any supplied sample-space integrability assumption. -/
theorem lintegral_positiveIncrement (ρ : E → E → ℝ) (jump : J → E → E) (j : J)
    (a b : ℝ) (x y : E) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫⁻ u, ENNReal.ofReal (positiveIncrement ρ jump j a b x y u) ∂positiveVolume) =
      ENNReal.ofReal (heightActivity ρ jump j a b x y) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_positiveIncrement ρ jump j a b x y)
    (Filter.Eventually.of_forall (positiveIncrement_nonnegative ρ jump j a b x y)),
    integral_positiveIncrement ρ jump j a b x y ha hb]

section Composition
variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]

/-- Arbitrary measurable state/rate/height fields can be substituted into
the shared-noise positive increment. This also applies to predictable spaces. -/
theorem measurable_positiveIncrement_comp (ρ : E → E → ℝ) (jump : J → E → E) (j : J)
    (a b u : Ω → ℝ) (X Y : Ω → E)
    (ha : Measurable a) (hb : Measurable b) (hu : Measurable u)
    (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun ω => positiveIncrement ρ jump j (a ω) (b ω) (X ω) (Y ω) (u ω)) := by
  have hx : Measurable (fun ω => if u ω ≤ a ω then jump j (X ω) else X ω) :=
    ((measurable_of_countable (jump j)).comp hX).ite (measurableSet_le hu ha) hX
  have hy : Measurable (fun ω => if u ω ≤ b ω then jump j (Y ω) else Y ω) :=
    ((measurable_of_countable (jump j)).comp hY).ite (measurableSet_le hu hb) hY
  exact (((measurable_of_countable (fun p : E × E => ρ p.1 p.2)).comp (hx.prodMk hy)).sub
    ((measurable_of_countable (fun p : E × E => ρ p.1 p.2)).comp (hX.prodMk hY))).max measurable_const

end Composition

/-- The height integrals reproduce the exact coupling activity used by the
manuscript assumptions, with no shared-jump term discarded. -/
theorem sum_integral_eq_couplingActivity {D : ℕ} (κ : MomentScale)
    (q : Rates D (MomentLaw κ D)) (x y : State D) (μ ν : MomentLaw κ D) :
    (∑ j, ∫ u, positiveIncrement (adaptedDistance κ) Jump.advance j
      (q.rate j x μ) (q.rate j y ν) x y u ∂positiveVolume) = couplingActivity κ q x y μ ν := by
  simp_rw [integral_positiveIncrement _ _ _ _ _ _ _ (q.nonnegative _ _ _) (q.nonnegative _ _ _)]
  rfl

/-- The same exact finite-label identity for extended nonnegative integrals. -/
theorem sum_lintegral_eq_couplingActivity {D : ℕ} (κ : MomentScale)
    (q : Rates D (MomentLaw κ D)) (x y : State D) (μ ν : MomentLaw κ D) :
    (∑ j, ∫⁻ u, ENNReal.ofReal (positiveIncrement (adaptedDistance κ) Jump.advance j
      (q.rate j x μ) (q.rate j y ν) x y u) ∂positiveVolume) =
      ENNReal.ofReal (couplingActivity κ q x y μ ν) := by
  simp_rw [lintegral_positiveIncrement _ _ _ _ _ _ _ (q.nonnegative _ _ _) (q.nonnegative _ _ _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => heightActivity_nonnegative _ _ j _ _ x y
    (q.nonnegative _ _ _) (q.nonnegative _ _ _))]
  rfl

/-- Any finite sequence is bounded at its endpoint by its initial value plus
all positive increments. No nonnegativity of the sequence is required. -/
theorem le_initial_add_positive_increments (d : ℕ → ℝ) (n : ℕ) :
    d n ≤ d 0 + ∑ k ∈ Finset.range n, max (d (k + 1) - d k) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hinc := le_max_left (d (n + 1) - d n) (0 : ℝ)
    linarith

/-- One common horizon bound holds for every prefix, hence bounds the running
maximum whenever the path is represented by a finite list of jumps. -/
theorem le_initial_add_positive_increments_of_le (d : ℕ → ℝ) {k n : ℕ} (hkn : k ≤ n) :
    d k ≤ d 0 + ∑ l ∈ Finset.range n, max (d (l + 1) - d l) 0 := by
  apply (le_initial_add_positive_increments d k).trans
  apply add_le_add_left
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkn)
    (fun _ _ _ => le_max_right _ _)

end CarryingCapacity.SynchronousPositiveIncrement
