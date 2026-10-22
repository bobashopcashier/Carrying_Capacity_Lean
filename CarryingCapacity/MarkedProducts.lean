import CarryingCapacity.MarkedNoise
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Products of marks before the actual clock count

The uniform marks in the constructed strip are genuinely iid and independent
of its clock. Integrating a bounded finite product of marks first reduces the
random-count product to a power of the single-mark expectation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

namespace CarryingCapacity.MarkedProducts
open CountableJumpProcess FrozenProcess MarkedNoise

def prefixProduct (g : ℝ → ℂ) (n : ℕ) (u : ℕ → ℝ) : ℂ :=
  ∏ k ∈ Finset.range n, g (u k)

theorem measurable_prefixProduct (g : ℝ → ℂ) (hg : Measurable g) (n : ℕ) :
    Measurable (prefixProduct g n) := by
  exact Finset.measurable_prod _ (fun k _ => hg.comp (measurable_pi_apply k))

theorem measurable_prefixProduct_joint (g : ℝ → ℂ) (hg : Measurable g) :
    Measurable (fun p : ℕ × (ℕ → ℝ) => prefixProduct g p.1 p.2) := by
  have h : Measurable (fun p : (ℕ → ℝ) × ℕ => prefixProduct g p.2 p.1) :=
    measurable_from_prod_countable (fun n => measurable_prefixProduct g hg n)
  exact h.comp measurable_swap

theorem norm_prefixProduct_le_one (g : ℝ → ℂ) (hbound : ∀ x, ‖g x‖ ≤ 1)
    (n : ℕ) (u : ℕ → ℝ) : ‖prefixProduct g n u‖ ≤ 1 := by
  exact (Finset.norm_prod_le _ _).trans
    (Finset.prod_le_one (fun k _ => norm_nonneg _) (fun k _ => hbound (u k)))

theorem integral_prefixProduct (g : ℝ → ℂ) (hg : Measurable g) (n : ℕ) :
    (∫ u, prefixProduct g n u ∂unitMarksLaw) =
      (∫ x, g x ∂uniformUnit) ^ n := by
  let s := Finset.range n
  let f : (s → ℝ) → ℂ := fun u => ∏ k : s, g (u k)
  have hf : Measurable f := Finset.measurable_prod _ (fun k _ =>
    hg.comp (measurable_pi_apply k))
  have he (u : ℕ → ℝ) : prefixProduct g n u = f (s.restrict u) := by
    exact (Finset.prod_coe_sort s (fun k => g (u k))).symm
  simp_rw [he]
  rw [unitMarksLaw]
  rw [integral_restrict_infinitePi (μ := fun _ : ℕ => uniformUnit)
    (s := s) (f := f) hf.aestronglyMeasurable]
  letI : MeasureSpace ℝ := ⟨uniformUnit⟩
  letI : IsProbabilityMeasure (volume : Measure ℝ) :=
    FrozenProcess.uniformUnit_probability
  have h := integral_fintype_prod_eq_pow s g
  simpa only [f, volume_pi, Fintype.card_coe, s, Finset.card_range] using h

def clockProduct (g : ℝ → ℂ) (T : ℝ) (ω : StripSample) : ℂ :=
  prefixProduct g (proposalCount ω.1 T) ω.2

theorem measurable_clockProduct (g : ℝ → ℂ) (hg : Measurable g) (T : ℝ) :
    Measurable (clockProduct g T) :=
  (measurable_prefixProduct_joint g hg).comp
    (((measurable_proposalCount T).comp measurable_fst).prodMk measurable_snd)

theorem integrable_clockProduct (g : ℝ → ℂ) (hg : Measurable g)
    (hbound : ∀ x, ‖g x‖ ≤ 1) (T : ℝ) : Integrable (clockProduct g T) stripLaw := by
  exact (integrable_const (1 : ℝ)).mono'
    (measurable_clockProduct g hg T).aestronglyMeasurable
    (Eventually.of_forall (fun ω => norm_prefixProduct_le_one g hbound _ _))

/-- Fubini applies to the actual independent clock/marks product law. -/
theorem integral_clockProduct (g : ℝ → ℂ) (hg : Measurable g)
    (hbound : ∀ x, ‖g x‖ ≤ 1) (T : ℝ) :
    (∫ ω, clockProduct g T ω ∂stripLaw) =
      ∫ ω, (∫ x, g x ∂uniformUnit) ^ proposalCount ω T
        ∂waitingTimeLaw 1 (by norm_num) := by
  rw [stripLaw, integral_prod _ (integrable_clockProduct g hg hbound T)]
  apply integral_congr_ae
  filter_upwards [] with ω
  exact integral_prefixProduct g hg (proposalCount ω T)

end CarryingCapacity.MarkedProducts
