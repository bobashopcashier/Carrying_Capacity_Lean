import CarryingCapacity.MarkedBlockProducts
import CarryingCapacity.PoissonTransform

/-!
# Products of marks on the actual random time-grid blocks

After fixing the clock, successive time windows select disjoint deterministic
mark-index blocks. Their mark integral depends only on the block lengths.
The proved clock increment law then evaluates the outer integral.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace CarryingCapacity.MarkedTimeProducts
open CountableJumpProcess FrozenProcess MarkedNoise MarkedBlockProducts

variable {q : ℕ}

def blockProduct (g : Fin q → ℝ → ℂ) (f : Fin (q+1) → ℕ) (v : ℕ → ℝ) : ℂ :=
  ∏ a, ∏ n ∈ Finset.Ico (f a.castSucc) (f a.succ), g a (v n)

theorem measurable_blockProduct (g : Fin q → ℝ → ℂ)
    (hg : ∀ a, Measurable (g a)) (f : Fin (q+1) → ℕ) :
    Measurable (blockProduct g f) := by
  exact Finset.measurable_prod _ (fun a _ => Finset.measurable_prod _
    (fun n _ => (hg a).comp (measurable_pi_apply n)))

theorem measurable_blockProduct_joint (g : Fin q → ℝ → ℂ)
    (hg : ∀ a, Measurable (g a)) :
    Measurable (fun p : (Fin (q+1) → ℕ) × (ℕ → ℝ) => blockProduct g p.1 p.2) := by
  have h : Measurable (fun p : (ℕ → ℝ) × (Fin (q+1) → ℕ) => blockProduct g p.2 p.1) :=
    measurable_from_prod_countable (fun f => measurable_blockProduct g hg f)
  exact h.comp measurable_swap

theorem norm_blockProduct_le_one (g : Fin q → ℝ → ℂ)
    (hb : ∀ a x, ‖g a x‖ ≤ 1) (f : Fin (q+1) → ℕ) (v : ℕ → ℝ) :
    ‖blockProduct g f v‖ ≤ 1 := by
  apply (Finset.norm_prod_le _ _).trans
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro a _
  exact (Finset.norm_prod_le _ _).trans
    (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun n _ => hb a (v n)))

def timeProduct (g : Fin q → ℝ → ℂ) (u : Fin (q+1) → ℝ) (ω : StripSample) : ℂ :=
  blockProduct g (fun a => proposalCount ω.1 (u a)) ω.2

set_option maxHeartbeats 1000000 in
theorem measurable_timeProduct (g : Fin q → ℝ → ℂ)
    (hg : ∀ a, Measurable (g a)) (u : Fin (q+1) → ℝ) :
    Measurable (timeProduct g u) := by
  have hc : Measurable (fun ω : StripSample => fun a : Fin (q+1) =>
      proposalCount ω.1 (u a)) := measurable_pi_lambda _ (fun a =>
        (measurable_proposalCount (u a)).comp measurable_fst)
  exact (measurable_blockProduct_joint g hg).comp (hc.prodMk measurable_snd)

theorem integrable_timeProduct (g : Fin q → ℝ → ℂ)
    (hg : ∀ a, Measurable (g a)) (hb : ∀ a x, ‖g a x‖ ≤ 1)
    (u : Fin (q+1) → ℝ) : Integrable (timeProduct g u) stripLaw :=
  (integrable_const (1 : ℝ)).mono' (measurable_timeProduct g hg u).aestronglyMeasurable
    (Eventually.of_forall (fun _ => norm_blockProduct_le_one g hb _ _))

/-- Actual random block products have the exponential transform of clock increments. -/
theorem integral_timeProduct (g : Fin q → ℝ → ℂ)
    (hg : ∀ a, Measurable (g a)) (hb : ∀ a x, ‖g a x‖ ≤ 1)
    (u : Fin (q+1) → ℝ) (hu : Monotone u) (hu0 : 0 ≤ u 0) :
    (∫ ω, timeProduct g u ω ∂stripLaw) =
      Complex.exp (∑ a, ((u a.succ - u a.castSucc : ℝ) : ℂ) *
        ((∫ x, g a x ∂uniformUnit) - 1)) := by
  rw [stripLaw, integral_prod _ (integrable_timeProduct g hg hb u)]
  have he : (∫ ω, ∫ v, timeProduct g u (ω,v) ∂unitMarksLaw
      ∂waitingTimeLaw 1 (by norm_num)) =
      ∫ ω, ∏ a, (∫ x, g a x ∂uniformUnit) ^
        (proposalCount ω (u a.succ) - proposalCount ω (u a.castSucc))
        ∂waitingTimeLaw 1 (by norm_num) := by
    apply integral_congr_ae
    filter_upwards [ae_locally_finite 1 (by norm_num)] with ω hω
    exact integral_endpoint_products (fun a => proposalCount ω (u a))
      ((proposalCount_mono hω.2).comp hu) g hg
  rw [he]
  have hm : Measurable (fun ω : ClockSpace => fun a : Fin q =>
      proposalCount ω (u a.succ) - proposalCount ω (u a.castSucc)) :=
    measurable_pi_lambda _ (fun a => (measurable_proposalCount (u a.succ)).sub
      (measurable_proposalCount (u a.castSucc)))
  rw [← integral_map_of_stronglyMeasurable hm
    (measurable_of_countable (fun v : Fin q → ℕ =>
      ∏ a, (∫ x, g a x ∂uniformUnit) ^ v a)).stronglyMeasurable,
    PoissonFiniteDimensional.increments_at_times_map 1 (by norm_num) u hu hu0,
    PoissonTransform.integral_poisson_product]
  simp only [one_mul]
  rfl

end CarryingCapacity.MarkedTimeProducts
