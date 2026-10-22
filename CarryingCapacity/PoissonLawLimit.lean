import CarryingCapacity.CountVectorTransform
import CarryingCapacity.PoissonTransform
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Limits of finite vectors with independent Poisson laws

Almost-sure eventual agreement of natural count vectors and convergence of
all intensity parameters determine the limiting product Poisson law. The
proof uses bounded complex power products, dominated convergence, and the
proved finite-vector transform uniqueness theorem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology

namespace CarryingCapacity.PoissonLawLimit

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Multivariate powers on the closed unit polydisk are uniformly bounded. -/
theorem norm_power_product_le_one (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (v : ι → ℕ) :
    ‖∏ i, z i ^ v i‖ ≤ 1 := by
  apply (Finset.norm_prod_le _ _).trans
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro i _
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (hz i)

/-- Product Poisson laws are closed under almost-sure eventual agreement of
the actual count vectors and coordinatewise convergence of their rates. -/
theorem map_eq_of_ae_eventually_eq
    (X : Ω → (ι → ℕ)) (hX : Measurable X)
    (Xₙ : ℕ → Ω → (ι → ℕ)) (hXₙ : ∀ n, Measurable (Xₙ n))
    (r : ι → ℝ≥0) (rₙ : ℕ → ι → ℝ≥0)
    (hr : ∀ i, Tendsto (fun n => (rₙ n i : ℝ)) atTop (𝓝 (r i : ℝ)))
    (hLaw : ∀ n, Measure.map (Xₙ n) μ = Measure.pi (fun i => poissonMeasure (rₙ n i)))
    (heq : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, Xₙ n ω = X ω) :
    Measure.map X μ = Measure.pi (fun i => poissonMeasure (r i)) := by
  apply CountVectorTransform.measure_eq_of_pow_integrals_fintype
  intro z hz
  let f : (ι → ℕ) → ℂ := fun v => ∏ i, z i ^ v i
  have hf : Measurable f := measurable_of_countable _
  have hlim : Tendsto (fun n => ∫ ω, f (Xₙ n ω) ∂μ) atTop
      (𝓝 (∫ ω, f (X ω) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => 1)
    · exact fun n => (hf.comp (hXₙ n)).aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      exact Eventually.of_forall (fun ω => norm_power_product_le_one z hz (Xₙ n ω))
    · filter_upwards [heq] with ω hω
      apply tendsto_const_nhds.congr'
      filter_upwards [hω] with n hn
      exact congrArg f hn.symm
  have hformula (n : ℕ) : (∫ ω, f (Xₙ n ω) ∂μ) =
      Complex.exp (∑ i, ((rₙ n i : ℝ) : ℂ) * (z i - 1)) := by
    rw [← integral_map_of_stronglyMeasurable (hXₙ n) hf.stronglyMeasurable, hLaw n]
    exact PoissonTransform.integral_poisson_product (rₙ n) z
  have hparam : Tendsto (fun n => Complex.exp (∑ i, ((rₙ n i : ℝ) : ℂ) * (z i - 1)))
      atTop (𝓝 (Complex.exp (∑ i, ((r i : ℝ) : ℂ) * (z i - 1)))) := by
    apply Complex.continuous_exp.continuousAt.tendsto.comp
    apply tendsto_finset_sum
    intro i _
    exact ((Complex.continuous_ofReal.continuousAt.tendsto).comp (hr i)).mul_const (z i - 1)
  simp_rw [← hformula] at hparam
  rw [integral_map_of_stronglyMeasurable hX hf.stronglyMeasurable,
    PoissonTransform.integral_poisson_product]
  exact tendsto_nhds_unique hlim hparam

end CarryingCapacity.PoissonLawLimit
