import CarryingCapacity.PoissonFiniteDimensional
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Complex transforms of the actual Poisson counts

The generating-function identity is proved from the Poisson mass series,
including integrability, and transferred to the constructed clock and its
increments. No generating-function or characteristic-function law is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace CarryingCapacity.PoissonTransform
open CountableJumpProcess FrozenProcess PoissonIncrements

/-- A weighted Poisson term is a term in the complex exponential series. -/
theorem poisson_pow_term (r : ℝ≥0) (z : ℂ) (n : ℕ) :
    (poissonPMFReal r n : ℂ) * z^n =
      Complex.exp (-((r:ℝ):ℂ)) * ((((r:ℝ):ℂ)*z)^n / (n.factorial:ℂ)) := by
  simp only [poissonPMFReal,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_neg,Complex.ofReal_exp,Complex.ofReal_natCast,mul_pow]
  ring

/-- The complex Poisson power series converges for every complex argument. -/
theorem hasSum_poisson_pow (r : ℝ≥0) (z : ℂ) :
    HasSum (fun n : ℕ => (poissonPMFReal r n : ℂ) * z^n)
      (Complex.exp (((r:ℝ):ℂ)*(z-1))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp ℂ (((r:ℝ):ℂ)*z)).mul_left
    (Complex.exp (-((r:ℝ):ℂ)))
  simp only [← Complex.exp_eq_exp_ℂ,← Complex.exp_add] at h
  convert h using 1
  · funext n
    exact poisson_pow_term r z n
  · congr 1
    ring

/-- Absolute convergence of the weighted complex Poisson series. -/
theorem summable_norm_poisson_pow (r : ℝ≥0) (z : ℂ) :
    Summable (fun n : ℕ => ‖(poissonPMFReal r n : ℂ) * z^n‖) := by
  have h := (NormedSpace.norm_expSeries_div_summable ℂ (((r:ℝ):ℂ)*z)).mul_left
    ‖Complex.exp (-((r:ℝ):ℂ))‖
  simpa only [poisson_pow_term,norm_mul] using h

/-- Every complex power of the Poisson count is integrable, without a unit-disk restriction. -/
theorem integrable_poisson_pow (r : ℝ≥0) (z : ℂ) :
    Integrable (fun n : ℕ => z^n) (poissonMeasure r) := by
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm,lintegral_countable']
  have he (n : ℕ) : ENNReal.ofReal ‖z^n‖ * poissonMeasure r {n} =
      ENNReal.ofReal ‖(poissonPMFReal r n : ℂ) * z^n‖ := by
    rw [poissonMeasure,PMF.toMeasure_apply_singleton _ n (measurableSet_singleton n)]
    change ENNReal.ofReal ‖z^n‖ * ENNReal.ofReal (poissonPMFReal r n) = _
    rw [← ENNReal.ofReal_mul (norm_nonneg _)]
    congr 1
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg poissonPMFReal_nonneg]
    ring
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (summable_norm_poisson_pow r z)]
  exact ENNReal.ofReal_lt_top

/-- Exact complex generating-function expectation under the Poisson probability measure. -/
theorem integral_poisson_pow (r : ℝ≥0) (z : ℂ) :
    (∫ n : ℕ, z^n ∂poissonMeasure r) = Complex.exp (((r:ℝ):ℂ)*(z-1)) := by
  rw [integral_countable' (integrable_poisson_pow r z)]
  have hm (n : ℕ) : (poissonMeasure r).real {n} = poissonPMFReal r n := by
    rw [Measure.real,poissonMeasure,PMF.toMeasure_apply_singleton _ n (measurableSet_singleton n)]
    exact ENNReal.toReal_ofReal poissonPMFReal_nonneg
  simp_rw [hm,Complex.real_smul]
  exact (hasSum_poisson_pow r z).tsum_eq

/-- A finite product of arbitrary complex powers is integrable under independent Poisson laws. -/
theorem integrable_poisson_product {ι : Type*} [Fintype ι]
    (r : ι → ℝ≥0) (z : ι → ℂ) :
    Integrable (fun n : ι → ℕ => ∏ i, z i ^ n i)
      (Measure.pi (fun i => poissonMeasure (r i))) := by
  have h := @Integrable.fintype_prod_dep ℂ _ ι _ (fun _ : ι => ℕ)
    (fun i n => z i ^ n) (fun i => ⟨poissonMeasure (r i)⟩)
    (fun i => inferInstanceAs (SigmaFinite (poissonMeasure (r i))))
    (fun i => integrable_poisson_pow (r i) (z i))
  simpa only [volume_pi] using h

/-- The multivariate complex transform of a finite product of Poisson laws. -/
theorem integral_poisson_product {ι : Type*} [Fintype ι]
    (r : ι → ℝ≥0) (z : ι → ℂ) :
    (∫ n : ι → ℕ, ∏ i, z i ^ n i ∂Measure.pi (fun i => poissonMeasure (r i))) =
      Complex.exp (∑ i, ((r i : ℝ) : ℂ) * (z i - 1)) := by
  have h := @integral_fintype_prod_eq_prod ℂ _ ι _ (fun _ : ι => ℕ)
    (fun i n => z i ^ n) (fun i => ⟨poissonMeasure (r i)⟩)
    (fun i => inferInstanceAs (SigmaFinite (poissonMeasure (r i))))
  simpa only [volume_pi, integral_poisson_pow, Complex.exp_sum] using h

/-- Integrability of powers of the constructed proposal count. -/
theorem integrable_proposalCount_pow (r : ℝ) (hr : 0 < r) (T : ℝ) (hT : 0 ≤ T) (z : ℂ) :
    Integrable (fun ω => z^(proposalCount ω T)) (waitingTimeLaw r hr) := by
  have h := integrable_poisson_pow ⟨r*T,mul_nonneg hr.le hT⟩ z
  rw [← proposalCount_map r hr T hT] at h
  exact h.comp_measurable (measurable_proposalCount T)

/-- Complex generating-function expectation for the actual constructed count process. -/
theorem integral_proposalCount_pow (r : ℝ) (hr : 0 < r) (T : ℝ) (hT : 0 ≤ T) (z : ℂ) :
    (∫ ω, z^(proposalCount ω T) ∂waitingTimeLaw r hr) =
      Complex.exp (((r*T:ℝ):ℂ)*(z-1)) := by
  rw [← integral_map_of_stronglyMeasurable (measurable_proposalCount T)
    (measurable_of_countable (fun n : ℕ => z^n)).stronglyMeasurable,
    proposalCount_map r hr T hT,integral_poisson_pow]
  rfl

/-- Integrability of powers of a stationary increment of the constructed count process. -/
theorem integrable_increment_pow (r : ℝ) (hr : 0 < r) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (z : ℂ) :
    Integrable (fun ω => z^(increment ω s t)) (waitingTimeLaw r hr) := by
  have h := integrable_poisson_pow ⟨r*t,mul_nonneg hr.le ht⟩ z
  rw [← increment_map r hr s t hs ht] at h
  exact h.comp_measurable (measurable_increment s t)

/-- Complex generating-function expectation for a stationary increment. -/
theorem integral_increment_pow (r : ℝ) (hr : 0 < r) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (z : ℂ) :
    (∫ ω, z^(increment ω s t) ∂waitingTimeLaw r hr) =
      Complex.exp (((r*t:ℝ):ℂ)*(z-1)) := by
  rw [← integral_map_of_stronglyMeasurable (measurable_increment s t)
    (measurable_of_countable (fun n : ℕ => z^n)).stronglyMeasurable,
    increment_map r hr s t hs ht,integral_poisson_pow]
  rfl

end CarryingCapacity.PoissonTransform
