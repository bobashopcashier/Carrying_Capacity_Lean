import CarryingCapacity.PoissonTransform
import CarryingCapacity.CountVectorTransform

/-!
# Finite superposition of independent Poisson vectors

Independent vector-valued counts with product Poisson laws remain product
Poisson after coordinatewise summation. The component rates may differ between
vectors and coordinates. The proof derives the joint product measure from
independence, factors its complex power integral, and uses transform uniqueness.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace CarryingCapacity.PoissonSuperposition

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {m : ℕ} {ι : Type*} [Fintype ι]

/-- Coordinatewise superposition of finitely many count vectors. -/
def sumCounts (X : Fin m → Ω → (ι → ℕ)) (ω : Ω) (i : ι) : ℕ :=
  ∑ n, X n ω i

omit [Fintype ι] in
theorem measurable_sumCounts (X : Fin m → Ω → (ι → ℕ))
    (hX : ∀ n, Measurable (X n)) : Measurable (sumCounts X) := by
  apply measurable_pi_lambda
  intro i
  exact Finset.measurable_sum _ (fun n _ => (measurable_pi_apply i).comp (hX n))

omit [MeasurableSpace Ω] in
/-- Powers of a coordinatewise sum factor over the independent vector index. -/
theorem pow_sumCounts (X : Fin m → Ω → (ι → ℕ)) (z : ι → ℂ) (ω : Ω) :
    (∏ i, z i ^ sumCounts X ω i) = ∏ n, ∏ i, z i ^ X n ω i := by
  simp only [sumCounts, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_comm

/-- The complex transform of a superposition, obtained from the actual joint law. -/
theorem integral_sumCounts [IsProbabilityMeasure μ]
    (X : Fin m → Ω → (ι → ℕ)) (hX : ∀ n, Measurable (X n))
    (hInd : iIndepFun X μ) (r : Fin m → ι → ℝ≥0)
    (hLaw : ∀ n, Measure.map (X n) μ = Measure.pi (fun i => poissonMeasure (r n i)))
    (z : ι → ℂ) :
    (∫ ω, ∏ i, z i ^ sumCounts X ω i ∂μ) =
      Complex.exp (∑ i, (((∑ n, r n i : ℝ≥0) : ℝ) : ℂ) * (z i - 1)) := by
  have hJoint : Measure.map (fun ω n => X n ω) μ =
      Measure.pi (fun n => Measure.pi (fun i => poissonMeasure (r n i))) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun n => (hX n).aemeasurable)).mp hInd]
    simp_rw [hLaw]
  simp_rw [pow_sumCounts]
  rw [← integral_map_of_stronglyMeasurable (measurable_pi_lambda _ hX)
    (measurable_of_countable
      (fun v : Fin m → ι → ℕ => ∏ n, ∏ i, z i ^ v n i)).stronglyMeasurable,
    hJoint]
  have hProd := @integral_fintype_prod_eq_prod ℂ _ (Fin m) _
    (fun _ : Fin m => ι → ℕ) (fun _ v => ∏ i, z i ^ v i)
    (fun n => ⟨Measure.pi (fun i => poissonMeasure (r n i))⟩)
    (fun n => inferInstanceAs
      (SigmaFinite (Measure.pi (fun i => poissonMeasure (r n i)))))
  simp only [volume_pi, PoissonTransform.integral_poisson_product] at hProd
  rw [hProd, ← Complex.exp_sum]
  congr 1
  simp only [NNReal.coe_sum, Complex.ofReal_sum, Finset.sum_mul]
  exact Finset.sum_comm

/-- Independent Poisson vectors superpose to a product Poisson vector whose
coordinate rates are the sums of the input rates. No identical-law assumption is needed. -/
theorem sumCounts_map [IsProbabilityMeasure μ]
    (X : Fin m → Ω → (ι → ℕ)) (hX : ∀ n, Measurable (X n))
    (hInd : iIndepFun X μ) (r : Fin m → ι → ℝ≥0)
    (hLaw : ∀ n, Measure.map (X n) μ = Measure.pi (fun i => poissonMeasure (r n i))) :
    Measure.map (sumCounts X) μ =
      Measure.pi (fun i => poissonMeasure (∑ n, r n i)) := by
  apply CountVectorTransform.measure_eq_of_pow_integrals_fintype
  intro z _
  rw [integral_map_of_stronglyMeasurable (measurable_sumCounts X hX)
    (measurable_of_countable (fun v : ι → ℕ => ∏ i, z i ^ v i)).stronglyMeasurable,
    integral_sumCounts X hX hInd r hLaw z,
    PoissonTransform.integral_poisson_product]

/-- All complex power products of the superposed vector are integrable. -/
theorem integrable_sumCounts [IsProbabilityMeasure μ]
    (X : Fin m → Ω → (ι → ℕ)) (hX : ∀ n, Measurable (X n))
    (hInd : iIndepFun X μ) (r : Fin m → ι → ℝ≥0)
    (hLaw : ∀ n, Measure.map (X n) μ = Measure.pi (fun i => poissonMeasure (r n i)))
    (z : ι → ℂ) :
    Integrable (fun ω => ∏ i, z i ^ sumCounts X ω i) μ := by
  have h := PoissonTransform.integrable_poisson_product (fun i => ∑ n, r n i) z
  rw [← sumCounts_map X hX hInd r hLaw] at h
  exact h.comp_measurable (measurable_sumCounts X hX)

end CarryingCapacity.PoissonSuperposition
