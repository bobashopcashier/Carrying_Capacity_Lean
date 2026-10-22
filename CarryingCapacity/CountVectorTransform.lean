import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Uniqueness of finite count-vector laws from power transforms

The multivariate complex power transform on the unit torus determines every
finite measure on natural-valued vectors. The proof embeds the vectors in a
finite-dimensional real inner-product space, identifies their characteristic
functions, and pulls equality back through the injective embedding.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace CarryingCapacity.CountVectorTransform

variable {k : ℕ}

/-- The usual coordinatewise embedding of count vectors in Euclidean space. -/
def embedding (v : Fin k → ℕ) : EuclideanSpace ℝ (Fin k) :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm (fun i => (v i : ℝ))

theorem embedding_injective : Function.Injective (embedding (k := k)) := by
  intro v w h
  funext i
  have hi := congrArg (fun x : EuclideanSpace ℝ (Fin k) => x i) h
  exact Nat.cast_injective (show (v i : ℝ) = (w i : ℝ) from hi)

theorem measurable_embedding : Measurable (embedding (k := k)) :=
  measurable_of_countable _

/-- The Euclidean character factors into coordinatewise powers on the unit circle. -/
theorem exp_inner_embedding (v : Fin k → ℕ) (t : EuclideanSpace ℝ (Fin k)) :
    Complex.exp ((⟪embedding v, t⟫_ℝ : ℂ) * Complex.I) =
      ∏ i, Complex.exp ((t i : ℂ) * Complex.I) ^ v i := by
  simp only [PiLp.inner_apply, real_inner_comm, RCLike.inner_apply]
  change Complex.exp (((∑ i, t i * (v i : ℝ) : ℝ) : ℂ) * Complex.I) = _
  rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [Complex.ofReal_mul, Complex.ofReal_natCast, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- Equality of multivariate power integrals on the unit torus determines a
finite count-vector measure. This includes the empty vector (`k = 0`). -/
theorem measure_eq_of_pow_integrals_unit_circle (μ ν : Measure (Fin k → ℕ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ z : Fin k → ℂ, (∀ i, ‖z i‖ = 1) →
      (∫ v, ∏ i, z i ^ v i ∂μ) = ∫ v, ∏ i, z i ^ v i ∂ν) : μ = ν := by
  have he : μ.map embedding = ν.map embedding := by
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_apply, charFun_apply]
    rw [integral_map_of_stronglyMeasurable measurable_embedding
      (by apply Measurable.stronglyMeasurable; fun_prop),
      integral_map_of_stronglyMeasurable measurable_embedding
      (by apply Measurable.stronglyMeasurable; fun_prop)]
    simp_rw [exp_inner_embedding]
    exact h _ (fun i => Complex.norm_exp_ofReal_mul_I (t i))
  apply Measure.ext_of_singleton
  intro v
  have hv := congrArg (fun ξ : Measure (EuclideanSpace ℝ (Fin k)) => ξ {embedding v}) he
  dsimp only at hv
  rw [Measure.map_apply measurable_embedding (measurableSet_singleton _),
    Measure.map_apply measurable_embedding (measurableSet_singleton _)] at hv
  simpa only [Set.preimage, Set.mem_singleton_iff, embedding_injective.eq_iff,
    Set.setOf_eq_eq_singleton] using hv

/-- Equality of the power integrals on the closed unit polydisk also determines
the measure, since the torus is contained in that polydisk. -/
theorem measure_eq_of_pow_integrals (μ ν : Measure (Fin k → ℕ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ z : Fin k → ℂ, (∀ i, ‖z i‖ ≤ 1) →
      (∫ v, ∏ i, z i ^ v i ∂μ) = ∫ v, ∏ i, z i ^ v i ∂ν) : μ = ν :=
  measure_eq_of_pow_integrals_unit_circle μ ν (fun z hz => h z (fun i => (hz i).le))

/-- Reindexing gives the same uniqueness theorem for an arbitrary finite index
type, including product index types for time-window/category arrays. -/
theorem measure_eq_of_pow_integrals_fintype {ι : Type*} [Fintype ι]
    (μ ν : Measure (ι → ℕ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ z : ι → ℂ, (∀ i, ‖z i‖ ≤ 1) →
      (∫ v, ∏ i, z i ^ v i ∂μ) = ∫ v, ∏ i, z i ^ v i ∂ν) : μ = ν := by
  classical
  let e := Fintype.equivFin ι
  let f : (ι → ℕ) → (Fin (Fintype.card ι) → ℕ) := fun v j => v (e.symm j)
  let g : (Fin (Fintype.card ι) → ℕ) → (ι → ℕ) := fun v i => v (e i)
  have hf : Measurable f := measurable_of_countable _
  have hg : Measurable g := measurable_of_countable _
  have he : μ.map f = ν.map f := by
    apply measure_eq_of_pow_integrals
    intro z hz
    rw [integral_map_of_stronglyMeasurable hf (measurable_of_countable _).stronglyMeasurable,
      integral_map_of_stronglyMeasurable hf (measurable_of_countable _).stronglyMeasurable]
    have hv (v : ι → ℕ) : (∏ j, z j ^ f v j) = ∏ i, z (e i) ^ v i := by
      simpa only [f, Equiv.symm_apply_apply] using
        (e.prod_comp (fun j => z j ^ v (e.symm j))).symm
    simp_rw [hv]
    exact h (fun i => z (e i)) (fun i => hz (e i))
  have hgf : g ∘ f = id := by
    funext v i
    exact congrArg v (e.symm_apply_apply i)
  have hm := congrArg (fun ξ : Measure (Fin (Fintype.card ι) → ℕ) => ξ.map g) he
  dsimp only at hm
  rw [Measure.map_map hg hf, Measure.map_map hg hf, hgf, Measure.map_id, Measure.map_id] at hm
  exact hm

end CarryingCapacity.CountVectorTransform
