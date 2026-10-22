import CarryingCapacity.MarkedProducts
import CarryingCapacity.MarkedStripCounts
import CarryingCapacity.PoissonTransform
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

/-!
# Distributional identification of marked counts

Characteristic-function uniqueness identifies natural-valued count laws from
their complex power integrals. The mark factor records membership in an
arbitrary measurable category, including categories of probability zero.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace CarryingCapacity.MarkedThinning
open CountableJumpProcess FrozenProcess MarkedNoise MarkedProducts

/-- Unit-circle power integrals determine a finite measure on the naturals. -/
theorem natMeasure_eq_of_pow_integrals (μ ν : Measure ℕ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ z : ℂ, ‖z‖ ≤ 1 → (∫ n, z ^ n ∂μ) = ∫ n, z ^ n ∂ν) : μ = ν := by
  have he : Measure.map (fun n : ℕ => (n : ℝ)) μ =
      Measure.map (fun n : ℕ => (n : ℝ)) ν := by
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_apply_real, charFun_apply_real]
    rw [integral_map_of_stronglyMeasurable (measurable_of_countable _)
      (by apply Measurable.stronglyMeasurable; fun_prop),
      integral_map_of_stronglyMeasurable (measurable_of_countable _)
      (by apply Measurable.stronglyMeasurable; fun_prop)]
    have hx (n : ℕ) : Complex.exp ((t : ℂ) * (n : ℂ) * Complex.I) =
        Complex.exp ((t : ℂ) * Complex.I) ^ n := by
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
    change (∫ n : ℕ, Complex.exp ((t : ℂ) * (n : ℂ) * Complex.I) ∂μ) =
      ∫ n : ℕ, Complex.exp ((t : ℂ) * (n : ℂ) * Complex.I) ∂ν
    simp_rw [hx]
    exact h _ (by simp [Complex.norm_exp_ofReal_mul_I])
  apply Measure.ext_of_singleton
  intro n
  have hn := congrArg (fun ξ : Measure ℝ => ξ {(n : ℝ)}) he
  dsimp only at hn
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)] at hn
  simpa only [preimage, mem_singleton_iff, Nat.cast_inj, setOf_eq_eq_singleton] using hn

def markFactor (B : Set ℝ) (z : ℂ) (x : ℝ) : ℂ := by
  classical
  exact if x ∈ B then z else 1

theorem measurable_markFactor (B : Set ℝ) (hB : MeasurableSet B) (z : ℂ) :
    Measurable (markFactor B z) := by
  classical
  exact Measurable.ite hB measurable_const measurable_const

theorem norm_markFactor_le_one (B : Set ℝ) (z : ℂ) (hz : ‖z‖ ≤ 1) (x : ℝ) :
    ‖markFactor B z x‖ ≤ 1 := by
  unfold markFactor
  split_ifs
  · exact hz
  · simp

theorem integral_markFactor (B : Set ℝ) (hB : MeasurableSet B) (z : ℂ) :
    (∫ x, markFactor B z x ∂uniformUnit) =
      1 + (uniformUnit.real B : ℂ) * (z - 1) := by
  have he : markFactor B z = (fun _ => (1 : ℂ)) + B.indicator (fun _ => z - 1) := by
    funext x
    simp only [Pi.add_apply, markFactor]
    by_cases hx : x ∈ B <;> simp [hx]
  rw [he]
  simp only [Pi.add_apply]
  rw [integral_add (integrable_const _) ((integrable_const _).indicator hB),
    integral_const, integral_indicator_const _ hB]
  simp [Complex.real_smul]

/-- Exact generating function for a category of the actual marked strip. -/
theorem integral_clockCount_pow (B : Set ℝ) (hB : MeasurableSet B)
    (T : ℝ) (hT : 0 ≤ T) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    (∫ ω, z ^ MarkedStripCounts.clockCount B T ω ∂stripLaw) =
      Complex.exp (((T * uniformUnit.real B : ℝ) : ℂ) * (z - 1)) := by
  have he (ω : StripSample) : z ^ MarkedStripCounts.clockCount B T ω =
      clockProduct (markFactor B z) T ω :=
    (MarkedStripCounts.clockProduct_indicator_eq_pow B z T ω).symm
  simp_rw [he]
  rw [integral_clockProduct _ (measurable_markFactor B hB z)
    (norm_markFactor_le_one B z hz),
    PoissonTransform.integral_proposalCount_pow 1 (by norm_num) T hT,
    integral_markFactor B hB z]
  congr 1
  push_cast
  ring

/-- A measurable category has the genuine Poisson law, including zero intensity. -/
theorem clockCount_map (B : Set ℝ) (hB : MeasurableSet B)
    (T : ℝ) (hT : 0 ≤ T) :
    Measure.map (MarkedStripCounts.clockCount B T) stripLaw =
      poissonMeasure ⟨T * uniformUnit.real B, mul_nonneg hT (measureReal_nonneg)⟩ := by
  apply natMeasure_eq_of_pow_integrals
  intro z hz
  rw [integral_map_of_stronglyMeasurable
    (MarkedStripCounts.measurable_clockCount B hB T)
    (measurable_of_countable _).stronglyMeasurable,
    integral_clockCount_pow B hB T hT z hz, PoissonTransform.integral_poisson_pow]
  rfl

end CarryingCapacity.MarkedThinning
