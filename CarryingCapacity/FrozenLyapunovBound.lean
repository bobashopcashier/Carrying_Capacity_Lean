import CarryingCapacity.InitialFrozenExpectation
import CarryingCapacity.IntegralGronwall

/-!
# Lyapunov expectation bounds for the actual frozen process

A generator drift bound on the finite active set is extended to inactive
states using nonnegativity of the Lyapunov function. The proved initialized
Dynkin and Fubini identities then imply the integral inequality for the actual
expectation. Integral Gronwall yields the exponential moment bound; no
expectation bound or differential inequality is supplied as an assumption.
-/

noncomputable section
open MeasureTheory Set Filter

namespace CarryingCapacity.FrozenLyapunovBound
open CommonInitialNoise FrozenProcess InitialFrozenExpectation

section Generator
variable {J E : Type*} [Fintype J] [DecidableEq E]

/-- Freezing makes the generator zero outside the active set, so a
nonnegative Lyapunov function extends the active-region drift bound globally. -/
theorem generator_le_of_active (active : Finset E) (jump : J → E → E)
    (rate : J → E → ℝ) (V : E → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hV : ∀ x, 0 ≤ V x)
    (hdrift : ∀ x ∈ active, frozenGenerator active jump rate V x ≤ b * (1 + V x))
    (x : E) : frozenGenerator active jump rate V x ≤ b * (1 + V x) := by
  by_cases hx : x ∈ active
  · exact hdrift x hx
  · rw [frozenGenerator, if_neg hx]
    exact mul_nonneg hb (by linarith [hV x])

end Generator

variable {A J E : Type*} [MeasurableSpace A] [Fintype J] [DecidableEq E]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ) (initial : A → E)

/-- The actual expected generator satisfies the Lyapunov drift inequality.
Integrability of the future test value is derived from its initial moment. -/
theorem expectedGenerator_le (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (b : ℝ)
    (hV : Integrable (fun a => V (initial a)) μ)
    (hdrift : ∀ x, frozenGenerator active jump rate V x ≤ b * (1 + V x)) (t : ℝ) :
    expectedGenerator active jump rate initial μ C V t ≤
      b * (1 + expectation active jump rate initial μ C V t) := by
  have hiV := InitialFrozenDynkin.integrable_testFunction active jump rate initial
    μ hinit C e V t hV
  have hiG : Integrable (fun p : Sample A J =>
      generatorField active jump rate initial C V (p,t)) (law μ J) :=
    integrable_generator_at active jump rate initial μ hinit C V t
  have h := integral_mono hiG ((integrable_const 1).add hiV |>.const_mul b)
    (fun p => hdrift (process active jump rate initial C p t))
  simpa only [expectedGenerator, expectation, integral_const_mul, Pi.add_apply,
    integral_add (integrable_const 1) hiV, integral_const,
    measureReal_univ_eq_one, one_smul] using h

/-- Adding one to the actual Lyapunov mean gives the integral inequality
obtained from Dynkin. -/
theorem one_add_expectation_integral_le (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (b : ℝ)
    (hq : ∀ y ∈ active, ∀ j, 0 ≤ rate j y)
    (hbound : ∀ y ∈ active, ∀ j, rate j y ≤ C)
    (hV : Integrable (fun a => V (initial a)) μ)
    (hdrift : ∀ x, frozenGenerator active jump rate V x ≤ b * (1 + V x))
    (t : ℝ) :
    1 + expectation active jump rate initial μ C V t ≤
      (1 + ∫ a, V (initial a) ∂μ) +
        b * ∫ s in Ioc 0 t, (1 + expectation active jump rate initial μ C V s) := by
  have hc := continuousOn_expectation active jump rate initial μ hinit C e V hq hbound hV
  have hiU : IntegrableOn (fun s => 1 + expectation active jump rate initial μ C V s)
      (Ioc 0 t) :=
    (continuousOn_const.add (hc.mono Icc_subset_Ici_self)).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hle := integral_mono
    (integrableOn_expectedGenerator active jump rate initial μ hinit C V 0 t)
    (hiU.const_mul b)
    (fun s => expectedGenerator_le active jump rate initial μ hinit C e V b hV hdrift s)
  rw [integral_const_mul] at hle
  rw [expectation_eq_initial_add_integral active jump rate initial μ hinit C e V t
    hq hbound hV]
  linarith

/-- Uniform exponential Lyapunov control derived for the actual randomly
initialized frozen construction. The constant is its actual initial moment. -/
theorem one_add_expectation_le (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hVnonneg : ∀ x, 0 ≤ V x)
    (hq : ∀ y ∈ active, ∀ j, 0 ≤ rate j y)
    (hbound : ∀ y ∈ active, ∀ j, rate j y ≤ C)
    (hV : Integrable (fun a => V (initial a)) μ)
    (hdrift : ∀ x ∈ active, frozenGenerator active jump rate V x ≤ b * (1 + V x))
    (T : ℝ) (hT : 0 ≤ T) :
    1 + expectation active jump rate initial μ C V T ≤
      (1 + ∫ a, V (initial a) ∂μ) * Real.exp (b * T) := by
  have hd := generator_le_of_active active jump rate V b hb hVnonneg hdrift
  have hc := continuousOn_expectation active jump rate initial μ hinit C e V hq hbound hV
  have hu : ContinuousOn (fun t => 1 + expectation active jump rate initial μ C V t)
      (Icc 0 T) := continuousOn_const.add (hc.mono Icc_subset_Ici_self)
  have hi : ∀ t ∈ Icc 0 T, 1 + expectation active jump rate initial μ C V t ≤
      (1 + ∫ a, V (initial a) ∂μ) +
        b * ∫ s in Ioc 0 t, (1 + expectation active jump rate initial μ C V s) :=
    fun t _ => one_add_expectation_integral_le active jump rate initial μ hinit C e V b
      hq hbound hV hd t
  exact @IntegralGronwall.endpoint_le_exp_mul
    (fun t => 1 + expectation active jump rate initial μ C V t)
    (1 + ∫ a, V (initial a) ∂μ) b T hT hu hb hi

/-- The unshifted mean satisfies the corresponding sharp affine-exponential
bound, including the `-1` term. -/
theorem expectation_le_exp_sub_one (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hVnonneg : ∀ x, 0 ≤ V x)
    (hq : ∀ y ∈ active, ∀ j, 0 ≤ rate j y)
    (hbound : ∀ y ∈ active, ∀ j, rate j y ≤ C)
    (hV : Integrable (fun a => V (initial a)) μ)
    (hdrift : ∀ x ∈ active, frozenGenerator active jump rate V x ≤ b * (1 + V x))
    (T : ℝ) (hT : 0 ≤ T) :
    expectation active jump rate initial μ C V T ≤
      (1 + ∫ a, V (initial a) ∂μ) * Real.exp (b * T) - 1 := by
  have h := one_add_expectation_le active jump rate initial μ hinit C e V b hb
    hVnonneg hq hbound hV hdrift T hT
  linarith

end CarryingCapacity.FrozenLyapunovBound
