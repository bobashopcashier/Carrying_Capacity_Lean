import CarryingCapacity.TimeDependentNonexplosion
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Passing finite-level moment bounds to the actual patch

Finite-horizon agreement gives eventual equality of the localized and global
states at every fixed time. Fatou's lemma therefore transfers a level-uniform
nonnegative Lyapunov bound to the measurable global process and proves its
integrability. No global integrability or uniform integrability is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

namespace CarryingCapacity.TimeDependentGlobalMoment
open CommonInitialNoise LyapunovLocalization TimeDependentLocalization

variable {A E J : Type*} [MeasurableSpace A] [DecidableEq E] [Fintype J]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (hbounded : ∀ n : ℕ, ∃ C : ℝ, ∀ x ∈ active V hfinite n, ∀ j t, rate j t x ≤ C)
  (initial : A → E) (e : E)
  (μ : Measure A) (hRate : ∀ j x, Measurable (fun t => rate j t x))
  (hinit : Measurable initial)
include hRate hinit

omit [BorelSpace E] in
/-- Fatou applied to eventual equality of the actual localizations. -/
theorem lintegral_le_of_bounds
    (hV : ∀ x, 0 ≤ V x) (T : ℝ) (hT : 0 ≤ T) (B : ℝ)
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ S : ℝ≥0, ∃ n,
      (S : ℝ≥0∞) < exit V hfinite jump rate hbounded initial n p)
    (hi : ∀ n, Integrable (fun p => V (path V hfinite jump rate hbounded initial n p T)) (law μ J))
    (hmean : ∀ n, (∫ p, V (path V hfinite jump rate hbounded initial n p T) ∂law μ J) ≤ B) :
    (∫⁻ p, ENNReal.ofReal (V (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p T))
      ∂law μ J) ≤ ENNReal.ofReal B := by
  let f : ℕ → Sample A J → ℝ≥0∞ :=
    fun n p => ENNReal.ofReal (V (path V hfinite jump rate hbounded initial n p T))
  have hm (n : ℕ) : Measurable (f n) :=
    ((measurable_of_countable V).comp
      ((measurable_path V hfinite jump rate hbounded initial hRate hinit n).comp
        (measurable_id.prodMk measurable_const))).ennreal_ofReal
  have he : (fun p => ENNReal.ofReal
      (V (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p T))) =ᵐ[law μ J]
      (fun p => liminf (fun n => f n p) atTop) := by
    filter_upwards [TimeDependentGlobalProcess.ae_agrees_on_horizon
      V hfinite jump rate hbounded initial e μ hexhaust] with p hp
    obtain ⟨n, hn⟩ := hp ⟨T, hT⟩
    have hlim : Tendsto (fun m => f m p) atTop
        (𝓝 (ENNReal.ofReal (V (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p T)))) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop n] with m hm
      exact congrArg (fun x => ENNReal.ofReal (V x)) (hn m hm T hT le_rfl)
    exact hlim.liminf_eq.symm
  rw [lintegral_congr_ae he]
  refine (lintegral_liminf_le hm).trans ?_
  apply liminf_le_of_frequently_le'
  apply Eventually.frequently
  apply Eventually.of_forall
  intro n
  change (∫⁻ p, ENNReal.ofReal (V (path V hfinite jump rate hbounded initial n p T)) ∂law μ J) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (Eventually.of_forall (fun _ => hV _))]
  exact ENNReal.ofReal_le_ofReal (hmean n)

/-- A finite level-uniform mean bound proves actual global integrability. -/
theorem integrable_of_bounds
    (hV : ∀ x, 0 ≤ V x) (T : ℝ) (hT : 0 ≤ T) (B : ℝ)
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ S : ℝ≥0, ∃ n,
      (S : ℝ≥0∞) < exit V hfinite jump rate hbounded initial n p)
    (hi : ∀ n, Integrable (fun p => V (path V hfinite jump rate hbounded initial n p T)) (law μ J))
    (hmean : ∀ n, (∫ p, V (path V hfinite jump rate hbounded initial n p T) ∂law μ J) ≤ B) :
    Integrable (fun p => V (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p T))
      (law μ J) := by
  have hpair : Measurable (fun p : Sample A J => (p, T)) :=
    measurable_id.prodMk measurable_const
  have hp := (TimeDependentGlobalProcess.measurable_process V hfinite jump rate hbounded initial e hRate hinit).comp hpair
  have hm : Measurable (fun p => V
      (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p T)) :=
    (measurable_of_countable V).comp hp
  exact (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Eventually.of_forall (fun _ => hV _))).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (lintegral_le_of_bounds V hfinite jump rate hbounded initial e μ hRate hinit hV T hT B hexhaust hi hmean))

/-- The same real-valued bound is retained by the actual global path. -/
theorem expectation_le_of_bounds
    (hV : ∀ x, 0 ≤ V x) (T : ℝ) (hT : 0 ≤ T) (B : ℝ) (hB : 0 ≤ B)
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ S : ℝ≥0, ∃ n,
      (S : ℝ≥0∞) < exit V hfinite jump rate hbounded initial n p)
    (hi : ∀ n, Integrable (fun p => V (path V hfinite jump rate hbounded initial n p T)) (law μ J))
    (hmean : ∀ n, (∫ p, V (path V hfinite jump rate hbounded initial n p T) ∂law μ J) ≤ B) :
    (∫ p, V (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p T) ∂law μ J) ≤ B := by
  have hb := lintegral_le_of_bounds V hfinite jump rate hbounded initial e μ hRate hinit hV T hT B hexhaust hi hmean
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_of_bounds V hfinite jump rate hbounded initial e μ hRate hinit hV T hT B hexhaust hi hmean)
      (Eventually.of_forall (fun _ => hV _))] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hb

section Actual
open TimeDependentNonexplosion
variable [IsProbabilityMeasure μ] (b : ℝ) (hb : 0 ≤ b)
  (hVnonneg : ∀ x, 0 ≤ V x) (hq : ∀ x j t, 0 ≤ t → 0 ≤ rate j t x)
  (hV : Integrable (fun a => V (initial a)) μ)
  (hdrift : ∀ x t, 0 ≤ t → (∑ j, rate j t x * (V (jump j x) - V x)) ≤ b * (1 + V x))
include hb hVnonneg hq hV hdrift

/-- The actual global Lyapunov value is integrable; exhaustion and all finite-level
bounds are discharged by the time-dependent Lyapunov argument. -/
theorem integrable (T : ℝ) (hT : 0 ≤ T) :
    Integrable (fun p => V (TimeDependentGlobalProcess.process
      V hfinite jump rate hbounded initial e p T)) (law μ J) :=
  integrable_of_bounds V hfinite jump rate hbounded initial e μ hRate hinit hVnonneg T hT
    (exponentialBound V initial μ b T)
    (ae_exhaustive V hfinite jump rate hbounded initial e μ hRate hinit b hb hVnonneg hq hV hdrift)
    (fun n => integrable_localized_value V hfinite jump rate hbounded initial e μ hRate hinit hV n T)
    (fun n => localized_expectation_le V hfinite jump rate hbounded initial e μ hRate hinit b hb
      hVnonneg hq hV hdrift n T hT)

/-- The extended Lyapunov moment of the actual global process has the same
finite affine-exponential bound as the finite-state constructions. -/
theorem lintegral_le (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ p, ENNReal.ofReal (V (TimeDependentGlobalProcess.process
      V hfinite jump rate hbounded initial e p T)) ∂law μ J) ≤
      ENNReal.ofReal (exponentialBound V initial μ b T) :=
  lintegral_le_of_bounds V hfinite jump rate hbounded initial e μ hRate hinit hVnonneg T hT
    (exponentialBound V initial μ b T)
    (ae_exhaustive V hfinite jump rate hbounded initial e μ hRate hinit b hb hVnonneg hq hV hdrift)
    (fun n => integrable_localized_value V hfinite jump rate hbounded initial e μ hRate hinit hV n T)
    (fun n => localized_expectation_le V hfinite jump rate hbounded initial e μ hRate hinit b hb
      hVnonneg hq hV hdrift n T hT)

/-- The actual real-valued global expectation retains the subtract-one bound. -/
theorem expectation_le (T : ℝ) (hT : 0 ≤ T) :
    (∫ p, V (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p T)
      ∂law μ J) ≤ exponentialBound V initial μ b T := by
  have hB : 0 ≤ exponentialBound V initial μ b T := by
    have hm : 0 ≤ ∫ a, V (initial a) ∂μ := integral_nonneg (fun _ => hVnonneg _)
    have he : 1 ≤ Real.exp (b * T) := Real.one_le_exp_iff.mpr (mul_nonneg hb hT)
    have hp : (1 : ℝ) ≤ (1 + ∫ a, V (initial a) ∂μ) * Real.exp (b * T) := by
      calc
        1 = 1 * 1 := by ring
        _ ≤ (1 + ∫ a, V (initial a) ∂μ) * Real.exp (b * T) :=
          mul_le_mul (by linarith) he (by norm_num) (by linarith)
    exact sub_nonneg.mpr hp
  exact expectation_le_of_bounds V hfinite jump rate hbounded initial e μ hRate hinit hVnonneg T hT
    (exponentialBound V initial μ b T) hB
    (ae_exhaustive V hfinite jump rate hbounded initial e μ hRate hinit b hb hVnonneg hq hV hdrift)
    (fun n => integrable_localized_value V hfinite jump rate hbounded initial e μ hRate hinit hV n T)
    (fun n => localized_expectation_le V hfinite jump rate hbounded initial e μ hRate hinit b hb
      hVnonneg hq hV hdrift n T hT)

end Actual

end CarryingCapacity.TimeDependentGlobalMoment
