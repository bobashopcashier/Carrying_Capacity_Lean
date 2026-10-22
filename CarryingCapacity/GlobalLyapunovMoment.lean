import CarryingCapacity.GlobalLocalizedProcess
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

namespace CarryingCapacity.GlobalLyapunovMoment
open CommonInitialNoise LyapunovLocalization

variable {A E J : Type*} [MeasurableSpace A] [DecidableEq E] [Fintype J]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → E → ℝ) (initial : A → E) (e : E)
  (μ : Measure A) (hinit : Measurable initial)
include hinit

omit [BorelSpace E] in
/-- Fatou applied to eventual equality of the actual localizations. -/
theorem lintegral_le
    (hV : ∀ x, 0 ≤ V x) (T : ℝ) (hT : 0 ≤ T) (B : ℝ)
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ S : ℝ≥0, ∃ n,
      (S : ℝ≥0∞) < exit V hfinite jump rate initial n p)
    (hi : ∀ n, Integrable (fun p => V (path V hfinite jump rate initial n p T)) (law μ J))
    (hmean : ∀ n, (∫ p, V (path V hfinite jump rate initial n p T) ∂law μ J) ≤ B) :
    (∫⁻ p, ENNReal.ofReal (V (GlobalLocalizedProcess.process V hfinite jump rate initial e p T))
      ∂law μ J) ≤ ENNReal.ofReal B := by
  let f : ℕ → Sample A J → ℝ≥0∞ :=
    fun n p => ENNReal.ofReal (V (path V hfinite jump rate initial n p T))
  have hm (n : ℕ) : Measurable (f n) :=
    ((measurable_of_countable V).comp
      ((measurable_path V hfinite jump rate initial hinit n).comp
        (measurable_id.prodMk measurable_const))).ennreal_ofReal
  have he : (fun p => ENNReal.ofReal
      (V (GlobalLocalizedProcess.process V hfinite jump rate initial e p T))) =ᵐ[law μ J]
      (fun p => liminf (fun n => f n p) atTop) := by
    filter_upwards [GlobalLocalizedProcess.ae_agrees_on_horizon
      V hfinite jump rate initial e μ hexhaust] with p hp
    obtain ⟨n, hn⟩ := hp ⟨T, hT⟩
    have hlim : Tendsto (fun m => f m p) atTop
        (𝓝 (ENNReal.ofReal (V (GlobalLocalizedProcess.process V hfinite jump rate initial e p T)))) := by
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
  change (∫⁻ p, ENNReal.ofReal (V (path V hfinite jump rate initial n p T)) ∂law μ J) ≤ _
  rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (Eventually.of_forall (fun _ => hV _))]
  exact ENNReal.ofReal_le_ofReal (hmean n)

/-- A finite level-uniform mean bound proves actual global integrability. -/
theorem integrable
    (hV : ∀ x, 0 ≤ V x) (T : ℝ) (hT : 0 ≤ T) (B : ℝ)
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ S : ℝ≥0, ∃ n,
      (S : ℝ≥0∞) < exit V hfinite jump rate initial n p)
    (hi : ∀ n, Integrable (fun p => V (path V hfinite jump rate initial n p T)) (law μ J))
    (hmean : ∀ n, (∫ p, V (path V hfinite jump rate initial n p T) ∂law μ J) ≤ B) :
    Integrable (fun p => V (GlobalLocalizedProcess.process V hfinite jump rate initial e p T))
      (law μ J) := by
  have hpair : Measurable (fun p : Sample A J => (p, T)) :=
    measurable_id.prodMk measurable_const
  have hp := (GlobalLocalizedProcess.measurable_process V hfinite jump rate initial e hinit).comp hpair
  have hm : Measurable (fun p => V
      (GlobalLocalizedProcess.process V hfinite jump rate initial e p T)) :=
    (measurable_of_countable V).comp hp
  exact (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Eventually.of_forall (fun _ => hV _))).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (lintegral_le V hfinite jump rate initial e μ hinit hV T hT B hexhaust hi hmean))

/-- The same real-valued bound is retained by the actual global path. -/
theorem expectation_le
    (hV : ∀ x, 0 ≤ V x) (T : ℝ) (hT : 0 ≤ T) (B : ℝ) (hB : 0 ≤ B)
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ S : ℝ≥0, ∃ n,
      (S : ℝ≥0∞) < exit V hfinite jump rate initial n p)
    (hi : ∀ n, Integrable (fun p => V (path V hfinite jump rate initial n p T)) (law μ J))
    (hmean : ∀ n, (∫ p, V (path V hfinite jump rate initial n p T) ∂law μ J) ≤ B) :
    (∫ p, V (GlobalLocalizedProcess.process V hfinite jump rate initial e p T) ∂law μ J) ≤ B := by
  have hb := lintegral_le V hfinite jump rate initial e μ hinit hV T hT B hexhaust hi hmean
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable V hfinite jump rate initial e μ hinit hV T hT B hexhaust hi hmean)
      (Eventually.of_forall (fun _ => hV _))] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hb

end CarryingCapacity.GlobalLyapunovMoment
