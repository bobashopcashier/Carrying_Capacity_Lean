import CarryingCapacity.TimeDependentGlobalMoment
import CarryingCapacity.TimeDependentLyapunovComparison

/-!
# Lyapunov envelope comparison for the actual nonexplosive patch

A coarse affine generator bound supplies genuine exit exhaustion. Independently,
a sharper time-dependent generator bound yields the chosen envelope at every
finite spatial localization. Fatou transfers this envelope to the actual global
process and proves integrability. Neither exhaustion nor a global expected-value
inequality is assumed. This is moment control, not continuity of the law curve.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace CarryingCapacity.TimeDependentGlobalComparison
open CommonInitialNoise LyapunovLocalization TimeDependentLocalization

variable {A E J : Type*} [MeasurableSpace A] [DecidableEq E] [Fintype J]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (hbounded : ∀ n : ℕ, ∃ C : ℝ, ∀ x ∈ active V hfinite n, ∀ j t, rate j t x ≤ C)
  (initial : A → E) (e : E)
  (μ : Measure A) [IsProbabilityMeasure μ]
  (hRate : ∀ j x, Measurable (fun t => rate j t x)) (hinit : Measurable initial)
  (b : ℝ) (hb : 0 ≤ b) (hVnonneg : ∀ x, 0 ≤ V x)
  (hq : ∀ x j t, 0 ≤ t → 0 ≤ rate j t x)
  (hV : Integrable (fun a => V (initial a)) μ)
  (hcoarse : ∀ x t, 0 ≤ t →
    (∑ j, rate j t x * (V (jump j x) - V x)) ≤ b * (1 + V x))
include hRate hinit hb hVnonneg hq hV hcoarse

/-- A deterministic supersolution controls both genuine global integrals.
The coarse coefficient `b` is used only for nonexplosion; the finer comparison
may use another nonnegative coefficient `c` and integrable forcing `g`. -/
theorem bounds_of_envelope (c : ℝ) (hc : 0 ≤ c) (g K : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hg : IntegrableOn g (Ioc 0 T)) (hg0 : ∀ t ∈ Icc 0 T, 0 ≤ g t)
    (hK : ContinuousOn K (Icc 0 T)) (hK0 : ∀ t ∈ Icc 0 T, 0 ≤ K t)
    (hdrift : ∀ t ∈ Icc 0 T, ∀ x,
      (∑ j, rate j t x * (V (jump j x) - V x)) ≤ c * V x + g t)
    (hsuper : ∀ t ∈ Icc 0 T, (∫ a, V (initial a) ∂μ) +
      ∫ s in Ioc 0 t, (c * K s + g s) ≤ K t) :
    ∀ t ∈ Icc 0 T,
      Integrable (fun p => V (TimeDependentGlobalProcess.process
        V hfinite jump rate hbounded initial e p t)) (law μ J) ∧
      (∫ p, V (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p t)
        ∂law μ J) ≤ K t ∧
      (∫⁻ p, ENNReal.ofReal (V (TimeDependentGlobalProcess.process
        V hfinite jump rate hbounded initial e p t)) ∂law μ J) ≤ ENNReal.ofReal (K t) := by
  have hex := TimeDependentNonexplosion.ae_exhaustive V hfinite jump rate hbounded initial e μ
    hRate hinit b hb hVnonneg hq hV hcoarse
  have hlocal (n : ℕ) : ∀ t ∈ Icc 0 T,
      (∫ p, V (path V hfinite jump rate hbounded initial n p t) ∂law μ J) ≤ K t := by
    exact TimeDependentLyapunovComparison.expectation_le_envelope
      (active V hfinite n) jump rate initial μ hRate hinit (rateBound V hfinite rate hbounded n)
      e V c hc g K T hT hVnonneg (fun x _ j t ht => hq x j t ht)
      (fun x hx j t _ => rate_le_bound V hfinite rate hbounded n x hx j t)
      hV hg hg0 hK (fun t ht x hx => by
        simpa only [TimeDependentGeneratorIntegral.frozenGenerator, FrozenProcess.frozenGenerator,
          if_pos hx] using hdrift t ht x) hsuper
  intro t ht
  have hi := fun n => TimeDependentNonexplosion.integrable_localized_value
    V hfinite jump rate hbounded initial e μ hRate hinit hV n t
  refine ⟨TimeDependentGlobalMoment.integrable_of_bounds V hfinite jump rate hbounded initial e μ
    hRate hinit hVnonneg t ht.1 (K t) hex hi (fun n => hlocal n t ht), ?_, ?_⟩
  · exact TimeDependentGlobalMoment.expectation_le_of_bounds V hfinite jump rate hbounded initial e μ
      hRate hinit hVnonneg t ht.1 (K t) (hK0 t ht) hex hi (fun n => hlocal n t ht)
  · exact TimeDependentGlobalMoment.lintegral_le_of_bounds V hfinite jump rate hbounded initial e μ
      hRate hinit hVnonneg t ht.1 (K t) hex hi (fun n => hlocal n t ht)

/-- The manuscript's sharper generator bound preserves its deterministic
Lyapunov envelope for the actual nonexplosive process, not only its cutoffs. -/
theorem bounds_of_manuscript_envelope (c : ℝ) (hc : 0 ≤ c) (K : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hK : ContinuousOn K (Icc 0 T)) (hK0 : ∀ t ∈ Icc 0 T, 0 ≤ K t)
    (hdrift : ∀ t ∈ Icc 0 T, ∀ x,
      (∑ j, rate j t x * (V (jump j x) - V x)) ≤ c * (1 + V x + K t))
    (hsuper : ∀ t ∈ Icc 0 T, (∫ a, V (initial a) ∂μ) +
      ∫ s in Ioc 0 t, c * (1 + 2 * K s) ≤ K t) :
    ∀ t ∈ Icc 0 T,
      Integrable (fun p => V (TimeDependentGlobalProcess.process
        V hfinite jump rate hbounded initial e p t)) (law μ J) ∧
      (∫ p, V (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p t)
        ∂law μ J) ≤ K t ∧
      (∫⁻ p, ENNReal.ofReal (V (TimeDependentGlobalProcess.process
        V hfinite jump rate hbounded initial e p t)) ∂law μ J) ≤ ENNReal.ofReal (K t) := by
  apply bounds_of_envelope V hfinite jump rate hbounded initial e μ hRate hinit b hb hVnonneg
    hq hV hcoarse c hc (fun s => c * (1 + K s)) K T hT
  · exact (continuousOn_const.mul (continuousOn_const.add hK)).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  · intro t ht
    exact mul_nonneg hc (by linarith [hK0 t ht])
  · exact hK
  · exact hK0
  · intro s hs x
    convert hdrift s hs x using 1
    ring
  · intro t ht
    convert hsuper t ht using 1
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s _
    ring

end CarryingCapacity.TimeDependentGlobalComparison
