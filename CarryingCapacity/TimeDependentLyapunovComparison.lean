import CarryingCapacity.TimeDependentExpectation
import CarryingCapacity.IntegralGronwallComparison

/-!
# Time-dependent Lyapunov envelope comparison

Pointwise generator control with an integrable deterministic forcing gives an
integral subsolution for the actual frozen expectation. The proved comparison
theorem then bounds this expectation by a deterministic supersolution. The
last theorem has the manuscript's forcing `b * (1 + V + K(t))`; its envelope
condition involves only `K` and the initial moment, not the unknown law.
-/

noncomputable section
open MeasureTheory Set Filter

namespace CarryingCapacity.TimeDependentLyapunovComparison
open CommonInitialNoise TimeDependentInitial TimeDependentGeneratorIntegral TimeDependentExpectation

variable {A J E : Type*} [MeasurableSpace A] [Fintype J] [DecidableEq E]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ) (initial : A → E)

/-- A pointwise linear generator bound gives the corresponding bound for
the actual expected generator, with integrability proved from the construction. -/
theorem expectedGenerator_le_linear (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (b c : ℝ)
    (hq : ∀ y ∈ active, ∀ j s, 0 ≤ s → 0 ≤ rate j s y)
    (hbound : ∀ y ∈ active, ∀ j s, 0 ≤ s → rate j s y ≤ C)
    (hV : Integrable (fun a => V (initial a)) μ) (t : ℝ) (ht : 0 ≤ t)
    (hdrift : ∀ x, frozenGenerator active jump rate V t x ≤ b * V x + c) :
    expectedGenerator active jump rate initial μ C V t ≤
      b * expectation active jump rate initial μ C V t + c := by
  have hiV := TimeDependentDynkin.integrable_testFunction active jump rate initial
    μ hRate hinit C e V t hV
  have hiG := integrable_generator_at active jump rate initial μ hRate hinit C V hq hbound t ht
  have h := integral_mono hiG ((hiV.const_mul b).add (integrable_const c))
    (fun p => hdrift (process active jump rate initial C p t))
  simpa only [expectedGenerator, expectation, Pi.add_apply,
    integral_add (hiV.const_mul b) (integrable_const c), integral_const_mul,
    integral_const, measureReal_univ_eq_one, one_smul] using h

/-- The actual expected test value is an integral subsolution. The forcing
is deterministic; no expected drift inequality is assumed. -/
theorem expectation_integral_le (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (b : ℝ)
    (g : ℝ → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j s, 0 ≤ s → 0 ≤ rate j s y)
    (hbound : ∀ y ∈ active, ∀ j s, 0 ≤ s → rate j s y ≤ C)
    (hV : Integrable (fun a => V (initial a)) μ)
    (hg : IntegrableOn g (Ioc 0 T))
    (hdrift : ∀ s ∈ Icc 0 T, ∀ x,
      frozenGenerator active jump rate V s x ≤ b * V x + g s)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    expectation active jump rate initial μ C V t ≤ (∫ a, V (initial a) ∂μ) +
      ∫ s in Ioc 0 t, (b * expectation active jump rate initial μ C V s + g s) := by
  have hc := continuousOn_expectation active jump rate initial μ hRate hinit C e V hq hbound hV
  have hiU : IntegrableOn (expectation active jump rate initial μ C V) (Ioc 0 t) :=
    (hc.mono Icc_subset_Ici_self).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hig := hg.mono_set (Ioc_subset_Ioc_right ht.2)
  have hle := integral_mono_ae
    (integrableOn_expectedGenerator active jump rate initial μ hRate hinit C V hq hbound 0 t le_rfl)
    ((hiU.const_mul b).add hig) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact expectedGenerator_le_linear active jump rate initial μ hRate hinit C e V b (g s)
        hq hbound hV s hs.1.le (hdrift s ⟨hs.1.le, hs.2.trans ht.2⟩))
  rw [expectation_eq_initial_add_integral active jump rate initial μ hRate hinit C e V t
    hq hbound hV]
  exact add_le_add_left hle _

/-- A deterministic integral supersolution bounds the actual frozen
Lyapunov mean on the entire horizon. All stochastic inequalities are derived
from a pointwise bound on the finite active set. -/
theorem expectation_le_envelope (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (g K : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hVnonneg : ∀ x, 0 ≤ V x)
    (hq : ∀ y ∈ active, ∀ j s, 0 ≤ s → 0 ≤ rate j s y)
    (hbound : ∀ y ∈ active, ∀ j s, 0 ≤ s → rate j s y ≤ C)
    (hV : Integrable (fun a => V (initial a)) μ)
    (hg : IntegrableOn g (Ioc 0 T)) (hg0 : ∀ t ∈ Icc 0 T, 0 ≤ g t)
    (hK : ContinuousOn K (Icc 0 T))
    (hdrift : ∀ s ∈ Icc 0 T, ∀ x ∈ active,
      frozenGenerator active jump rate V s x ≤ b * V x + g s)
    (hsuper : ∀ t ∈ Icc 0 T, (∫ a, V (initial a) ∂μ) +
      ∫ s in Ioc 0 t, (b * K s + g s) ≤ K t) :
    ∀ t ∈ Icc 0 T, expectation active jump rate initial μ C V t ≤ K t := by
  have hd : ∀ s ∈ Icc 0 T, ∀ x,
      frozenGenerator active jump rate V s x ≤ b * V x + g s := by
    intro s hs x
    by_cases hx : x ∈ active
    · exact hdrift s hs x hx
    · rw [frozenGenerator, FrozenProcess.frozenGenerator, if_neg hx]
      exact add_nonneg (mul_nonneg hb (hVnonneg x)) (hg0 s hs)
  exact IntegralGronwallComparison.le_of_integral_subsolution hT
    ((continuousOn_expectation active jump rate initial μ hRate hinit C e V hq hbound hV).mono
      Icc_subset_Ici_self) hK hb hg
    (fun t ht => expectation_integral_le active jump rate initial μ hRate hinit C e V b g T
      hq hbound hV hg hd t ht) hsuper

/-- The manuscript's time-varying forcing preserves any continuous
nonnegative envelope satisfying its deterministic scalar integral inequality. -/
theorem expectation_le_manuscript_envelope (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (K : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hVnonneg : ∀ x, 0 ≤ V x)
    (hq : ∀ y ∈ active, ∀ j s, 0 ≤ s → 0 ≤ rate j s y)
    (hbound : ∀ y ∈ active, ∀ j s, 0 ≤ s → rate j s y ≤ C)
    (hV : Integrable (fun a => V (initial a)) μ)
    (hK : ContinuousOn K (Icc 0 T)) (hK0 : ∀ t ∈ Icc 0 T, 0 ≤ K t)
    (hdrift : ∀ s ∈ Icc 0 T, ∀ x ∈ active,
      frozenGenerator active jump rate V s x ≤ b * (1 + V x + K s))
    (hsuper : ∀ t ∈ Icc 0 T, (∫ a, V (initial a) ∂μ) +
      ∫ s in Ioc 0 t, b * (1 + 2 * K s) ≤ K t) :
    ∀ t ∈ Icc 0 T, expectation active jump rate initial μ C V t ≤ K t := by
  apply expectation_le_envelope active jump rate initial μ hRate hinit C e V b hb
    (fun s => b * (1 + K s)) K T hT hVnonneg hq hbound hV
  · exact (continuousOn_const.mul (continuousOn_const.add hK)).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  · intro t ht
    exact mul_nonneg hb (by linarith [hK0 t ht])
  · exact hK
  · intro s hs x hx
    convert hdrift s hs x hx using 1
    ring
  · intro t ht
    convert hsuper t ht using 1
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s _
    ring

end CarryingCapacity.TimeDependentLyapunovComparison
