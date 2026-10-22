import CarryingCapacity.TimeDependentFrozenForward
import CarryingCapacity.TimeDependentGlobalProcess
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual frozen-law convergence and atomic probability comparison

Exhaustion of the genuine exits makes the constructed finite-level paths
agree eventually with the global path on every bounded horizon. Bounded
convergence for singleton indicators then proves convergence of their actual
masses to the global pushforward law. No law equation or convergence premise
is supplied. On a countable space, domination of all real singleton masses
between two probability measures already forces equality.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal Topology

namespace CarryingCapacity.TimeDependentFrozenLawLimit
open CommonInitialNoise LyapunovLocalization TimeDependentLocalization TimeDependentFrozenForward

section Probability
variable {E : Type*} [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]

/-- Probability normalization upgrades domination of every real atom to equality. -/
theorem probability_eq_of_real_atom_le (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ x, μ.real {x} ≤ ν.real {x}) : μ = ν := by
  have hsingle (x : E) : μ {x} ≤ ν {x} :=
    (ENNReal.toReal_le_toReal (measure_ne_top μ {x}) (measure_ne_top ν {x})).mp (h x)
  have hle : μ ≤ ν := Measure.le_iff.mpr (fun s hs => by
    rw [← μ.tsum_indicator_apply_singleton s hs, ← ν.tsum_indicator_apply_singleton s hs]
    apply ENNReal.tsum_le_tsum
    intro x
    by_cases hx : x ∈ s
    · simpa only [indicator_of_mem hx] using hsingle x
    · simp [indicator_of_not_mem hx])
  apply ext_iff_measureReal_singleton.mpr
  intro x
  apply le_antisymm (h x)
  have hcomp : μ.real ({x}ᶜ) ≤ ν.real ({x}ᶜ) :=
    ENNReal.toReal_mono (measure_ne_top ν _) (Measure.le_iff'.mp hle _)
  have hμ := measureReal_add_measureReal_compl (μ := μ) (measurableSet_singleton x)
  have hν := measureReal_add_measureReal_compl (μ := ν) (measurableSet_singleton x)
  simp only [measureReal_univ_eq_one] at hμ hν
  linarith

end Probability

variable {E J : Type*} [DecidableEq E] [Fintype J]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (hbounded : ∀ n : ℕ, ∃ C : ℝ,
    ∀ x ∈ active V hfinite n, ∀ j t, rate j t x ≤ C)
  (e : E) (μ : Measure E) [IsProbabilityMeasure μ]

/-- The genuine global time marginal under the sampled initial law. -/
def globalLaw (t : ℝ) : Measure E :=
  (law μ J).map (fun p => TimeDependentGlobalProcess.process
    V hfinite jump rate hbounded id e p t)

variable (hRate : ∀ j x, Measurable (fun t => rate j t x))
include hRate

/-- Probability of the actual pushforward follows from proved process measurability. -/
theorem globalLaw_probability (t : ℝ) :
    IsProbabilityMeasure (globalLaw V hfinite jump rate hbounded e μ t) :=
  isProbabilityMeasure_map
    ((TimeDependentGlobalProcess.measurable_process V hfinite jump rate hbounded id e
      hRate measurable_id).comp (measurable_id.prodMk measurable_const)).aemeasurable

omit [IsProbabilityMeasure μ] in
/-- All real test integrals have their actual pushforward expectation identity. -/
theorem integral_globalLaw (t : ℝ) (f : E → ℝ) :
    (∫ x, f x ∂globalLaw V hfinite jump rate hbounded e μ t) =
      ∫ p, f (TimeDependentGlobalProcess.process V hfinite jump rate hbounded id e p t)
        ∂law μ J :=
  integral_map_of_stronglyMeasurable
    ((TimeDependentGlobalProcess.measurable_process V hfinite jump rate hbounded id e
      hRate measurable_id).comp (measurable_id.prodMk measurable_const))
    (measurable_of_countable f).stronglyMeasurable

/-- The actual frozen singleton probabilities converge under genuine exit exhaustion. -/
theorem tendsto_mass
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rate hbounded id n p)
    (t : ℝ) (ht : 0 ≤ t) (x : E) :
    Tendsto (fun n => mass (active V hfinite n) jump rate id μ
      (rateBound V hfinite rate hbounded n) t x) atTop
      (𝓝 ((globalLaw V hfinite jump rate hbounded e μ t).real {x})) := by
  have hp (n : ℕ) : Measurable
      (fun p => path V hfinite jump rate hbounded id n p t) :=
    (measurable_path V hfinite jump rate hbounded id hRate measurable_id n).comp
      (measurable_id.prodMk measurable_const)
  have hconv : Tendsto
      (fun n => ∫ p, atomTest x (path V hfinite jump rate hbounded id n p t) ∂law μ J)
      atTop (𝓝 (∫ p, atomTest x
        (TimeDependentGlobalProcess.process V hfinite jump rate hbounded id e p t) ∂law μ J)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => 1)
    · intro n
      exact ((measurable_of_countable (atomTest x)).comp (hp n)).aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      exact Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (atomTest_nonneg x _)]
        exact atomTest_le_one x _)
    · filter_upwards [TimeDependentGlobalProcess.ae_agrees_on_horizon
        V hfinite jump rate hbounded id e μ hexhaust] with p hp'
      obtain ⟨n, hn⟩ := hp' ⟨t, ht⟩
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop n] with m hm
      exact congrArg (atomTest x) (hn m hm t ht le_rfl)
  have hid : (∫ p, atomTest x
      (TimeDependentGlobalProcess.process V hfinite jump rate hbounded id e p t) ∂law μ J) =
      (globalLaw V hfinite jump rate hbounded e μ t).real {x} := by
    rw [← integral_globalLaw V hfinite jump rate hbounded e μ hRate t (atomTest x)]
    simpa only [id_eq, preimage_id] using
      integral_atomTest_eq_measureReal (globalLaw V hfinite jump rate hbounded e μ t)
        id measurable_id x
  rw [hid] at hconv
  exact hconv

/-- Bounds that hold only once the target lies in the active sublevels are enough. -/
theorem global_atom_le_of_eventually_frozen_mass_le
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rate hbounded id n p)
    (t : ℝ) (ht : 0 ≤ t) (x : E) (b : ℝ)
    (hb : ∀ᶠ n in atTop, mass (active V hfinite n) jump rate id μ
      (rateBound V hfinite rate hbounded n) t x ≤ b) :
    (globalLaw V hfinite jump rate hbounded e μ t).real {x} ≤ b :=
  le_of_tendsto (tendsto_mass V hfinite jump rate hbounded e μ hRate hexhaust t ht x) hb

/-- A bound holding at every genuine frozen level passes to the actual global atom. -/
theorem global_atom_le_of_frozen_mass_le
    (hexhaust : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
      (T : ℝ≥0∞) < exit V hfinite jump rate hbounded id n p)
    (t : ℝ) (ht : 0 ≤ t) (x : E) (b : ℝ)
    (hb : ∀ n, mass (active V hfinite n) jump rate id μ
      (rateBound V hfinite rate hbounded n) t x ≤ b) :
    (globalLaw V hfinite jump rate hbounded e μ t).real {x} ≤ b :=
  le_of_tendsto (tendsto_mass V hfinite jump rate hbounded e μ hRate hexhaust t ht x)
    (Eventually.of_forall hb)

end CarryingCapacity.TimeDependentFrozenLawLimit
