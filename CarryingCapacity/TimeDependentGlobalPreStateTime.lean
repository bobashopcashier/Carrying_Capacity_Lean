import CarryingCapacity.TimeDependentGlobalCounting
import CarryingCapacity.TimeDependentDynkin

/-!
# The global pre-jump state agrees with the current state at almost every time

Only countably many actual frozen levels are combined. Their time-null
pre-state identities, genuine exit exhaustion, and before-exit agreement give
the corresponding identity for the constructed global path. In particular,
time integrals may use current states without assuming continuity at jumps or
any stochastic integrability bound.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace CarryingCapacity.TimeDependentGlobalPreStateTime
open CommonInitialNoise TimeDependentLocalization MarkedIntensity
open TimeDependentGlobalCounting
open LyapunovLocalization (active)

variable {A E J : Type*} [MeasurableSpace A] [DecidableEq E] [Fintype J]
  [TopologicalSpace E] [PolishSpace E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (hbounded : ∀ n : ℕ, ∃ C : ℝ,
    ∀ x ∈ active V hfinite n, ∀ j t, rate j t x ≤ C)
  (initial : A → E) (e : E) (μ : Measure A)
  (hexhaust : ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n,
    (T : ℝ≥0∞) < exit V hfinite jump rate hbounded initial n p)

include hexhaust

/-- Actual global predictable pre-states and current states agree for almost
every sample and almost every positive-Lebesgue time. -/
theorem ae_preState_eq_process_time :
    ∀ᵐ p ∂law μ J,
      preState V hfinite jump rate hbounded initial e p =ᵐ[positiveVolume]
        TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p := by
  have hl := ae_all_iff.mpr (fun n : ℕ =>
    TimeDependentDynkin.ae_initial_process_eq_preState_time
      (active V hfinite n) jump rate initial μ)
  filter_upwards [hl,
    ae_preState_eq_level V hfinite jump rate hbounded initial e μ,
    TimeDependentGlobalProcess.ae_eq_path V hfinite jump rate hbounded initial e μ,
    hexhaust] with p hl he hg hx
  have htall := ae_all_iff.mpr (fun n : ℕ => hl n (rateBound V hfinite rate hbounded n) e)
  filter_upwards [htall, FrozenPreStateTime.ae_time_pos] with t ht htpos
  obtain ⟨n, hn⟩ := hx ⟨t, htpos.le⟩
  calc
    preState V hfinite jump rate hbounded initial e p t =
        TimeDependentInitial.preState (active V hfinite n) jump rate initial
          (rateBound V hfinite rate hbounded n) e p t :=
      (he n ⟨t, htpos.le⟩ hn t ⟨htpos, le_rfl⟩).1
    _ = path V hfinite jump rate hbounded initial n p t := (ht n).symm
    _ = TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p t :=
      (hg n t htpos.le (by simpa only [← ENNReal.ofReal_coe_nnreal] using hn.le)).symm

/-- All real time tests and all restrictions share the same sample event.
This is integral congruence, with no integrability assumption. -/
theorem ae_setIntegral_preState_eq_process : ∀ᵐ p ∂law μ J,
    ∀ (G : ℝ → E → ℝ) (B : Set ℝ),
      (∫ t in B, G t (preState V hfinite jump rate hbounded initial e p t)
        ∂positiveVolume) =
      ∫ t in B, G t (TimeDependentGlobalProcess.process
        V hfinite jump rate hbounded initial e p t) ∂positiveVolume := by
  filter_upwards [ae_preState_eq_process_time V hfinite jump rate hbounded initial e μ hexhaust]
    with p hp
  intro G B
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hp] with t ht
  exact congrArg (G t) ht

/-- Nonnegative extended time integrals also agree, allowing infinite values. -/
theorem ae_setLIntegral_preState_eq_process : ∀ᵐ p ∂law μ J,
    ∀ (G : ℝ → E → ℝ≥0∞) (B : Set ℝ),
      (∫⁻ t in B, G t (preState V hfinite jump rate hbounded initial e p t)
        ∂positiveVolume) =
      ∫⁻ t in B, G t (TimeDependentGlobalProcess.process
        V hfinite jump rate hbounded initial e p t) ∂positiveVolume := by
  filter_upwards [ae_preState_eq_process_time V hfinite jump rate hbounded initial e μ hexhaust]
    with p hp
  intro G B
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae hp] with t ht
  exact congrArg (G t) ht

end CarryingCapacity.TimeDependentGlobalPreStateTime
