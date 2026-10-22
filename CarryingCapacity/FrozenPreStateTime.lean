import CarryingCapacity.FrozenJumpIdentity
import CarryingCapacity.InitialFrozenPredictable
import CarryingCapacity.MarkedIntensity
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

/-!
# Pre-jump states agree with current states at almost every time

Only actual labelled proposal times can distinguish the chronological path
from its strict-past version. This set is countable for each noise sample and
has zero positive Lebesgue measure. Combining this fact with the already
proved predictable-version identification removes pre-jump notation from
time integrals, also on the independent-initial-record probability space.
-/

noncomputable section
open MeasureTheory Set Filter

namespace CarryingCapacity.FrozenPreStateTime
open MarkedNoise MarkedIntensity ChronologicalEvents CommonFrozenProcess
  FrozenJumpIdentity FrozenPredictableIntegrand

variable {J : Type*} [Fintype J]

local instance : NoAtoms positiveVolume := by
  unfold positiveVolume
  infer_instance

/-- Every time at which an actual labelled proposal occurs. -/
def proposalTimes (ω : Sample J) : Set ℝ :=
  range (fun e : Event J => (point e.1 ω e.2).1)

theorem proposalTimes_countable (ω : Sample J) : (proposalTimes ω).Countable :=
  countable_range _

theorem ae_time_not_proposalTimes (ω : Sample J) :
    ∀ᵐ t ∂positiveVolume, t ∉ proposalTimes ω :=
  (proposalTimes_countable ω).ae_not_mem positiveVolume

theorem ae_time_pos : ∀ᵐ t ∂positiveVolume, 0 < t := by
  have hn : ∀ᵐ t ∂positiveVolume, t ∈ Ici (0 : ℝ) := ae_restrict_mem measurableSet_Ici
  have hz := (countable_singleton (0 : ℝ)).ae_not_mem positiveVolume
  filter_upwards [hn, hz] with t ht hne
  exact lt_of_le_of_ne ht (Ne.symm hne)

variable {E : Type*} [DecidableEq E]
  (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)

/-- Off proposal times, replacing the actual chronological list by its
strict-past filter does not remove any event. -/
theorem ae_process_eq_leftProcess_off_proposalTimes : ∀ᵐ ω ∂law J,
    ∀ C x t, t ∉ proposalTimes ω →
      process active jump rate C x ω t = leftProcess active jump rate C x ω t := by
  filter_upwards [ae_boxedList_mem (J := J)] with ω hmem
  intro C x t ht
  have he : (boxedList (ω,t,C)).filter
      (fun e => decide ((point e.1 ω e.2).1 < t)) = boxedList (ω,t,C) := by
    apply List.filter_eq_self.mpr
    intro e he
    simp only [decide_eq_true_eq]
    apply lt_of_le_of_ne ((hmem t C e).mp he).1
    intro heq
    exact ht ⟨e, heq⟩
  simp only [process, runBox, leftProcess, he]

variable [TopologicalSpace E] [PolishSpace E]

/-- On one noise event, current and predictable pre-jump states agree outside
the countable proposal-time set at every positive time. -/
theorem ae_process_eq_preState_off_proposalTimes : ∀ᵐ ω ∂law J,
    ∀ C x t, 0 < t → t ∉ proposalTimes ω →
      process active jump rate C x ω t = preState active jump rate C x ω t := by
  filter_upwards [ae_process_eq_leftProcess_off_proposalTimes active jump rate,
    ae_process_eq_leftProcess_on_left active jump rate] with ω he hl
  intro C x t ht hnot
  obtain ⟨b, hb, hy⟩ := hl C x t
  rw [preState_eq_of_left_constant active jump rate C x ω t ht b hb _ hy]
  exact he C x t hnot

/-- The exceptional time set is independent of the cutoff and initial state. -/
theorem ae_time_process_eq_preState : ∀ᵐ ω ∂law J,
    ∀ᵐ t ∂positiveVolume, ∀ C x,
      process active jump rate C x ω t = preState active jump rate C x ω t := by
  filter_upwards [ae_process_eq_preState_off_proposalTimes active jump rate] with ω hω
  filter_upwards [ae_time_not_proposalTimes ω, ae_time_pos] with t hn ht
  exact fun C x => hω C x t ht hn

theorem ae_process_eq_preState_time : ∀ᵐ ω ∂law J,
    ∀ C x, (process active jump rate C x ω) =ᵐ[positiveVolume]
      (preState active jump rate C x ω) := by
  filter_upwards [ae_time_process_eq_preState active jump rate] with ω hω
  intro C x
  filter_upwards [hω] with t ht
  exact ht C x

/-- Arbitrary real test functions and arbitrary time restrictions have equal
time integrals. This is integral congruence and needs no integrability premise. -/
theorem ae_setIntegral_comp_eq_preState : ∀ᵐ ω ∂law J,
    ∀ C x (V : E → ℝ) (B : Set ℝ),
      (∫ t in B, V (process active jump rate C x ω t) ∂positiveVolume) =
        ∫ t in B, V (preState active jump rate C x ω t) ∂positiveVolume := by
  filter_upwards [ae_process_eq_preState_time active jump rate] with ω hω
  intro C x V B
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (hω C x)] with t ht
  exact congrArg V ht

theorem integral_setIntegral_comp_eq_preState (C : ℝ) (x : E)
    (V : E → ℝ) (B : Set ℝ) :
    (∫ ω, ∫ t in B, V (process active jump rate C x ω t) ∂positiveVolume ∂law J) =
      ∫ ω, ∫ t in B, V (preState active jump rate C x ω t) ∂positiveVolume ∂law J := by
  apply integral_congr_ae
  filter_upwards [ae_setIntegral_comp_eq_preState active jump rate] with ω hω
  exact hω C x V B

section Initial
variable {A : Type*} [MeasurableSpace A]
  (initial : A → E) (μ : Measure A)

/-- The same time-null exceptional set works at the actually sampled initial
state and for every fallback used by the product-space predictable version. -/
theorem ae_initial_process_eq_preState_time : ∀ᵐ p ∂CommonInitialNoise.law μ J,
    ∀ C e, (CommonInitialNoise.process active jump rate initial C p) =ᵐ[positiveVolume]
      (InitialFrozenPredictable.preState active jump rate initial C e p) := by
  filter_upwards [CommonInitialNoise.ae_noise μ
      (ae_process_eq_preState_time active jump rate),
    InitialFrozenPredictable.ae_preState_eq_base active jump rate initial μ] with p hp he
  intro C e
  filter_upwards [hp C (initial p.1), ae_time_pos] with t ht hpos
  exact ht.trans (he C e t hpos).symm

theorem ae_initial_setIntegral_comp_eq_preState : ∀ᵐ p ∂CommonInitialNoise.law μ J,
    ∀ C e (V : E → ℝ) (B : Set ℝ),
      (∫ t in B, V (CommonInitialNoise.process active jump rate initial C p t)
        ∂positiveVolume) =
      ∫ t in B, V (InitialFrozenPredictable.preState active jump rate initial C e p t)
        ∂positiveVolume := by
  filter_upwards [ae_initial_process_eq_preState_time active jump rate initial μ] with p hp
  intro C e V B
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (hp C e)] with t ht
  exact congrArg V ht

end Initial
end CarryingCapacity.FrozenPreStateTime
