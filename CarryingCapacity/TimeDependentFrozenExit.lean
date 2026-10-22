import CarryingCapacity.TimeDependentRateLocalization
import CarryingCapacity.CommonFrozenExit

/-!
# Actual first exits for time-dependent frozen paths

The genuine first-exit infimum is attained whenever finite. Nested active sets
have ordered exits, and the larger path stopped at the smaller exit equals the
smaller path, including its exit jump. These conclusions follow from the actual
chronological construction. No stopping-time or probabilistic tail estimate is
asserted here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical ENNReal

namespace CarryingCapacity.TimeDependentFrozenExit
open CommonFrozenExit TimeDependentFrozenProcess

variable {E J : Type*} [DecidableEq E] [Fintype J]
  (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)

/-- The first exit of the defined common-noise frozen path. -/
def firstExit (C : ℝ) (x : E) (ω : MarkedNoise.Sample J) : ℝ≥0∞ :=
  exitTime (active : Set E) (process active jump rate C x ω)

omit [Fintype J] in
/-- Membership before the actual first exit is automatic from its definition. -/
theorem process_mem_before_firstExit (C : ℝ) (x : E) (ω : MarkedNoise.Sample J)
    {t : ℝ} (ht : 0 ≤ t)
    (hbefore : ENNReal.ofReal t < firstExit active jump rate C x ω) :
    process active jump rate C x ω t ∈ active :=
  mem_before_exit _ _ ht hbefore

/-- Finite exits of the actual frozen paths are attained, simultaneously in
initial state and vertical cutoff. -/
theorem ae_firstExit_attained : ∀ᵐ ω ∂MarkedNoise.law J, ∀ C x,
    firstExit active jump rate C x ω ≠ ⊤ →
      process active jump rate C x ω (firstExit active jump rate C x ω).toReal ∉ active := by
  filter_upwards [ae_process_right_constant active jump rate] with ω hright
  intro C x hfin
  exact exitTime_attained _ _ (hright C x) hfin

/-- The first exit is zero exactly for initial states outside the active set.
In particular, an active initial state has strictly positive first exit. -/
theorem ae_firstExit_eq_zero_iff : ∀ᵐ ω ∂MarkedNoise.law J, ∀ C x,
    firstExit active jump rate C x ω = 0 ↔ x ∉ active := by
  filter_upwards [ae_process_right_constant active jump rate,
    ae_process_zero active jump rate] with ω hright hzero
  intro C x
  exact (exitTime_eq_zero_iff _ _ (hright C x)).trans (by rw [hzero C x]; rfl)

/-- Stopping an actual frozen path at its first exit leaves it unchanged. -/
theorem ae_stopped_firstExit_self : ∀ᵐ ω ∂MarkedNoise.law J, ∀ C x t,
    stopped (firstExit active jump rate C x ω) (process active jump rate C x ω) t =
      process active jump rate C x ω t := by
  filter_upwards [ae_process_right_constant active jump rate,
    ae_process_frozen active jump rate] with ω hright hfrozen
  intro C x t
  exact stopped_exitTime_eq _ _ (hright C x) (hfrozen C x) t

/-- The true exit times increase with the active sets for paths driven by the
same noise. Distinct dominating height bounds are permitted. -/
theorem ae_firstExit_mono (large : Finset E) (hsets : active ⊆ large)
    (C₁ C₂ : ℝ) (h₁ : ∀ x ∈ active, ∀ j t, rate j t x ≤ C₁)
    (h₂ : ∀ x ∈ large, ∀ j t, rate j t x ≤ C₂) :
    ∀ᵐ ω ∂MarkedNoise.law J, ∀ x,
      firstExit active jump rate C₁ x ω ≤ firstExit large jump rate C₂ x ω := by
  filter_upwards [ae_firstExit_attained large jump rate,
    ae_process_agree_before_exit active jump rate large hsets C₁ C₂ h₁ h₂]
    with ω hatt hagree
  intro x
  by_cases hfin : firstExit large jump rate C₂ x ω = ⊤
  · rw [hfin]
    exact le_top
  · by_contra hle
    have hlt := lt_of_not_ge hle
    let t := (firstExit large jump rate C₂ x ω).toReal
    have ht : 0 ≤ t := ENNReal.toReal_nonneg
    have hsmall : ENNReal.ofReal t < firstExit active jump rate C₁ x ω := by
      simpa only [t, ENNReal.ofReal_toReal hfin] using hlt
    have hin := process_mem_before_firstExit active jump rate C₁ x ω ht hsmall
    have heq := hagree x t (by
      intro s hs hst
      apply process_mem_before_firstExit active jump rate C₁ x ω hs
      exact (ENNReal.ofReal_le_ofReal hst.le).trans_lt hsmall)
    exact hatt C₂ x hfin (heq.symm ▸ hsets hin)

/-- Stopping the larger actual path at the smaller actual exit gives the
smaller path, including its accepted exit jump and all subsequent times. -/
theorem ae_stopped_nested (large : Finset E) (hsets : active ⊆ large)
    (C₁ C₂ : ℝ) (h₁ : ∀ x ∈ active, ∀ j t, rate j t x ≤ C₁)
    (h₂ : ∀ x ∈ large, ∀ j t, rate j t x ≤ C₂) :
    ∀ᵐ ω ∂MarkedNoise.law J, ∀ x t, 0 ≤ t →
      stopped (firstExit active jump rate C₁ x ω)
        (process large jump rate C₂ x ω) t = process active jump rate C₁ x ω t := by
  filter_upwards [ae_firstExit_attained active jump rate,
    ae_process_frozen active jump rate,
    ae_process_agree_before_exit active jump rate large hsets C₁ C₂ h₁ h₂]
    with ω hatt hfrozen hagree
  intro x t ht
  by_cases hfin : firstExit active jump rate C₁ x ω = ⊤
  · simp only [stopped, hfin, ↓reduceIte]
    apply hagree x t
    intro s hs _
    apply process_mem_before_firstExit active jump rate C₁ x ω hs
    rw [hfin]
    exact ENNReal.ofReal_lt_top
  · have hbefore : ∀ s : ℝ, 0 ≤ s →
        s < (firstExit active jump rate C₁ x ω).toReal →
        process active jump rate C₁ x ω s ∈ active := by
      intro s hs hst
      exact mem_before_exit_toReal _ _ hfin hs hst
    simp only [stopped, hfin, ↓reduceIte]
    by_cases hts : t ≤ (firstExit active jump rate C₁ x ω).toReal
    · rw [min_eq_left hts]
      exact hagree x t (fun s hs hst => hbefore s hs (hst.trans_le hts))
    · rw [min_eq_right (le_of_not_ge hts), hagree x _ hbefore]
      exact (hfrozen C₁ x _ t (le_of_not_ge hts) (hatt C₁ x hfin)).symm

/-- The stopped compatibility identity on `[0,T]` needs rate bounds only on
that interval, even when the rates are unbounded at later times. -/
theorem ae_stopped_nested_on_horizon (large : Finset E) (hsets : active ⊆ large)
    (T C₁ C₂ : ℝ) (hT : 0 ≤ T)
    (h₁ : ∀ x ∈ active, ∀ j s, s ∈ Icc 0 T → rate j s x ≤ C₁)
    (h₂ : ∀ x ∈ large, ∀ j s, s ∈ Icc 0 T → rate j s x ≤ C₂) :
    ∀ᵐ ω ∂MarkedNoise.law J, ∀ x t, t ∈ Icc 0 T →
      stopped (firstExit active jump rate C₁ x ω)
        (process large jump rate C₂ x ω) t = process active jump rate C₁ x ω t := by
  filter_upwards [ae_firstExit_attained active jump rate,
    ae_process_frozen active jump rate,
    TimeDependentRateLocalization.ae_agree_before_exit_on_horizon active large jump rate
      hsets T C₁ C₂ hT h₁ h₂] with ω hatt hfrozen hagree
  intro x t ht
  by_cases hfin : firstExit active jump rate C₁ x ω = ⊤
  · simp only [stopped, hfin, ↓reduceIte]
    apply hagree x t ht.2
    intro s hs _
    apply process_mem_before_firstExit active jump rate C₁ x ω hs
    rw [hfin]
    exact ENNReal.ofReal_lt_top
  · have hbefore : ∀ s : ℝ, 0 ≤ s →
        s < (firstExit active jump rate C₁ x ω).toReal →
        process active jump rate C₁ x ω s ∈ active := by
      intro s hs hst
      exact mem_before_exit_toReal _ _ hfin hs hst
    simp only [stopped, hfin, ↓reduceIte]
    by_cases hts : t ≤ (firstExit active jump rate C₁ x ω).toReal
    · rw [min_eq_left hts]
      exact hagree x t ht.2 (fun s hs hst => hbefore s hs (hst.trans_le hts))
    · have hτT : (firstExit active jump rate C₁ x ω).toReal ≤ T :=
        (le_of_not_ge hts).trans ht.2
      rw [min_eq_right (le_of_not_ge hts), hagree x _ hτT hbefore]
      exact (hfrozen C₁ x _ t (le_of_not_ge hts) (hatt C₁ x hfin)).symm

end CarryingCapacity.TimeDependentFrozenExit
