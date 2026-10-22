import CarryingCapacity.CommonFrozenRegularity

/-!
# Actual first exits and stopped compatibility

The exit time is the infimum of the nonnegative times outside the active set,
with value infinity if there are none. Its finite attainment is proved from
local constancy of the constructed paths. This is a pathwise result; no
filtration, adaptedness, or stopping-time assertion is made here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical ENNReal

namespace CarryingCapacity.CommonFrozenExit
open CommonFrozenProcess CommonFrozenRegularity

section DeterministicExit
variable {E : Type*}

/-- The nonnegative times at which a path is outside a prescribed set. -/
def exitSet (A : Set E) (f : ℝ → E) : Set ℝ := {t | 0 ≤ t ∧ f t ∉ A}

/-- The genuine first exit, including infinity for a path that never exits. -/
def exitTime (A : Set E) (f : ℝ → E) : ℝ≥0∞ :=
  if (exitSet A f).Nonempty then ENNReal.ofReal (sInf (exitSet A f)) else ⊤

/-- Stop a real-time path at an extended nonnegative time. -/
def stopped (σ : ℝ≥0∞) (f : ℝ → E) (t : ℝ) : E :=
  if σ = ⊤ then f t else f (min t σ.toReal)

theorem exitSet_bddBelow (A : Set E) (f : ℝ → E) : BddBelow (exitSet A f) :=
  ⟨0, fun _ h => h.1⟩

theorem exitSet_inf_nonneg (A : Set E) (f : ℝ → E)
    (h : (exitSet A f).Nonempty) : 0 ≤ sInf (exitSet A f) :=
  le_csInf h (fun _ ht => ht.1)

theorem exitTime_eq_top_iff (A : Set E) (f : ℝ → E) :
    exitTime A f = ⊤ ↔ ¬ (exitSet A f).Nonempty := by
  simp only [exitTime]
  split_ifs with h <;> simp [h]

/-- Infinite exit time means that the path never leaves at a nonnegative time. -/
theorem exitTime_eq_top_iff_forall_mem (A : Set E) (f : ℝ → E) :
    exitTime A f = ⊤ ↔ ∀ t : ℝ, 0 ≤ t → f t ∈ A := by
  rw [exitTime_eq_top_iff]
  constructor
  · intro h t ht
    by_contra hout
    exact h ⟨t, ht, hout⟩
  · intro h ⟨t, ht, hout⟩
    exact hout (h t ht)

theorem exitTime_toReal (A : Set E) (f : ℝ → E)
    (h : (exitSet A f).Nonempty) : (exitTime A f).toReal = sInf (exitSet A f) := by
  simp only [exitTime, if_pos h, ENNReal.toReal_ofReal (exitSet_inf_nonneg A f h)]

theorem exitTime_le_of_not_mem (A : Set E) (f : ℝ → E)
    {t : ℝ} (ht : 0 ≤ t) (hout : f t ∉ A) : exitTime A f ≤ ENNReal.ofReal t := by
  have hmem : t ∈ exitSet A f := ⟨ht, hout⟩
  rw [exitTime, if_pos ⟨t, hmem⟩]
  exact ENNReal.ofReal_le_ofReal (csInf_le (exitSet_bddBelow A f) hmem)

/-- Before the infimum the path belongs to the set, without a regularity assumption. -/
theorem mem_before_exit (A : Set E) (f : ℝ → E)
    {t : ℝ} (ht : 0 ≤ t) (hbefore : ENNReal.ofReal t < exitTime A f) : f t ∈ A := by
  by_contra hout
  exact (not_le_of_gt hbefore) (exitTime_le_of_not_mem A f ht hout)

theorem mem_before_exit_toReal (A : Set E) (f : ℝ → E)
    (hfin : exitTime A f ≠ ⊤) {t : ℝ} (ht : 0 ≤ t)
    (hbefore : t < (exitTime A f).toReal) : f t ∈ A := by
  apply mem_before_exit A f ht
  rw [← ENNReal.ofReal_toReal hfin]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).mpr hbefore

/-- A finite first exit is attained if the actual path is locally constant to
the right. This hypothesis will be discharged from the finite event lists. -/
theorem exitTime_attained (A : Set E) (f : ℝ → E)
    (hright : ∀ t : ℝ, ∃ b, t < b ∧ ∀ u ∈ Ico t b, f u = f t)
    (hfin : exitTime A f ≠ ⊤) : f (exitTime A f).toReal ∉ A := by
  have hne : (exitSet A f).Nonempty := by
    by_contra h
    exact hfin ((exitTime_eq_top_iff A f).mpr h)
  rw [exitTime_toReal A f hne]
  intro hin
  obtain ⟨b, hb, hconst⟩ := hright (sInf (exitSet A f))
  obtain ⟨u, hu, hub⟩ := exists_lt_of_csInf_lt hne hb
  have hlu := csInf_le (exitSet_bddBelow A f) hu
  exact hu.2 ((hconst u ⟨hlu, hub⟩).symm ▸ hin)

/-- Right-local constancy rules out an unattained exit at time zero. -/
theorem exitTime_eq_zero_iff (A : Set E) (f : ℝ → E)
    (hright : ∀ t : ℝ, ∃ b, t < b ∧ ∀ u ∈ Ico t b, f u = f t) :
    exitTime A f = 0 ↔ f 0 ∉ A := by
  constructor
  · intro hz
    have hfin : exitTime A f ≠ ⊤ := by rw [hz]; simp
    simpa only [hz, ENNReal.toReal_zero] using exitTime_attained A f hright hfin
  · intro hout
    apply le_antisymm _ bot_le
    simpa only [ENNReal.ofReal_zero] using exitTime_le_of_not_mem A f le_rfl hout

/-- If a path freezes after leaving the set, stopping at the genuine first
exit leaves the path unchanged. -/
theorem stopped_exitTime_eq (A : Set E) (f : ℝ → E)
    (hright : ∀ t : ℝ, ∃ b, t < b ∧ ∀ u ∈ Ico t b, f u = f t)
    (hfrozen : ∀ s t : ℝ, s ≤ t → f s ∉ A → f t = f s)
    (t : ℝ) : stopped (exitTime A f) f t = f t := by
  by_cases hfin : exitTime A f = ⊤
  · simp only [stopped, hfin, ↓reduceIte]
  · simp only [stopped, hfin, ↓reduceIte]
    by_cases ht : t ≤ (exitTime A f).toReal
    · rw [min_eq_left ht]
    · rw [min_eq_right (le_of_not_ge ht)]
      exact (hfrozen _ t (le_of_not_ge ht) (exitTime_attained A f hright hfin)).symm

end DeterministicExit

variable {E J : Type*} [DecidableEq E] [Fintype J]
  (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)

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
    (C₁ C₂ : ℝ) (h₁ : ∀ x ∈ active, ∀ j, rate j x ≤ C₁)
    (h₂ : ∀ x ∈ large, ∀ j, rate j x ≤ C₂) :
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
    (C₁ C₂ : ℝ) (h₁ : ∀ x ∈ active, ∀ j, rate j x ≤ C₁)
    (h₂ : ∀ x ∈ large, ∀ j, rate j x ≤ C₂) :
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

end CarryingCapacity.CommonFrozenExit
