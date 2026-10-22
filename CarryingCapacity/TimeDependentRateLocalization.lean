import CarryingCapacity.TimeDependentFrozenProcess

/-!
# Finite-horizon localization of deterministic time-dependent rates

Clamping the time argument to `[0,T]` turns an active-state rate bound on a
finite horizon into a global bound. Actual proposal times on that horizon are
unchanged, so the clamped and original frozen paths agree there. Consequently
cutoff independence and nested-set compatibility require only horizon-local
rate bounds. Neither agreement nor local boundedness is assumed of a solution.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical

namespace CarryingCapacity.TimeDependentRateLocalization
open ChronologicalEvents Freezing TimeDependentFrozenProcess

variable {E J : Type*}

/-- Time is held at zero before the horizon and at `T` after it. -/
def clampTime (T t : ℝ) : ℝ := max 0 (min t T)

/-- A rate extended outside a finite horizon by keeping its endpoint values. -/
def clampRate (T : ℝ) (rate : J → ℝ → E → ℝ) (j : J) (t : ℝ) (x : E) : ℝ :=
  rate j (clampTime T t) x

theorem clampTime_mem (T : ℝ) (hT : 0 ≤ T) (t : ℝ) :
    clampTime T t ∈ Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

theorem clampTime_eq (T t : ℝ) (ht : t ∈ Icc 0 T) : clampTime T t = t := by
  simp only [clampTime, min_eq_left ht.2, max_eq_right ht.1]

theorem measurable_clampRate (T : ℝ) (rate : J → ℝ → E → ℝ)
    (hrate : ∀ j x, Measurable (fun t => rate j t x)) :
    ∀ j x, Measurable (fun t => clampRate T rate j t x) := by
  intro j x
  exact (hrate j x).comp (measurable_const.max (measurable_id.min measurable_const))

theorem clampRate_bound (active : Finset E) (rate : J → ℝ → E → ℝ)
    (T C : ℝ) (hT : 0 ≤ T)
    (hbound : ∀ x ∈ active, ∀ j t, t ∈ Icc 0 T → rate j t x ≤ C) :
    ∀ x ∈ active, ∀ j t, clampRate T rate j t x ≤ C := by
  intro x hx j t
  exact hbound x hx j _ (clampTime_mem T hT t)

theorem clampRate_nonneg (rate : J → ℝ → E → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hbound : ∀ j t x, t ∈ Icc 0 T → 0 ≤ rate j t x) :
    ∀ j t x, 0 ≤ clampRate T rate j t x := by
  intro j t x
  exact hbound j _ x (clampTime_mem T hT t)

variable [DecidableEq E]

/-- A frozen recursion reads the decoder only at active states and actual list
members; agreement elsewhere is unnecessary. -/
theorem run_congr_decode_on_active {M : Type*} (active : Finset E)
    (jump : J → E → E) (d₁ d₂ : E → M → Option J) (x : E) (l : List M)
    (h : ∀ e ∈ l, ∀ y ∈ active, d₁ y e = d₂ y e) :
    Freezing.run active jump d₁ x l = Freezing.run active jump d₂ x l := by
  induction l generalizing x with
  | nil => rfl
  | cons e l ih =>
    have hs : frozenStep active jump d₁ x e = frozenStep active jump d₂ x e := by
      by_cases hx : x ∈ active
      · simp only [frozenStep, hx, ↓reduceIte, h e (by simp) x hx]
      · simp only [frozenStep, hx, ↓reduceIte]
    simp only [Freezing.run, hs]
    exact ih _ (fun f hf y hy => h f (by simp [hf]) y hy)

variable [Fintype J]

/-- Actual finite-horizon paths depend only on rates on that horizon at active
states. The event is simultaneous in cutoff, initial state, and time. -/
theorem ae_process_congr_on_horizon (active : Finset E) (jump : J → E → E)
    (rate₁ rate₂ : J → ℝ → E → ℝ) (T : ℝ)
    (heq : ∀ x ∈ active, ∀ j t, t ∈ Icc 0 T → rate₁ j t x = rate₂ j t x) :
    ∀ᵐ ω ∂MarkedNoise.law J, ∀ C x t, t ≤ T →
      process active jump rate₁ C x ω t = process active jump rate₂ C x ω t := by
  filter_upwards [ae_boxedList_mem (J := J), MarkedNoise.ae_positive_points (J := J)]
    with ω hm hp
  intro C x t ht
  apply run_congr_decode_on_active
  intro e he y hy
  have htime : (MarkedNoise.point e.1 ω e.2).1 ∈ Icc 0 T :=
    ⟨(hp e.1 e.2).1.le, (((hm t C e).mp he).1).trans ht⟩
  simp only [eventDecode, heq y hy e.1 _ htime]

/-- Clamping changes no active decision up to the selected horizon. -/
theorem ae_clamp_process_agrees (active : Finset E) (jump : J → E → E)
    (rate : J → ℝ → E → ℝ) (T : ℝ) :
    ∀ᵐ ω ∂MarkedNoise.law J, ∀ C x t, t ≤ T →
      process active jump (clampRate T rate) C x ω t =
        process active jump rate C x ω t := by
  apply ae_process_congr_on_horizon
  intro x _ j t ht
  simp only [clampRate, clampTime_eq T t ht]

/-- A finite-horizon rate bound suffices for independence of the height cutoff. -/
theorem ae_bound_independent_on_horizon (active : Finset E) (jump : J → E → E)
    (rate : J → ℝ → E → ℝ) (T C₁ C₂ : ℝ) (hT : 0 ≤ T)
    (h₁ : ∀ x ∈ active, ∀ j t, t ∈ Icc 0 T → rate j t x ≤ C₁)
    (h₂ : ∀ x ∈ active, ∀ j t, t ∈ Icc 0 T → rate j t x ≤ C₂) :
    ∀ᵐ ω ∂MarkedNoise.law J, ∀ x t, t ≤ T →
      process active jump rate C₁ x ω t = process active jump rate C₂ x ω t := by
  filter_upwards [ae_clamp_process_agrees active jump rate T,
    ae_process_bound_independent active jump (clampRate T rate) C₁ C₂
      (clampRate_bound active rate T C₁ hT h₁)
      (clampRate_bound active rate T C₂ hT h₂)] with ω hc hb
  intro x t ht
  exact (hc C₁ x t ht).symm.trans ((hb x t).trans (hc C₂ x t ht))

/-- Nested frozen paths agree through the smaller exit on a finite horizon,
using only bounds for rates on that horizon. The exit jump is included. -/
theorem ae_agree_before_exit_on_horizon (active large : Finset E)
    (jump : J → E → E) (rate : J → ℝ → E → ℝ) (hsets : active ⊆ large)
    (T C₁ C₂ : ℝ) (hT : 0 ≤ T)
    (h₁ : ∀ x ∈ active, ∀ j t, t ∈ Icc 0 T → rate j t x ≤ C₁)
    (h₂ : ∀ x ∈ large, ∀ j t, t ∈ Icc 0 T → rate j t x ≤ C₂) :
    ∀ᵐ ω ∂MarkedNoise.law J, ∀ x t, t ≤ T →
      (∀ s, 0 ≤ s → s < t → process active jump rate C₁ x ω s ∈ active) →
      process large jump rate C₂ x ω t = process active jump rate C₁ x ω t := by
  filter_upwards [ae_clamp_process_agrees active jump rate T,
    ae_clamp_process_agrees large jump rate T,
    ae_process_agree_before_exit active jump (clampRate T rate) large hsets C₁ C₂
      (clampRate_bound active rate T C₁ hT h₁)
      (clampRate_bound large rate T C₂ hT h₂)] with ω ha hl he
  intro x t ht hbefore
  rw [← hl C₂ x t ht, ← ha C₁ x t ht]
  apply he x t
  intro s hs hst
  rw [ha C₁ x s (hst.le.trans ht)]
  exact hbefore s hs hst

end CarryingCapacity.TimeDependentRateLocalization
