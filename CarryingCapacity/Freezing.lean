import Mathlib

/-!
# Deterministic freezing and patching

This file formalizes deterministic parts of Sections 3.1 and 3.3 of Xie's
manuscript. It does not construct Poisson random measures, prove their local
finiteness, derive stopping-time estimates, or establish non-explosion.

The finite recursion takes proposal data and a state-dependent decoder as
inputs. The patching theorem takes compatibility and exhaustion as explicit
hypotheses. Those are the conclusions that the stochastic argument must supply.
-/

noncomputable section
open scoped NNReal ENNReal Topology

namespace CarryingCapacity.Freezing

section FiniteRecursion

variable {E J M : Type*} [DecidableEq E] [Fintype J]

/-- The active set together with every state reachable by one jump. -/
def oneStepEnlargement (active : Finset E) (jump : J → E → E) : Finset E :=
  active ∪ ((Finset.univ.product active).image fun p : J × E => jump p.1 p.2)

/-- Outside `active` the state never moves. Inside it, `decode` either rejects
this proposal (`none`) or selects one of the finitely many jump directions. -/
def frozenStep (active : Finset E) (jump : J → E → E)
    (decode : E → M → Option J) (x : E) (mark : M) : E :=
  if x ∈ active then
    match decode x mark with
    | none => x
    | some j => jump j x
  else x

/-- Deterministic jump-by-jump recursion through a finite list of proposals. -/
def run (active : Finset E) (jump : J → E → E)
    (decode : E → M → Option J) : E → List M → E
  | x, [] => x
  | x, mark :: marks => run active jump decode
      (frozenStep active jump decode x mark) marks

variable (active : Finset E) (jump : J → E → E) (decode : E → M → Option J)

omit [Fintype J] in
@[simp] theorem frozenStep_outside {x : E} (hx : x ∉ active) (mark : M) :
    frozenStep active jump decode x mark = x := by
  simp [frozenStep, hx]

theorem active_subset_enlargement : active ⊆ oneStepEnlargement active jump := by
  intro x hx
  exact Finset.mem_union.mpr (Or.inl hx)

theorem jump_mem_enlargement {x : E} (hx : x ∈ active) (j : J) :
    jump j x ∈ oneStepEnlargement active jump := by
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_image.mpr
  exact ⟨(j, x), by simp [hx], rfl⟩

theorem frozenStep_mem_enlargement {x : E}
    (hx : x ∈ oneStepEnlargement active jump) (mark : M) :
    frozenStep active jump decode x mark ∈ oneStepEnlargement active jump := by
  by_cases hactive : x ∈ active
  · cases hdecode : decode x mark with
    | none => simpa [frozenStep, hactive, hdecode] using hx
    | some j =>
      simpa [frozenStep, hactive, hdecode] using
        jump_mem_enlargement active jump hactive j
  · simpa [frozenStep, hactive] using hx

theorem run_mem_enlargement {x : E}
    (hx : x ∈ oneStepEnlargement active jump) (marks : List M) :
    run active jump decode x marks ∈ oneStepEnlargement active jump := by
  induction marks generalizing x with
  | nil => exact hx
  | cons mark marks ih =>
    exact ih (frozenStep_mem_enlargement active jump decode hx mark)

/- This also covers initial states outside the active set, which need not
belong to the deterministic finite enlargement. -/
omit [Fintype J] in
theorem run_outside {x : E} (hx : x ∉ active) (marks : List M) :
    run active jump decode x marks = x := by
  induction marks with
  | nil => rfl
  | cons mark marks ih =>
    simpa [run, frozenStep, hx] using ih

theorem run_mem_or_eq_initial (x : E) (marks : List M) :
    run active jump decode x marks ∈ oneStepEnlargement active jump ∨
      run active jump decode x marks = x := by
  by_cases hx : x ∈ active
  · left
    exact run_mem_enlargement active jump decode
      (active_subset_enlargement active jump hx) marks
  · right
    exact run_outside active jump decode hx marks

omit [Fintype J] in
theorem run_append (x : E) (pre post : List M) :
    run active jump decode x (pre ++ post) =
      run active jump decode (run active jump decode x pre) post := by
  induction pre generalizing x with
  | nil => rfl
  | cons mark marks ih =>
    simpa [run] using ih (frozenStep active jump decode x mark)

/- The accepted exit jump is retained; every subsequent proposal is ignored. -/
omit [Fintype J] in
theorem frozen_after_exit (x : E) (pre post : List M)
    (hexit : run active jump decode x pre ∉ active) :
    run active jump decode x (pre ++ post) = run active jump decode x pre := by
  rw [run_append]
  exact run_outside active jump decode hexit post

end FiniteRecursion

section Patching

variable {Time E : Type*}

/-- Local paths agreeing on nested regions which cover the time domain. -/
structure CompatibleFamily (Time E : Type*) where
  path : ℕ → Time → E
  region : ℕ → Set Time
  nested : Monotone region
  compatible : ∀ r s, r ≤ s → ∀ t, t ∈ region r → path s t = path r t
  exhaustive : ∀ t, ∃ r, t ∈ region r

namespace CompatibleFamily

variable (F : CompatibleFamily Time E)

/-- Choose any region containing this time. Compatibility removes dependence
on that choice, as proved by `patch_eq` below. -/
def patch (t : Time) : E := F.path (Classical.choose (F.exhaustive t)) t

theorem patch_eq (r : ℕ) (t : Time) (ht : t ∈ F.region r) :
    F.patch t = F.path r t := by
  let s := Classical.choose (F.exhaustive t)
  have hs : t ∈ F.region s := Classical.choose_spec (F.exhaustive t)
  change F.path s t = F.path r t
  rcases le_total r s with hrs | hsr
  · exact F.compatible r s hrs t ht
  · exact (F.compatible s r hsr t hs).symm

theorem patch_unique (Y : Time → E)
    (hY : ∀ r t, t ∈ F.region r → Y t = F.path r t) : Y = F.patch := by
  funext t
  obtain ⟨r, hr⟩ := F.exhaustive t
  exact (hY r t hr).trans (F.patch_eq r t hr).symm

theorem existsUnique_patch :
    ∃! Y : Time → E, ∀ r t, t ∈ F.region r → Y t = F.path r t := by
  refine ⟨F.patch, ?_, ?_⟩
  · exact F.patch_eq
  · intro Y hY
    exact F.patch_unique Y hY

end CompatibleFamily

/-- A family localized by nondecreasing extended nonnegative exit times.
Compatibility includes the exit time itself, so an exit overshoot is retained. -/
structure ExitFamily (E : Type*) where
  path : ℕ → ℝ≥0 → E
  exit : ℕ → ℝ≥0∞
  monotone_exit : Monotone exit
  compatible : ∀ r s, r ≤ s → ∀ t : ℝ≥0,
    (t : ℝ≥0∞) ≤ exit r → path s t = path r t
  exhaustive : ∀ t : ℝ≥0, ∃ r, (t : ℝ≥0∞) < exit r

namespace ExitFamily

variable (F : ExitFamily E)

/-- The deterministic regions on which the localized paths are prescribed. -/
def toCompatibleFamily : CompatibleFamily ℝ≥0 E where
  path := F.path
  region r := {t | (t : ℝ≥0∞) ≤ F.exit r}
  nested := by
    intro r s hrs t ht
    exact le_trans ht (F.monotone_exit hrs)
  compatible := F.compatible
  exhaustive := by
    intro t
    obtain ⟨r, hr⟩ := F.exhaustive t
    exact ⟨r, le_of_lt hr⟩

def patch : ℝ≥0 → E := F.toCompatibleFamily.patch

theorem patch_eq (r : ℕ) (t : ℝ≥0) (ht : (t : ℝ≥0∞) ≤ F.exit r) :
    F.patch t = F.path r t :=
  F.toCompatibleFamily.patch_eq r t ht

theorem patch_eq_before_exit (r : ℕ) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < F.exit r) : F.patch t = F.path r t :=
  F.patch_eq r t (le_of_lt ht)

/-- A single sufficiently large level supplies the whole finite time horizon,
and every higher level gives the same path on that horizon. -/
theorem eventually_agrees_on_horizon (T : ℝ≥0) :
    ∃ R, ∀ S, R ≤ S → ∀ t : ℝ≥0, t ≤ T → F.patch t = F.path S t := by
  obtain ⟨R, hR⟩ := F.exhaustive T
  refine ⟨R, ?_⟩
  intro S hRS t ht
  apply F.patch_eq
  have ht' : (t : ℝ≥0∞) ≤ (T : ℝ≥0∞) := by exact_mod_cast ht
  exact ht'.trans ((le_of_lt hR).trans (F.monotone_exit hRS))

theorem existsUnique_patch :
    ∃! Y : ℝ≥0 → E, ∀ (r : ℕ) (t : ℝ≥0), (t : ℝ≥0∞) ≤ F.exit r → Y t = F.path r t :=
  F.toCompatibleFamily.existsUnique_patch

end ExitFamily
end Patching

section ExitTails

open Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A reciprocal upper bound forces the event of belonging to every set to
have measure zero. Nestedness and measurability of the individual sets are
not needed for this consequence, since the intersection is contained in each. -/
theorem measure_iInter_eq_zero_of_reciprocal_bound (μ : Measure Ω)
    (events : ℕ → Set Ω) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hbound : ∀ n : ℕ, μ (events n) ≤ C / ((n + 1 : ℕ) : ℝ≥0∞)) :
    μ (⋂ n, events n) = 0 := by
  have hinv : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ≥0∞))⁻¹) atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun n : ℕ => C / ((n + 1 : ℕ) : ℝ≥0∞)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (ENNReal.Tendsto.const_mul hinv (Or.inr hC))
  apply le_antisymm _ (zero_le _)
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
  intro n
  exact (measure_mono (Set.iInter_subset events n)).trans (hbound n)

/-- For a fixed horizon, the Lyapunov exit-tail estimate implies that almost
surely at least one localization level has not exited by that horizon. -/
theorem ae_exists_exit_gt_of_reciprocal_bound (μ : Measure Ω)
    (exit : ℕ → Ω → ℝ≥0∞) (T : ℝ≥0∞) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hbound : ∀ n : ℕ, μ {ω | exit n ω ≤ T} ≤ C / ((n + 1 : ℕ) : ℝ≥0∞)) :
    ∀ᵐ ω ∂μ, ∃ n : ℕ, T < exit n ω := by
  have hnull := measure_iInter_eq_zero_of_reciprocal_bound μ
    (fun n => {ω | exit n ω ≤ T}) C hC hbound
  apply ae_iff.mpr
  have heq : {ω | ¬∃ n : ℕ, T < exit n ω} = ⋂ n, {ω | exit n ω ≤ T} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, not_exists, not_lt]
  rw [heq]
  exact hnull

/-- Countably many integer horizons suffice to obtain one probability-one
set on which the localizations exhaust every finite nonnegative horizon. -/
theorem ae_exhaustive_of_reciprocal_bounds (μ : Measure Ω)
    (exit : ℕ → Ω → ℝ≥0∞) (C : ℕ → ℝ≥0∞) (hC : ∀ k, C k ≠ ∞)
    (hbound : ∀ k n : ℕ, μ {ω | exit n ω ≤ (k : ℝ≥0∞)} ≤
      C k / ((n + 1 : ℕ) : ℝ≥0∞)) :
    ∀ᵐ ω ∂μ, ∀ T : ℝ≥0, ∃ n : ℕ, (T : ℝ≥0∞) < exit n ω := by
  have hint : ∀ k : ℕ, ∀ᵐ ω ∂μ, ∃ n : ℕ, (k : ℝ≥0∞) < exit n ω := by
    intro k
    exact ae_exists_exit_gt_of_reciprocal_bound μ exit k (C k) (hC k) (hbound k)
  have hall : ∀ᵐ ω ∂μ, ∀ k : ℕ, ∃ n : ℕ, (k : ℝ≥0∞) < exit n ω :=
    ae_all_iff.mpr hint
  filter_upwards [hall] with ω hω
  intro T
  obtain ⟨k, hk⟩ := exists_nat_gt T
  obtain ⟨n, hn⟩ := hω k
  refine ⟨n, ?_⟩
  have hk' : (T : ℝ≥0∞) < (k : ℝ≥0∞) := by exact_mod_cast hk
  exact hk'.trans hn

/-- Combining exit tails with pathwise compatibility gives an almost-sure
unique patched path. This asserts pointwise existence on a full-measure set;
it makes no claim of joint measurability, adaptedness, or a Poisson SDE law. -/
theorem ae_existsUnique_patch_of_exit_bounds {E : Type*} (μ : Measure Ω)
    (paths : ℕ → Ω → ℝ≥0 → E) (exit : ℕ → Ω → ℝ≥0∞)
    (hmono : ∀ ω, Monotone fun n => exit n ω)
    (hcompat : ∀ ω r s, r ≤ s → ∀ t : ℝ≥0,
      (t : ℝ≥0∞) ≤ exit r ω → paths s ω t = paths r ω t)
    (C : ℕ → ℝ≥0∞) (hC : ∀ k, C k ≠ ∞)
    (hbound : ∀ k n : ℕ, μ {ω | exit n ω ≤ (k : ℝ≥0∞)} ≤
      C k / ((n + 1 : ℕ) : ℝ≥0∞)) :
    ∀ᵐ ω ∂μ, ∃! Y : ℝ≥0 → E, ∀ (r : ℕ) (t : ℝ≥0),
      (t : ℝ≥0∞) ≤ exit r ω → Y t = paths r ω t := by
  have hexhaust := ae_exhaustive_of_reciprocal_bounds μ exit C hC hbound
  filter_upwards [hexhaust] with ω hω
  let F : ExitFamily E := {
    path := fun r => paths r ω
    exit := fun r => exit r ω
    monotone_exit := hmono ω
    compatible := hcompat ω
    exhaustive := hω }
  exact F.existsUnique_patch

end ExitTails
end CarryingCapacity.Freezing
