import CarryingCapacity.EmpiricalMeasure
import CarryingCapacity.RateControl
import CarryingCapacity.LyapunovLocalization

/-!
# The empirical particle configuration and its actual localization data

The configuration rates use the genuine empirical moment law. The empirical
Lyapunov function has finite sublevels, and its configuration drift follows
from the manuscript's single-lineage `LyapunovControl`. No configuration drift
or stochastic existence conclusion is assumed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical ENNReal

namespace CarryingCapacity.ConfigurationLocalization

abbrev Configuration (N D : ℕ) := Fin N → State D
abbrev Label (N D : ℕ) := Fin N × Jump D

variable {N D : ℕ}

/-- A label selects one particle and one of the original jump directions. -/
def jump (h : Label N D) (z : Configuration N D) : Configuration N D :=
  Function.update z h.1 (Jump.advance h.2 (z h.1))

/-- The configuration rate uses the actual empirical probability law. -/
def rate (κ : MomentScale) (q : Rates D (MomentLaw κ D)) (hN : 0 < N)
    (h : Label N D) (z : Configuration N D) : ℝ :=
  q.rate h.2 (z h.1) (empiricalLaw κ hN z)

theorem rate_nonnegative (κ : MomentScale) (q : Rates D (MomentLaw κ D))
    (hN : 0 < N) (h : Label N D) (z : Configuration N D) :
    0 ≤ rate κ q hN h z := q.nonnegative _ _ _

/-- The finite configuration's generator, in the same label convention as
its common-noise frozen construction. -/
def generator (κ : MomentScale) (q : Rates D (MomentLaw κ D)) (hN : 0 < N)
    (F : Configuration N D → ℝ) (z : Configuration N D) : ℝ :=
  ∑ h : Label N D, rate κ q hN h z * (F (jump h z) - F z)

theorem generator_eq_systemGenerator (κ : MomentScale) (q : Rates D (MomentLaw κ D))
    (hN : 0 < N) (F : Configuration N D → ℝ) (z : Configuration N D) :
    generator κ q hN F z =
      FiniteGenerator.systemGenerator Jump.advance q.rate (empiricalLaw κ hN) F z := by
  unfold generator FiniteGenerator.systemGenerator
  rw [Fintype.sum_prod_type]
  rfl

/-- The test function V^N is the empirical average of the supplied Ψ. -/
def lyapunov {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
    (control : LyapunovControl κ q) (z : Configuration N D) : ℝ :=
  FiniteGenerator.empiricalMean control.function z

variable {κ : MomentScale} {q : Rates D (MomentLaw κ D)} (control : LyapunovControl κ q)

theorem function_one_le (x : State D) : 1 ≤ control.function x :=
  (le_add_of_nonneg_right (momentWeight_nonneg κ x)).trans (control.dominates x)

theorem function_nonnegative (x : State D) : 0 ≤ control.function x :=
  zero_le_one.trans (function_one_le control x)

theorem lyapunov_nonnegative (z : Configuration N D) : 0 ≤ lyapunov control z :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))
    (Finset.sum_nonneg (fun i _ => function_nonnegative control (z i)))

theorem lyapunov_one_le (hN : 0 < N) (z : Configuration N D) :
    1 ≤ lyapunov control z := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  calc
    1 = (N : ℝ)⁻¹ * ∑ _ : Fin N, (1 : ℝ) := by simp [inv_mul_cancel₀ hNr]
    _ ≤ lyapunov control z :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => function_one_le control (z i)))
        (inv_nonneg.mpr (Nat.cast_nonneg N))

/-- Finite sublevels are derived from Ψ's domination of the moment weight. -/
theorem finite_sublevel (hN : 0 < N) (R : ℝ) :
    {z : Configuration N D | lyapunov control z < R}.Finite :=
  finite_configuration_lyapunov_sublevel hN κ control.function
    (fun x => (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)).trans (control.dominates x)) R

/-- One single-lineage drift constant works for every positive particle number. -/
def driftConstant : ℝ := Classical.choose control.drift

theorem driftConstant_nonnegative : 0 ≤ driftConstant control :=
  (Classical.choose_spec control.drift).1

theorem single_drift_empirical (hN : 0 < N) (z : Configuration N D) (i : Fin N) :
    q.generator (empiricalLaw κ hN z) control.function (z i) ≤
      driftConstant control * (1 + control.function (z i) + lyapunov control z) := by
  have hd := (Classical.choose_spec control.drift).2 (z i) (empiricalLaw κ hN z)
    (integrable_empiricalMeasure hN z control.function)
  simpa only [integral_empiricalLaw, lyapunov, driftConstant] using hd

/-- Exact generator algebra retains both the empirical law and the factor 1/N. -/
theorem generator_lyapunov (hN : 0 < N) (z : Configuration N D) :
    generator κ q hN (lyapunov control) z =
      (N : ℝ)⁻¹ * ∑ i, q.generator (empiricalLaw κ hN z) control.function (z i) := by
  rw [generator_eq_systemGenerator]
  exact FiniteGenerator.systemGenerator_empiricalMean Jump.advance q.rate
    (empiricalLaw κ hN) control.function z

/-- The closed configuration drift is derived directly from LyapunovControl,
with a constant independent of N and of the localization level. -/
theorem generator_lyapunov_le (hN : 0 < N) (z : Configuration N D) :
    generator κ q hN (lyapunov control) z ≤
      driftConstant control * (1 + 2 * lyapunov control z) := by
  rw [generator_eq_systemGenerator]
  exact FiniteGenerator.averaged_lyapunov_drift hN Jump.advance q.rate (empiricalLaw κ hN)
    control.function (driftConstant control) z (single_drift_empirical control hN z)

theorem frozenGenerator_eq (hN : 0 < N) (active : Finset (Configuration N D))
    (F : Configuration N D → ℝ) (z : Configuration N D) :
    FrozenProcess.frozenGenerator active jump (rate κ q hN) F z =
      if z ∈ active then generator κ q hN F z else 0 := rfl

/-- Freezing preserves the same Lyapunov upper bound, since V is nonnegative. -/
theorem frozenGenerator_lyapunov_le (hN : 0 < N)
    (active : Finset (Configuration N D)) (z : Configuration N D) :
    FrozenProcess.frozenGenerator active jump (rate κ q hN) (lyapunov control) z ≤
      driftConstant control * (1 + 2 * lyapunov control z) := by
  rw [frozenGenerator_eq]
  split_ifs with hz
  · exact generator_lyapunov_le control hN z
  · exact mul_nonneg (driftConstant_nonnegative control)
      (by have hV := lyapunov_nonnegative control z; positivity)

/-- The usual affine Lyapunov form, with an explicit uniform coefficient. -/
theorem frozenGenerator_lyapunov_le_affine (hN : 0 < N)
    (active : Finset (Configuration N D)) (z : Configuration N D) :
    FrozenProcess.frozenGenerator active jump (rate κ q hN) (lyapunov control) z ≤
      (2 * driftConstant control) * (1 + lyapunov control z) := by
  apply (frozenGenerator_lyapunov_le control hN active z).trans
  have hC := driftConstant_nonnegative control
  nlinarith

/-- The actual integer-threshold active regions for the particle model. -/
def active (hN : 0 < N) (n : ℕ) : Finset (Configuration N D) :=
  LyapunovLocalization.active (lyapunov control) (finite_sublevel control hN) n

@[simp] theorem mem_active (hN : 0 < N) (n : ℕ) (z : Configuration N D) :
    z ∈ active control hN n ↔ lyapunov control z < (n : ℝ) + 1 :=
  LyapunovLocalization.mem_active (lyapunov control) (finite_sublevel control hN) n z

theorem active_mono (hN : 0 < N) : Monotone (active control hN) :=
  LyapunovLocalization.active_mono (lyapunov control) (finite_sublevel control hN)

/-- A positive finite cutoff for the actual empirical configuration rates. -/
def rateBound (hN : 0 < N) (n : ℕ) : ℝ :=
  LyapunovLocalization.rateBound (lyapunov control) (finite_sublevel control hN)
    (rate κ q hN) n

theorem rateBound_positive (hN : 0 < N) (n : ℕ) : 0 < rateBound control hN n :=
  LyapunovLocalization.rateBound_pos (lyapunov control) (finite_sublevel control hN)
    (rate κ q hN) n

theorem rate_le_bound (hN : 0 < N) (n : ℕ) (z : Configuration N D)
    (hz : z ∈ active control hN n) (j : Label N D) :
    rate κ q hN j z ≤ rateBound control hN n :=
  LyapunovLocalization.rate_le_bound (lyapunov control) (finite_sublevel control hN)
    (rate κ q hN) n z hz j

variable {A : Type*}

/-- The actual common-noise frozen configuration process at level n. -/
def path (hN : 0 < N) (initial : A → Configuration N D) (n : ℕ)
    (p : CommonInitialNoise.Sample A (Label N D)) (t : ℝ) : Configuration N D :=
  LyapunovLocalization.path (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q hN) initial n p t

/-- Its genuine first exit from the empirical Lyapunov sublevel. -/
def exit (hN : 0 < N) (initial : A → Configuration N D) (n : ℕ)
    (p : CommonInitialNoise.Sample A (Label N D)) : ℝ≥0∞ :=
  LyapunovLocalization.exit (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q hN) initial n p

variable [MeasurableSpace A]

/-- The actual particle cutoffs have ordered exits on a single full-measure event. -/
theorem ae_exit_mono (hN : 0 < N) (initial : A → Configuration N D) (μ : Measure A) :
    ∀ᵐ p ∂CommonInitialNoise.law μ (Label N D), Monotone (fun n => exit control hN initial n p) :=
  LyapunovLocalization.ae_exit_mono (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q hN) initial μ

/-- All particle localization levels agree through the smaller actual exit,
including the jump that reaches or overshoots its threshold. -/
theorem ae_compatible (hN : 0 < N) (initial : A → Configuration N D) (μ : Measure A) :
    ∀ᵐ p ∂CommonInitialNoise.law μ (Label N D), ∀ n m : ℕ, n ≤ m →
      ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t ≤ exit control hN initial n p →
        path control hN initial m p t = path control hN initial n p t :=
  LyapunovLocalization.ae_compatible (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q hN) initial μ

end CarryingCapacity.ConfigurationLocalization
