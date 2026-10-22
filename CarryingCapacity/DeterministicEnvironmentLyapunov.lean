import CarryingCapacity.DeterministicEnvironmentFrozen
import CarryingCapacity.LyapunovFlowSpace
import CarryingCapacity.LyapunovLocalization

/-!
# Lyapunov and spatial localization bounds for deterministic environments

The prescribed law curve has a finite genuine Lyapunov moment bound on the
construction horizon. Together with the manuscript's LyapunovControl this
implies a uniform affine drift for the endpoint-clamped rates. The activity
hypothesis independently supplies uniform rate bounds on every finite spatial
sublevel. The manuscript curve space supplies the required moment bound by its
actual extended-integral envelope. No invariance or forward equation is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal Topology BigOperators

namespace CarryingCapacity.DeterministicEnvironmentLyapunov
open LyapunovFlowSpace DeterministicEnvironmentFrozen

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q)

/-- The Lyapunov function is nonnegative by its domination of the moment weight. -/
theorem function_nonnegative (x : State D) : 0 ≤ control.function x := by
  have hw := momentWeight_nonneg κ x
  have hd := control.dominates x
  linarith

/-- The exact state sublevels used for the spatial frozen construction are finite. -/
theorem finite_sublevels (R : ℝ) : {x : State D | control.function x < R}.Finite :=
  finite_lyapunov_sublevel κ control.function (fun x =>
    (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)).trans (control.dominates x)) R

/-- The exact constant supplied with the Lyapunov drift assumption. -/
def driftConstant : ℝ := control.drift.val

theorem driftConstant_nonnegative : 0 ≤ driftConstant control :=
  control.drift.property.1

/-- A finite genuine Lyapunov bound includes integrability, rather than using
an ordinary integral's default value on nonintegrable laws. -/
theorem integrable_and_bound (μ : MomentLaw κ D) (B : ℝ) (hB : 0 ≤ B)
    (hμ : lyapunovIntegral control.function μ ≤ ENNReal.ofReal B) :
    Integrable control.function μ.measure ∧ (∫ x, control.function x ∂μ.measure) ≤ B :=
  (lyapunovIntegral_le_iff (function_nonnegative control) μ hB).mp hμ

/-- The exact Lyapunov inequality retains the prescribed environment moment. -/
theorem generator_le (μ : MomentLaw κ D) (hμ : Integrable control.function μ.measure)
    (x : State D) : q.generator μ control.function x ≤
      driftConstant control * (1 + control.function x + ∫ y, control.function y ∂μ.measure) :=
  control.drift.property.2 x μ hμ

/-- A uniformly bounded genuine environmental Lyapunov moment gives the
additive drift bound used before Gronwall. -/
theorem generator_le_of_bound (μ : MomentLaw κ D) (B : ℝ) (hB : 0 ≤ B)
    (hμ : lyapunovIntegral control.function μ ≤ ENNReal.ofReal B) (x : State D) :
    q.generator μ control.function x ≤ driftConstant control * (1 + control.function x + B) := by
  obtain ⟨hi, hbound⟩ := integrable_and_bound control μ B hB hμ
  exact (generator_le control μ hi x).trans
    (mul_le_mul_of_nonneg_left (by linarith) (driftConstant_nonnegative control))

/-- A single nonnegative affine coefficient works at every clamped time. -/
def affineConstant (B : ℝ) : ℝ := driftConstant control * (1 + B)

theorem affineConstant_nonnegative (B : ℝ) (hB : 0 ≤ B) :
    0 ≤ affineConstant control B :=
  mul_nonneg (driftConstant_nonnegative control) (by linarith)

variable (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T)
  (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ t ∈ Icc 0 T, lyapunovIntegral control.function (v t) ≤ ENNReal.ofReal B)
include hT hB hEnv

/-- Integrability and the same moment bound hold for the endpoint extension
at every real time, including times after the selected horizon. -/
theorem clamped_integrable_and_bound (t : ℝ) :
    Integrable control.function (v (max 0 (min t T))).measure ∧
      (∫ x, control.function x ∂(v (max 0 (min t T))).measure) ≤ B :=
  integrable_and_bound control _ B hB
    (hEnv _ ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩)

/-- Exact additive drift for the actual time-dependent jump rates. -/
theorem clamped_generator_le (t : ℝ) (x : State D) :
    (∑ j, timeRate κ q v T j t x * (control.function (Jump.advance j x) - control.function x)) ≤
      driftConstant control * (1 + control.function x + B) :=
  generator_le_of_bound control _ B hB
    (hEnv _ ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩) x

/-- The genuine unclipped generator satisfies a uniform affine bound. -/
theorem clamped_generator_affine_bound (t : ℝ) (x : State D) :
    (∑ j, timeRate κ q v T j t x * (control.function (Jump.advance j x) - control.function x)) ≤
      affineConstant control B * (1 + control.function x) := by
  apply (clamped_generator_le control v T hT B hB hEnv t x).trans
  have hV := function_nonnegative control x
  have hC := driftConstant_nonnegative control
  unfold affineConstant
  have hprod : 0 ≤ B * control.function x := mul_nonneg hB hV
  nlinarith

/-- Freezing on any spatial region preserves the same affine Lyapunov bound. -/
theorem frozen_generator_affine_bound (active : Finset (State D)) (t : ℝ) (x : State D) :
    TimeDependentGeneratorIntegral.frozenGenerator active Jump.advance (timeRate κ q v T)
      control.function t x ≤ affineConstant control B * (1 + control.function x) := by
  by_cases hx : x ∈ active
  · simpa only [TimeDependentGeneratorIntegral.frozenGenerator, FrozenProcess.frozenGenerator,
      hx, ↓reduceIte] using clamped_generator_affine_bound control v T hT B hB hEnv t x
  · simp only [TimeDependentGeneratorIntegral.frozenGenerator, FrozenProcess.frozenGenerator,
      hx, ↓reduceIte]
    exact mul_nonneg (affineConstant_nonnegative control B hB)
      (by have hV := function_nonnegative control x; linarith)

omit B hB hEnv in
/-- Uniform spatial cutoffs required by the global localization are derived
from activity and compactness of the actual continuous moment-law curve. -/
theorem exists_positive_uniform_rate_bounds (hActivity : MomentActivityBound κ q)
    (hv : ContinuousOn v (Icc 0 T)) :
    ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ LyapunovLocalization.active control.function (finite_sublevels control) n,
        ∀ j t, timeRate κ q v T j t x ≤ C := by
  intro n
  obtain ⟨C, hC, hbound⟩ := DeterministicEnvironmentRates.exists_positive_rate_bound_on_Icc
    κ q hActivity (LyapunovLocalization.active control.function (finite_sublevels control) n) v T hv
  refine ⟨C, hC, fun x hx j t => ?_⟩
  exact hbound x hx j _ ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

omit B hB hEnv in
/-- The exact rate-bound premise for the generic spatial patch is discharged. -/
theorem exists_uniform_rate_bounds (hActivity : MomentActivityBound κ q)
    (hv : ContinuousOn v (Icc 0 T)) :
    ∀ n : ℕ, ∃ C : ℝ,
      ∀ x ∈ LyapunovLocalization.active control.function (finite_sublevels control) n,
        ∀ j t, timeRate κ q v T j t x ≤ C := by
  intro n
  obtain ⟨C, _, hC⟩ := exists_positive_uniform_rate_bounds control v T hT hActivity hv n
  exact ⟨C, hC⟩

end CarryingCapacity.DeterministicEnvironmentLyapunov

namespace CarryingCapacity.DeterministicEnvironmentLyapunov
open LyapunovFlowSpace DeterministicEnvironmentFrozen

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q)

/-- Endpoint projection from the full time line to the manuscript time interval. -/
def clampPoint (T : ℝ) (hT : 0 ≤ T) (t : ℝ) : Icc (0 : ℝ) T :=
  ⟨max 0 (min t T), le_max_left _ _, max_le hT (min_le_right _ _)⟩

theorem continuous_clampPoint (T : ℝ) (hT : 0 ≤ T) : Continuous (clampPoint T hT) :=
  (continuous_const.max (continuous_id.min continuous_const)).subtype_mk _

/-- The concrete continuous real-time extension of a manuscript candidate curve. -/
def manuscriptExtension (ν : MomentLaw κ D) (C T : ℝ) (hT : 0 ≤ T)
    (v : ManuscriptCurves control.function ν C T hT) (t : ℝ) : MomentLaw κ D :=
  v.val (clampPoint T hT t)

theorem continuous_manuscriptExtension (ν : MomentLaw κ D) (C T : ℝ) (hT : 0 ≤ T)
    (v : ManuscriptCurves control.function ν C T hT) :
    Continuous (manuscriptExtension control ν C T hT v) :=
  v.val.continuous.comp (continuous_clampPoint T hT)

/-- The extension agrees with every value of the given curve on its interval. -/
theorem manuscriptExtension_eq (ν : MomentLaw κ D) (C T : ℝ) (hT : 0 ≤ T)
    (v : ManuscriptCurves control.function ν C T hT) (t : Icc (0 : ℝ) T) :
    manuscriptExtension control ν C T hT v t = v.val t := by
  apply congrArg v.val
  apply Subtype.ext
  exact (congrArg (max 0) (min_eq_left t.property.2)).trans (max_eq_right t.property.1)

/-- Its initial law is the prescribed initial law of the actual curve space. -/
theorem manuscriptExtension_initial (ν : MomentLaw κ D) (C T : ℝ) (hT : 0 ≤ T)
    (v : ManuscriptCurves control.function ν C T hT) :
    manuscriptExtension control ν C T hT v 0 = ν := by
  rw [show (0 : ℝ) = (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T).val from rfl,
    manuscriptExtension_eq]
  exact curve_initial v

/-- The manuscript envelope is increasing at nonnegative drift constant. -/
theorem exponentialEnvelope_mono_time {m C s t : ℝ} (hm : 0 ≤ m) (hC : 0 ≤ C)
    (hst : s ≤ t) : exponentialEnvelope m C s ≤ exponentialEnvelope m C t := by
  have he : Real.exp (2 * C * s) ≤ Real.exp (2 * C * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst (by positivity))
  change (m + 1 / 2) * Real.exp (2 * C * s) - 1 / 2 ≤
    (m + 1 / 2) * Real.exp (2 * C * t) - 1 / 2
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left he (by linarith)) _

/-- The terminal envelope is an explicit uniform environmental moment bound. -/
def manuscriptBound (ν : MomentLaw κ D) (C T : ℝ) : ℝ :=
  exponentialEnvelope (∫ x, control.function x ∂ν.measure) C T

theorem manuscriptBound_nonnegative (ν : MomentLaw κ D) (C T : ℝ)
    (hC : 0 ≤ C) (hT : 0 ≤ T) : 0 ≤ manuscriptBound control ν C T :=
  (integral_nonneg (function_nonnegative control)).trans
    (le_exponentialEnvelope (integral_nonneg (function_nonnegative control)) hC hT)

/-- Every value of the extended candidate curve has a genuine finite Lyapunov
moment and is bounded by the terminal exponential envelope. -/
theorem manuscriptExtension_bound (ν : MomentLaw κ D) (C T : ℝ)
    (hC : 0 ≤ C) (hT : 0 ≤ T) (v : ManuscriptCurves control.function ν C T hT) (t : ℝ) :
    lyapunovIntegral control.function (manuscriptExtension control ν C T hT v t) ≤
      ENNReal.ofReal (manuscriptBound control ν C T) := by
  exact (v.property.2 (clampPoint T hT t)).trans
    (ENNReal.ofReal_le_ofReal (exponentialEnvelope_mono_time
      (integral_nonneg (function_nonnegative control)) hC (clampPoint T hT t).property.2))

theorem manuscriptExtension_integrable_and_bound (ν : MomentLaw κ D) (C T : ℝ)
    (hC : 0 ≤ C) (hT : 0 ≤ T) (v : ManuscriptCurves control.function ν C T hT) (t : ℝ) :
    Integrable control.function (manuscriptExtension control ν C T hT v t).measure ∧
      (∫ x, control.function x ∂(manuscriptExtension control ν C T hT v t).measure) ≤
        manuscriptBound control ν C T :=
  integrable_and_bound control _ _ (manuscriptBound_nonnegative control ν C T hC hT)
    (manuscriptExtension_bound control ν C T hC hT v t)

/-- The actual manuscript curve constraint discharges the generic affine-drift
premise for its endpoint-clamped rates. No invariance of an evolution map is used. -/
theorem manuscript_generator_affine_bound (ν : MomentLaw κ D) (C T : ℝ)
    (hC : 0 ≤ C) (hT : 0 ≤ T) (v : ManuscriptCurves control.function ν C T hT)
    (t : ℝ) (x : State D) :
    (∑ j, timeRate κ q (manuscriptExtension control ν C T hT v) T j t x *
      (control.function (Jump.advance j x) - control.function x)) ≤
        affineConstant control (manuscriptBound control ν C T) * (1 + control.function x) :=
  clamped_generator_affine_bound control _ T hT _
    (manuscriptBound_nonnegative control ν C T hC hT)
    (fun s _ => manuscriptExtension_bound control ν C T hC hT v s) t x

/-- Every canonical spatial cutoff has a uniform rate bound for a manuscript
candidate curve, derived entirely from the activity assumption. -/
theorem manuscript_uniform_rate_bounds (hActivity : MomentActivityBound κ q)
    (ν : MomentLaw κ D) (C T : ℝ) (hT : 0 ≤ T)
    (v : ManuscriptCurves control.function ν C T hT) :
    ∀ n : ℕ, ∃ c : ℝ,
      ∀ x ∈ LyapunovLocalization.active control.function (finite_sublevels control) n,
        ∀ j t, timeRate κ q (manuscriptExtension control ν C T hT v) T j t x ≤ c :=
  exists_uniform_rate_bounds control _ T hT hActivity
    (continuous_manuscriptExtension control ν C T hT v).continuousOn

/-- Coupling regularity supplies the measurability needed by the actual
stochastic construction at every fixed state and jump label. -/
theorem manuscript_measurable_timeRate (hCoupling : MomentCouplingBound κ q)
    (ν : MomentLaw κ D) (C T : ℝ) (hT : 0 ≤ T)
    (v : ManuscriptCurves control.function ν C T hT) (j : Jump D) (x : State D) :
    Measurable (fun t => timeRate κ q (manuscriptExtension control ν C T hT v) T j t x) :=
  DeterministicEnvironmentFrozen.measurable_timeRate κ q _ T
    (continuous_manuscriptExtension control ν C T hT v).continuousOn hCoupling hT j x

/-- On the original horizon the sharper drift retains the pointwise manuscript
envelope K(t), which is the input needed for a later invariance comparison. -/
theorem manuscript_generator_envelope_bound (ν : MomentLaw κ D) (C T : ℝ)
    (hC : 0 ≤ C) (hT : 0 ≤ T) (v : ManuscriptCurves control.function ν C T hT)
    (t : ℝ) (ht : t ∈ Icc 0 T) (x : State D) :
    (∑ j, timeRate κ q (manuscriptExtension control ν C T hT v) T j t x *
      (control.function (Jump.advance j x) - control.function x)) ≤
        driftConstant control * (1 + control.function x +
          exponentialEnvelope (∫ y, control.function y ∂ν.measure) C t) := by
  have he (j : Jump D) : timeRate κ q (manuscriptExtension control ν C T hT v) T j t x =
      q.rate j x (v.val ⟨t, ht⟩) :=
    (timeRate_eq κ q _ T j t ht x).trans
      (congrArg (q.rate j x) (manuscriptExtension_eq control ν C T hT v ⟨t, ht⟩))
  simp_rw [he]
  exact generator_le_of_bound control _ _
    ((integral_nonneg (function_nonnegative control)).trans
      (le_exponentialEnvelope (integral_nonneg (function_nonnegative control)) hC ht.1))
    (v.property.2 ⟨t, ht⟩) x

end CarryingCapacity.DeterministicEnvironmentLyapunov
