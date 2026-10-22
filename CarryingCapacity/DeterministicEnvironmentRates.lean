import CarryingCapacity.RateControl
import CarryingCapacity.TransportMetric

/-!
# Regularity and finite-horizon bounds for deterministic environments

The manuscript's coupling assumption itself makes every fixed-state jump rate
Lipschitz in the actual adapted Wasserstein metric. Its activity assumption
then bounds all rates on a finite active region along any continuous law curve
on a compact time interval. These are derived consequences of the stated
assumptions, not added measurability or local boundedness premises.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators NNReal

namespace CarryingCapacity.DeterministicEnvironmentRates
variable {D : ℕ} (κ : MomentScale) (q : Rates D (MomentLaw κ D))

/-- At identical states, coupling cost consists exactly of unmatched-rate
variation multiplied by the actual jump length. -/
theorem couplingActivity_diagonal (x : State D) (μ ν : MomentLaw κ D) :
    couplingActivity κ q x x μ ν =
      ∑ h, |q.rate h x μ - q.rate h x ν| * adaptedDistance κ (Jump.advance h x) x := by
  unfold couplingActivity
  apply Finset.sum_congr rfl
  intro h _
  simp only [adaptedDistance_self, sub_zero, max_self, mul_zero, zero_add,
    max_eq_left (adaptedDistance_nonneg κ _ _)]
  rw [adaptedDistance_symm κ x (Jump.advance h x)]
  rcases le_total (q.rate h x μ) (q.rate h x ν) with hab | hba
  · rw [max_eq_right (sub_nonpos.mpr hab), max_eq_left (sub_nonneg.mpr hab),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · rw [max_eq_left (sub_nonneg.mpr hba), max_eq_right (sub_nonpos.mpr hba),
      abs_of_nonneg (sub_nonneg.mpr hba)]
    ring

/-- Normalized nonzero jump lengths control each fixed-state rate difference. -/
theorem abs_rate_sub_le_diagonal (h : Jump D) (x : State D) (μ ν : MomentLaw κ D) :
    |q.rate h x μ - q.rate h x ν| ≤ couplingActivity κ q x x μ ν := by
  rw [couplingActivity_diagonal]
  by_cases hh : Jump.Admissible h x
  · calc
      _ ≤ |q.rate h x μ - q.rate h x ν| * adaptedDistance κ (Jump.advance h x) x := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (Jump.one_le_adaptedDistance_advance κ h x hh) (abs_nonneg _)
      _ ≤ _ := Finset.single_le_sum
        (f := fun j => |q.rate j x μ - q.rate j x ν| * adaptedDistance κ (Jump.advance j x) x)
        (fun j _ => mul_nonneg (abs_nonneg _) (adaptedDistance_nonneg κ _ _)) (Finset.mem_univ h)
  · simp only [q.invalid_zero h x μ hh, q.invalid_zero h x ν hh, sub_self, abs_zero]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (adaptedDistance_nonneg κ _ _))

variable (hCoupling : MomentCouplingBound κ q)

/-- A constant provided by the exact weighted coupling assumption. -/
def couplingConstant : ℝ := Classical.choose hCoupling

theorem couplingConstant_nonnegative : 0 ≤ couplingConstant κ q hCoupling :=
  (Classical.choose_spec hCoupling).1

/-- Fixed-state rate variation has a finite state-dependent Lipschitz constant. -/
theorem abs_rate_sub_le (h : Jump D) (x : State D) (μ ν : MomentLaw κ D) :
    |q.rate h x μ - q.rate h x ν| ≤
      (couplingConstant κ q hCoupling * (1 + 2 * momentWeight κ x)) * wasserstein μ ν := by
  have hb := (Classical.choose_spec hCoupling).2 x x μ ν
  have hd := abs_rate_sub_le_diagonal κ q h x μ ν
  simp only [adaptedDistance_self, mul_zero, zero_add] at hb
  calc
    _ ≤ couplingActivity κ q x x μ ν := hd
    _ ≤ _ := by convert hb using 1; unfold couplingConstant; ring

/-- The exact regularity needed by a deterministic-environment construction. -/
theorem rate_lipschitz (h : Jump D) (x : State D) :
    LipschitzWith
      ⟨couplingConstant κ q hCoupling * (1 + 2 * momentWeight κ x),
        mul_nonneg (couplingConstant_nonnegative κ q hCoupling)
          (by have hx := momentWeight_nonneg κ x; positivity)⟩
      (fun μ : MomentLaw κ D => q.rate h x μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro μ ν
  simpa only [Real.dist_eq, momentLaw_dist] using abs_rate_sub_le κ q hCoupling h x μ ν

include hCoupling

theorem continuous_rate (h : Jump D) (x : State D) :
    Continuous (fun μ : MomentLaw κ D => q.rate h x μ) :=
  (rate_lipschitz κ q hCoupling h x).continuous

/-- Measurability is for the Borel sigma algebra of the proved Wasserstein metric. -/
theorem borel_measurable_rate (h : Jump D) (x : State D) :
    @Measurable (MomentLaw κ D) ℝ (borel (MomentLaw κ D)) inferInstance
      (fun μ => q.rate h x μ) :=
  (continuous_rate κ q hCoupling h x).borel_measurable

/-- Continuous environments give measurable actual time-dependent rates. -/
theorem measurable_timeRate (v : ℝ → MomentLaw κ D) (hv : Continuous v)
    (h : Jump D) (x : State D) : Measurable (fun t => q.rate h x (v t)) :=
  ((continuous_rate κ q hCoupling h x).comp hv).measurable

/-- The same rate continuity holds on a compact time interval. -/
theorem continuousOn_timeRate (v : ℝ → MomentLaw κ D) (T : ℝ)
    (hv : ContinuousOn v (Icc 0 T)) (h : Jump D) (x : State D) :
    ContinuousOn (fun t => q.rate h x (v t)) (Icc 0 T) :=
  (continuous_rate κ q hCoupling h x).comp_continuousOn hv

/-- A curve continuous only on the construction horizon has a measurable
time extension obtained by freezing its endpoints outside that horizon. -/
theorem measurable_clamped_timeRate (v : ℝ → MomentLaw κ D) (T : ℝ)
    (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))
    (h : Jump D) (x : State D) :
    Measurable (fun t => q.rate h x (v (max 0 (min t T)))) := by
  have hc : Continuous (fun t : ℝ => max 0 (min t T)) :=
    continuous_const.max (continuous_id.min continuous_const)
  have hv' : Continuous (fun t => v (max 0 (min t T))) :=
    hv.comp_continuous hc (fun t => ⟨le_max_left _ _,
      max_le hT (min_le_right _ _)⟩)
  exact ((continuous_rate κ q hCoupling h x).comp hv').measurable

omit hCoupling q in
/-- A continuous law curve has a bounded genuine moment on every compact horizon. -/
theorem exists_moment_bound (v : ℝ → MomentLaw κ D) (T : ℝ)
    (hv : ContinuousOn v (Icc 0 T)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 T, moment (v t) ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image
    ((moment_lipschitz (κ := κ) (D := D)).continuous.comp_continuousOn hv)
  refine ⟨max M 0, le_max_right _ _, fun t ht => ?_⟩
  exact (hM (mem_image_of_mem _ ht)).trans (le_max_left _ _)

omit hCoupling
variable (hActivity : MomentActivityBound κ q)
include hActivity

/-- A constant supplied by the exact weighted activity assumption. -/
def activityConstant : ℝ := Classical.choose hActivity

theorem activityConstant_nonnegative : 0 ≤ activityConstant κ q hActivity :=
  (Classical.choose_spec hActivity).1

/-- Every rate is bounded by weighted activity, including invalid jumps. -/
theorem rate_le_activity (h : Jump D) (x : State D) (μ : MomentLaw κ D) :
    q.rate h x μ ≤ activityConstant κ q hActivity * (1 + momentWeight κ x) * (1 + moment μ) := by
  apply (Finset.single_le_sum (fun j _ => q.nonnegative j x μ) (Finset.mem_univ h)).trans
  exact (totalRate_le_weightedActivity κ q x μ).trans ((Classical.choose_spec hActivity).2 x μ)

/-- The explicit activity bound along a moment-bounded deterministic environment. -/
theorem rate_le_of_moment_bound (h : Jump D) (x : State D) (μ : MomentLaw κ D)
    (M : ℝ) (hM : moment μ ≤ M) :
    q.rate h x μ ≤ activityConstant κ q hActivity * (1 + momentWeight κ x) * (1 + M) := by
  apply (rate_le_activity κ q hActivity h x μ).trans
  apply mul_le_mul_of_nonneg_left (by linarith)
  exact mul_nonneg (activityConstant_nonnegative κ q hActivity)
    (by have hx := momentWeight_nonneg κ x; positivity)

/-- A single strictly positive finite cutoff works for every active state,
label, and time on a compact horizon of a continuous environment. -/
theorem exists_positive_rate_bound_on_Icc (active : Finset (State D))
    (v : ℝ → MomentLaw κ D) (T : ℝ) (hv : ContinuousOn v (Icc 0 T)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ active, ∀ h t, t ∈ Icc 0 T → q.rate h x (v t) ≤ C := by
  obtain ⟨M, hM0, hM⟩ := exists_moment_bound κ v T hv
  let K : ℝ := ∑ x ∈ active, (1 + momentWeight κ x)
  have hK0 : 0 ≤ K := Finset.sum_nonneg (fun x _ =>
    by have hx := momentWeight_nonneg κ x; positivity)
  refine ⟨activityConstant κ q hActivity * K * (1 + M) + 1, ?_, ?_⟩
  · have hA := activityConstant_nonnegative κ q hActivity
    positivity
  · intro x hx h t ht
    apply (rate_le_of_moment_bound κ q hActivity h x (v t) M (hM t ht)).trans
    have hK : 1 + momentWeight κ x ≤ K :=
      Finset.single_le_sum (f := fun y : State D => 1 + momentWeight κ y)
        (fun y _ => by have hy := momentWeight_nonneg κ y; positivity) hx
    have hprod := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hK (activityConstant_nonnegative κ q hActivity))
      (by linarith : 0 ≤ 1 + M)
    linarith

end CarryingCapacity.DeterministicEnvironmentRates
