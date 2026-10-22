import CarryingCapacity.PoissonPastIndependence

/-!
# The compensated canonical Poisson clock is a martingale

The martingale property is deduced from the constructed clock's independence
from its full past and its proved first moments. No martingale property is
assumed for the sample paths or the underlying measure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace CarryingCapacity.PoissonMartingale
open CountableJumpProcess FrozenProcess PoissonIncrements PoissonMoments
open PoissonPastIndependence

/-- The count process compensated by its deterministic rate. -/
def compensated (r : ℝ) (t : ℝ≥0) (ω : ClockSpace) : ℝ :=
  (proposalCount ω t : ℝ) - r*(t:ℝ)

/-- Each compensated count has a finite first absolute moment. -/
theorem integrable_compensated (r : ℝ) (hr : 0 < r) (t : ℝ≥0) :
    Integrable (compensated r t) (waitingTimeLaw r hr) :=
  (integrable_proposalCount r hr t t.property).sub (integrable_const _)

/-- The compensated count is adapted to the actual count-process natural filtration. -/
theorem adapted_compensated (r : ℝ) : Adapted naturalFiltration (compensated r) := by
  intro t
  have hN : StronglyMeasurable[naturalFiltration t] (fun ω => proposalCount ω (t:ℝ)) :=
    Filtration.adapted_natural (fun s : ℝ≥0 => (measurable_proposalCount s).stronglyMeasurable) t
  have hreal : StronglyMeasurable[naturalFiltration t] (fun ω => (proposalCount ω (t:ℝ) : ℝ)) :=
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hN.measurable).stronglyMeasurable
  exact hreal.sub stronglyMeasurable_const

/-- The compensated difference over two deterministic times has zero conditional mean
with respect to all observations up to the earlier time. -/
theorem conditional_compensated_difference (r : ℝ) (hr : 0 < r) (s t : ℝ≥0) (hst : s ≤ t) :
    (waitingTimeLaw r hr)[compensated r t - compensated r s | naturalFiltration s]
      =ᵐ[waitingTimeLaw r hr] fun _ => (0 : ℝ) := by
  let d : ℝ := (t:ℝ)-(s:ℝ)
  have hd : 0 ≤ d := sub_nonneg.mpr hst
  let I : ClockSpace → ℝ := fun ω => (increment ω s d : ℝ)
  have hI : Integrable I (waitingTimeLaw r hr) := integrable_increment r hr s d s.property hd
  have hrel : compensated r t - compensated r s =ᵐ[waitingTimeLaw r hr]
      I - (fun _ => r*d) := by
    filter_upwards [ae_locally_finite r hr] with ω hω
    have hle := proposalCount_mono hω.2 (show (s:ℝ) ≤ (t:ℝ) from hst)
    have htime : (s:ℝ)+d = (t:ℝ) := by dsimp [d]; ring
    simp only [Pi.sub_apply,compensated,I,increment,htime,Nat.cast_sub hle]
    dsimp [d]
    ring
  have hmean := conditional_increment r hr s d s.property hd
  rw [← naturalFiltration_eq_past s] at hmean
  have hsub := condExp_sub hI (integrable_const (r*d)) (naturalFiltration s)
  rw [condExp_const (naturalFiltration.le s)] at hsub
  apply (condExp_congr_ae hrel).trans
  apply hsub.trans
  filter_upwards [hmean] with ω hω
  change (waitingTimeLaw r hr)[I | naturalFiltration s] ω - r*d = 0
  rw [hω]
  ring

/-- The actual compensated Poisson clock is a martingale for its full natural filtration. -/
theorem martingale_compensated (r : ℝ) (hr : 0 < r) :
    Martingale (compensated r) naturalFiltration (waitingTimeLaw r hr) := by
  refine ⟨adapted_compensated r, ?_⟩
  intro s t hst
  have hzero := conditional_compensated_difference r hr s t hst
  have hsub := condExp_sub (integrable_compensated r hr t) (integrable_compensated r hr s)
    (naturalFiltration s)
  rw [condExp_of_stronglyMeasurable (naturalFiltration.le s) (adapted_compensated r s)
    (integrable_compensated r hr s)] at hsub
  filter_upwards [hzero,hsub] with ω h0 hs
  simp only [Pi.sub_apply] at hs
  linarith

/-- The compensated process has zero expectation at each deterministic time. -/
theorem integral_compensated (r : ℝ) (hr : 0 < r) (t : ℝ≥0) :
    (∫ ω, compensated r t ω ∂waitingTimeLaw r hr) = 0 := by
  simp only [compensated]
  rw [integral_sub (integrable_proposalCount r hr t t.property) (integrable_const _),
    integral_proposalCount r hr t t.property,integral_const]
  simp

/-- Freeze the compensated process at a deterministic finite horizon. -/
def deterministicStopped (r : ℝ) (T t : ℝ≥0) : ClockSpace → ℝ :=
  compensated r (min t T)

theorem integrable_deterministicStopped (r : ℝ) (hr : 0 < r) (T t : ℝ≥0) :
    Integrable (deterministicStopped r T t) (waitingTimeLaw r hr) :=
  integrable_compensated r hr (min t T)

theorem adapted_deterministicStopped (r : ℝ) (T : ℝ≥0) :
    Adapted naturalFiltration (deterministicStopped r T) := by
  intro t
  exact (adapted_compensated r (min t T)).mono (naturalFiltration.mono (min_le_left t T))

/-- Stopping at a deterministic horizon preserves the actual martingale property.
This theorem makes no assertion about arbitrary random stopping times. -/
theorem martingale_deterministicStopped (r : ℝ) (hr : 0 < r) (T : ℝ≥0) :
    Martingale (deterministicStopped r T) naturalFiltration (waitingTimeLaw r hr) := by
  refine ⟨adapted_deterministicStopped r T, ?_⟩
  intro s t hst
  by_cases hs : s ≤ T
  · have h := (martingale_compensated r hr).2 s (min t T) (le_min hst hs)
    simpa only [deterministicStopped,min_eq_left hs] using h
  · have hTs : T ≤ s := le_of_lt (lt_of_not_ge hs)
    have hTt : T ≤ t := hTs.trans hst
    simp only [deterministicStopped,min_eq_right hTs,min_eq_right hTt]
    rw [condExp_of_stronglyMeasurable (naturalFiltration.le s)
      ((adapted_compensated r T).mono (naturalFiltration.mono hTs))
      (integrable_compensated r hr T)]

end CarryingCapacity.PoissonMartingale
