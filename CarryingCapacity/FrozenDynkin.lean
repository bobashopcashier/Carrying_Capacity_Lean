import CarryingCapacity.FrozenCountingIdentity
import CarryingCapacity.FrozenCompensation
import CarryingCapacity.FrozenGeneratorIntegral
import CarryingCapacity.FrozenPreStateTime

/-!
# Dynkin's expectation identity for the actual frozen process

The pathwise identity comes from chronological telescoping at actual marked
points. Predictability, finite-region integrability and compensation are
already proved for that same construction. Integrating the height coordinate
therefore identifies the expectation change with the frozen generator.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace CarryingCapacity.FrozenDynkin
open MarkedNoise MarkedIntensity CommonFrozenProcess FrozenPredictableIntegrand
  FrozenCompensation FrozenCountingIdentity FrozenGeneratorIntegral PredictableSets

variable {J E : Type*} [Fintype J] [DecidableEq E]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

omit [Fintype J] [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [PolishSpace E] [BorelSpace E] in
theorem horizonIntegral_eq_setIntegral (C : ℝ) (x : E) (V : E → ℝ)
    (j : J) (T : ℝ) (ω : Sample J) (ν : Measure (ℝ × ℝ)) :
    (∫ p, horizonIncrement active jump rate C x V j T (ω,p) ∂ν) =
      ∫ p in Ioc 0 T ×ˢ univ, jumpIncrement active jump rate C x V j (ω,p) ∂ν := by
  have he : (fun p => horizonIncrement active jump rate C x V j T (ω,p)) =
      (Ioc 0 T ×ˢ univ).indicator (fun p => jumpIncrement active jump rate C x V j (ω,p)) := by
    funext p
    by_cases ht : p.1 ∈ Ioc 0 T <;> by_cases hC : p.2 ≤ C <;>
      simp [horizonIncrement, PredictableSets.rectangle, Set.indicator_apply, ht, hC,
        jumpIncrement]
  rw [he, integral_indicator (measurableSet_Ioc.prod MeasurableSet.univ)]

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
theorem ae_change_eq_countingIntegral (C : ℝ) (x : E) (V : E → ℝ) (T : ℝ) :
    (fun ω => V (process active jump rate C x ω T) - V x) =ᵐ[law J]
      (fun ω => ∑ j, ∫ p, horizonIncrement active jump rate C x V j T (ω,p)
        ∂countingMeasure j ω) := by
  filter_upwards [ae_testFunction_counting_identity active jump rate V,
    CommonFrozenRegularity.ae_process_zero active jump rate] with ω hω hzero
  have he := hω C x T
  rw [hzero C x] at he
  exact he.trans (Finset.sum_congr rfl (fun j _ =>
    (horizonIntegral_eq_setIntegral active jump rate C x V j T ω _).symm))

/-- Integrability of the test-function change is a consequence of the actual
counting identity and compensation, not an assumed Dynkin hypothesis. -/
theorem integrable_testFunction_change (C : ℝ) (x : E) (V : E → ℝ) (T : ℝ) :
    Integrable (fun ω => V (process active jump rate C x ω T) - V x) (law J) :=
  (integrable_finset_sum Finset.univ (fun j _ =>
    integrable_horizon_countingIntegral active jump rate C x V j T)).congr
      (ae_change_eq_countingIntegral active jump rate C x V T).symm

theorem integrable_testFunction (C : ℝ) (x : E) (V : E → ℝ) (T : ℝ) :
    Integrable (fun ω => V (process active jump rate C x ω T)) (law J) := by
  have h := (integrable_testFunction_change active jump rate C x V T).add
    (integrable_const (V x))
  change Integrable (fun ω => (V (process active jump rate C x ω T) - V x) + V x) (law J) at h
  simpa only [sub_add_cancel] using h

theorem integral_change_eq_intensity (C : ℝ) (x : E) (V : E → ℝ) (T : ℝ) :
    (∫ ω, V (process active jump rate C x ω T) - V x ∂law J) =
      ∑ j, ∫ ω, ∫ p, horizonIncrement active jump rate C x V j T (ω,p)
        ∂positiveVolume.prod positiveVolume ∂law J := by
  rw [integral_congr_ae (ae_change_eq_countingIntegral active jump rate C x V T),
    integral_finset_sum _ (fun j _ => integrable_horizon_countingIntegral active jump rate C x V j T)]
  exact Finset.sum_congr rfl (fun j _ => compensation_horizonIncrement active jump rate C x V j T)

/-- An actual intensity section equals the rate-weighted time drift almost surely. -/
theorem ae_horizon_intensity_eq_timeDrift (C : ℝ) (x : E) (V : E → ℝ) (j : J) (T : ℝ)
    (hq : ∀ y ∈ active, 0 ≤ rate j y) (hbound : ∀ y ∈ active, rate j y ≤ C) :
    (fun ω => ∫ p, horizonIncrement active jump rate C x V j T (ω,p)
      ∂positiveVolume.prod positiveVolume) =ᵐ[law J]
      (fun ω => ∫ s in Ioc 0 T,
        labelDrift active jump rate V j (preState active jump rate C x ω s) ∂positiveVolume) := by
  simp_rw [horizonIncrement_eq_localizedIncrement]
  exact ae_intensityIntegral_eq_timeDrift (law J) active jump rate V j _
    ((measurable_preState active jump rate C x).mono (predictable_le _) le_rfl) T C hq hbound

theorem integrable_timeGenerator (C : ℝ) (x : E) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j, 0 ≤ rate j y)
    (hbound : ∀ y ∈ active, ∀ j, rate j y ≤ C) :
    Integrable (fun ω => ∫ s in Ioc 0 T,
      FrozenProcess.frozenGenerator active jump rate V (preState active jump rate C x ω s)
        ∂positiveVolume) (law J) := by
  have hZ := (measurable_preState active jump rate C x).mono (predictable_le _) le_rfl
  have hi := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_timeDrift (law J) active jump rate V j _ hZ T C
      (fun y hy => hq y hy j) (fun y hy => hbound y hy j))
  exact hi.congr (ae_sum_timeDrift_eq_generator (law J) active jump rate V _ hZ T C hq hbound)

/-- Dynkin's identity for the defined frozen construction and an arbitrary
real test function. Only finite active-set rate nonnegativity and dominance
are required; all stochastic identities and integrability are derived. -/
theorem dynkin_preState (C : ℝ) (x : E) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j, 0 ≤ rate j y)
    (hbound : ∀ y ∈ active, ∀ j, rate j y ≤ C) :
    (∫ ω, V (process active jump rate C x ω T) ∂law J) = V x +
      ∫ ω, ∫ s in Ioc 0 T,
        FrozenProcess.frozenGenerator active jump rate V (preState active jump rate C x ω s)
          ∂positiveVolume ∂law J := by
  have hZ := (measurable_preState active jump rate C x).mono (predictable_le _) le_rfl
  have hchange := integral_change_eq_intensity active jump rate C x V T
  have he : (∑ j, ∫ ω, ∫ p, horizonIncrement active jump rate C x V j T (ω,p)
        ∂positiveVolume.prod positiveVolume ∂law J) =
      ∫ ω, ∫ s in Ioc 0 T,
        FrozenProcess.frozenGenerator active jump rate V (preState active jump rate C x ω s)
          ∂positiveVolume ∂law J := by
    calc
      _ = ∑ j, ∫ ω, ∫ s in Ioc 0 T,
          labelDrift active jump rate V j (preState active jump rate C x ω s)
            ∂positiveVolume ∂law J := by
        apply Finset.sum_congr rfl
        intro j _
        exact integral_congr_ae (ae_horizon_intensity_eq_timeDrift active jump rate C x V j T
          (fun y hy => hq y hy j) (fun y hy => hbound y hy j))
      _ = ∫ ω, ∑ j, ∫ s in Ioc 0 T,
          labelDrift active jump rate V j (preState active jump rate C x ω s)
            ∂positiveVolume ∂law J := by
        symm
        exact integral_finset_sum _ (fun j _ => integrable_timeDrift (law J) active jump rate V j
          _ hZ T C (fun y hy => hq y hy j) (fun y hy => hbound y hy j))
      _ = _ := integral_congr_ae
        (ae_sum_timeDrift_eq_generator (law J) active jump rate V _ hZ T C hq hbound)
  rw [integral_sub (integrable_testFunction active jump rate C x V T) (integrable_const _)] at hchange
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at hchange
  rw [he] at hchange
  linarith

/-- The same time integral written with the actual current state. Actual
proposal times form a time-null set, so no continuity assumption is added. -/
theorem dynkin (C : ℝ) (x : E) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j, 0 ≤ rate j y)
    (hbound : ∀ y ∈ active, ∀ j, rate j y ≤ C) :
    (∫ ω, V (process active jump rate C x ω T) ∂law J) = V x +
      ∫ ω, ∫ s in Ioc 0 T,
        FrozenProcess.frozenGenerator active jump rate V (process active jump rate C x ω s)
          ∂positiveVolume ∂law J := by
  rw [FrozenPreStateTime.integral_setIntegral_comp_eq_preState active jump rate C x
    (FrozenProcess.frozenGenerator active jump rate V) (Ioc 0 T)]
  exact dynkin_preState active jump rate C x V T hq hbound

theorem integrable_current_timeGenerator (C : ℝ) (x : E) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j, 0 ≤ rate j y)
    (hbound : ∀ y ∈ active, ∀ j, rate j y ≤ C) :
    Integrable (fun ω => ∫ s in Ioc 0 T,
      FrozenProcess.frozenGenerator active jump rate V (process active jump rate C x ω s)
        ∂positiveVolume) (law J) := by
  apply (integrable_timeGenerator active jump rate C x V T hq hbound).congr
  filter_upwards [FrozenPreStateTime.ae_setIntegral_comp_eq_preState active jump rate]
    with ω hω
  exact (hω C x (FrozenProcess.frozenGenerator active jump rate V) (Ioc 0 T)).symm

end CarryingCapacity.FrozenDynkin
