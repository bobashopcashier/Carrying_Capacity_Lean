import CarryingCapacity.InitialFrozenCountingIdentity
import CarryingCapacity.FrozenGeneratorIntegral
import CarryingCapacity.FrozenPreStateTime

/-!
# Dynkin's identity for the actual randomly initialized frozen process

The change in an arbitrary real test function is integrable without an
initial moment assumption: the finite active region controls every accepted
increment. The actual counting identity, compensation, and height integration
then give Dynkin's change-expectation identity. The usual separate-expectation
form requires only integrability of the test function of the initial record.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace CarryingCapacity.InitialFrozenDynkin
open CommonInitialNoise MarkedIntensity InitialFrozenPredictable InitialFrozenCompensation
  InitialFrozenCountingIdentity FrozenGeneratorIntegral PredictableSets

variable {A J E : Type*} [MeasurableSpace A] [Fintype J] [DecidableEq E]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ) (initial : A → E)

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
theorem ae_change_eq_countingIntegral (μ : Measure A)
    (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ) :
    (fun p => V (process active jump rate initial C p T) - V (initial p.1)) =ᵐ[law μ J]
      (fun p => ∑ j, ∫ q, horizonIncrement active jump rate initial C e V j T (p, q)
        ∂MarkedNoise.countingMeasure j p.2) := by
  filter_upwards [ae_testFunction_counting_identity active jump rate initial μ V,
    ae_process_zero active jump rate initial μ] with p hp hzero
  simpa only [hzero C] using hp C e T

/-- Frozen changes are integrable for an arbitrary initial probability law,
even when the initial test function itself has infinite expectation. -/
theorem integrable_testFunction_change (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ) :
    Integrable (fun p => V (process active jump rate initial C p T) - V (initial p.1))
      (law μ J) :=
  (integrable_finset_sum Finset.univ (fun j _ =>
    integrable_horizon_countingIntegral active jump rate initial μ hinit C e V j T)).congr
      (ae_change_eq_countingIntegral active jump rate initial μ C e V T).symm

theorem integral_change_eq_intensity (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ) :
    (∫ p, V (process active jump rate initial C p T) - V (initial p.1) ∂law μ J) =
      ∑ j, ∫ p, ∫ q, horizonIncrement active jump rate initial C e V j T (p, q)
        ∂positiveVolume.prod positiveVolume ∂law μ J := by
  rw [integral_congr_ae (ae_change_eq_countingIntegral active jump rate initial μ C e V T),
    integral_finset_sum _ (fun j _ =>
      integrable_horizon_countingIntegral active jump rate initial μ hinit C e V j T)]
  exact Finset.sum_congr rfl (fun j _ =>
    compensation_horizonIncrement active jump rate initial μ hinit C e V j T)

theorem ae_horizon_intensity_eq_timeDrift (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (j : J) (T : ℝ)
    (hq : ∀ y ∈ active, 0 ≤ rate j y) (hbound : ∀ y ∈ active, rate j y ≤ C) :
    (fun p => ∫ q, horizonIncrement active jump rate initial C e V j T (p, q)
      ∂positiveVolume.prod positiveVolume) =ᵐ[law μ J]
      (fun p => ∫ s in Ioc 0 T,
        labelDrift active jump rate V j (preState active jump rate initial C e p s)
          ∂positiveVolume) := by
  simp_rw [horizonIncrement_eq_localizedIncrement]
  exact ae_intensityIntegral_eq_timeDrift (law μ J) active jump rate V j _
    ((measurable_preState active jump rate initial hinit C e).mono (predictable_le _) le_rfl)
      T C hq hbound

theorem integrable_timeGenerator_preState (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j, 0 ≤ rate j y)
    (hbound : ∀ y ∈ active, ∀ j, rate j y ≤ C) :
    Integrable (fun p => ∫ s in Ioc 0 T,
      FrozenProcess.frozenGenerator active jump rate V (preState active jump rate initial C e p s)
        ∂positiveVolume) (law μ J) := by
  have hZ := (measurable_preState active jump rate initial hinit C e).mono (predictable_le _) le_rfl
  have hi := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_timeDrift (law μ J) active jump rate V j _ hZ T C
      (fun y hy => hq y hy j) (fun y hy => hbound y hy j))
  exact hi.congr
    (ae_sum_timeDrift_eq_generator (law μ J) active jump rate V _ hZ T C hq hbound)

/-- The generator is identified inside the expectation from the actual
accepted increments and the proved predictable compensation theorem. -/
theorem dynkin_change_preState (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j, 0 ≤ rate j y)
    (hbound : ∀ y ∈ active, ∀ j, rate j y ≤ C) :
    (∫ p, V (process active jump rate initial C p T) - V (initial p.1) ∂law μ J) =
      ∫ p, ∫ s in Ioc 0 T,
        FrozenProcess.frozenGenerator active jump rate V (preState active jump rate initial C e p s)
          ∂positiveVolume ∂law μ J := by
  have hZ := (measurable_preState active jump rate initial hinit C e).mono (predictable_le _) le_rfl
  rw [integral_change_eq_intensity active jump rate initial μ hinit C e V T]
  calc
    _ = ∑ j, ∫ p, ∫ s in Ioc 0 T,
        labelDrift active jump rate V j (preState active jump rate initial C e p s)
          ∂positiveVolume ∂law μ J := by
      apply Finset.sum_congr rfl
      intro j _
      exact integral_congr_ae (ae_horizon_intensity_eq_timeDrift active jump rate initial
        μ hinit C e V j T (fun y hy => hq y hy j) (fun y hy => hbound y hy j))
    _ = ∫ p, ∑ j, ∫ s in Ioc 0 T,
        labelDrift active jump rate V j (preState active jump rate initial C e p s)
          ∂positiveVolume ∂law μ J := by
      symm
      exact integral_finset_sum _ (fun j _ => integrable_timeDrift (law μ J)
        active jump rate V j _ hZ T C (fun y hy => hq y hy j) (fun y hy => hbound y hy j))
    _ = _ := integral_congr_ae
      (ae_sum_timeDrift_eq_generator (law μ J) active jump rate V _ hZ T C hq hbound)

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
theorem ae_timeGenerator_eq_preState (μ : Measure A)
    (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ) :
    (fun p => ∫ s in Ioc 0 T,
      FrozenProcess.frozenGenerator active jump rate V (process active jump rate initial C p s)
        ∂positiveVolume) =ᵐ[law μ J]
    (fun p => ∫ s in Ioc 0 T,
      FrozenProcess.frozenGenerator active jump rate V (preState active jump rate initial C e p s)
        ∂positiveVolume) := by
  filter_upwards [FrozenPreStateTime.ae_initial_setIntegral_comp_eq_preState
    active jump rate initial μ] with p hp
  exact hp C e (FrozenProcess.frozenGenerator active jump rate V) (Ioc 0 T)

/-- The actual current-state generator integral is integrable, not just its
predictable pre-state representative. -/
theorem integrable_timeGenerator (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j, 0 ≤ rate j y)
    (hbound : ∀ y ∈ active, ∀ j, rate j y ≤ C) :
    Integrable (fun p => ∫ s in Ioc 0 T,
      FrozenProcess.frozenGenerator active jump rate V (process active jump rate initial C p s)
        ∂positiveVolume) (law μ J) :=
  (integrable_timeGenerator_preState active jump rate initial μ hinit C e V T hq hbound).congr
    (ae_timeGenerator_eq_preState active jump rate initial μ C e V T).symm

/-- Dynkin's change identity has no initial test-function integrability
premise. The integrand uses the actual state at time s. -/
theorem dynkin_change (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j, 0 ≤ rate j y)
    (hbound : ∀ y ∈ active, ∀ j, rate j y ≤ C) :
    (∫ p, V (process active jump rate initial C p T) - V (initial p.1) ∂law μ J) =
      ∫ p, ∫ s in Ioc 0 T,
        FrozenProcess.frozenGenerator active jump rate V (process active jump rate initial C p s)
          ∂positiveVolume ∂law μ J := by
  rw [integral_congr_ae (ae_timeGenerator_eq_preState active jump rate initial μ C e V T)]
  exact dynkin_change_preState active jump rate initial μ hinit C e V T hq hbound

/-- The exact X(0) version also follows from the proved initial-value identity. -/
theorem dynkin_process_change (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j, 0 ≤ rate j y)
    (hbound : ∀ y ∈ active, ∀ j, rate j y ≤ C) :
    (∫ p, V (process active jump rate initial C p T) -
      V (process active jump rate initial C p 0) ∂law μ J) =
      ∫ p, ∫ s in Ioc 0 T,
        FrozenProcess.frozenGenerator active jump rate V (process active jump rate initial C p s)
          ∂positiveVolume ∂law μ J := by
  calc
    _ = ∫ p, V (process active jump rate initial C p T) - V (initial p.1) ∂law μ J := by
      apply integral_congr_ae
      filter_upwards [ae_process_zero active jump rate initial μ] with p hp
      rw [hp C]
    _ = _ := dynkin_change active jump rate initial μ hinit C e V T hq hbound

omit [Fintype J] [DecidableEq E] [Countable E] [MeasurableSpace E]
  [MeasurableSingletonClass E] [TopologicalSpace E] [PolishSpace E] [BorelSpace E] in
theorem integrable_initial_testFunction (μ : Measure A) [IsProbabilityMeasure μ]
    (V : E → ℝ) (hV : Integrable (fun a => V (initial a)) μ) :
    Integrable (fun p : Sample A J => V (initial p.1)) (law μ J) := by
  have hm : Integrable (fun a => V (initial a)) ((law μ J).map Prod.fst) := by
    rw [map_initial]
    exact hV
  exact hm.comp_measurable measurable_fst

theorem integrable_testFunction (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ)
    (hV : Integrable (fun a => V (initial a)) μ) :
    Integrable (fun p => V (process active jump rate initial C p T)) (law μ J) := by
  have h := (integrable_testFunction_change active jump rate initial μ hinit C e V T).add
    (integrable_initial_testFunction initial μ V hV)
  exact h.congr (Filter.Eventually.of_forall (fun p => sub_add_cancel _ _))

/-- The usual separate-expectation Dynkin formula requires exactly the
integrability of the initial test value; future integrability is proved. -/
theorem dynkin (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j, 0 ≤ rate j y)
    (hbound : ∀ y ∈ active, ∀ j, rate j y ≤ C)
    (hV : Integrable (fun a => V (initial a)) μ) :
    (∫ p, V (process active jump rate initial C p T) ∂law μ J) =
      (∫ a, V (initial a) ∂μ) +
      ∫ p, ∫ s in Ioc 0 T,
        FrozenProcess.frozenGenerator active jump rate V (process active jump rate initial C p s)
          ∂positiveVolume ∂law μ J := by
  have hchange := dynkin_change active jump rate initial μ hinit C e V T hq hbound
  rw [integral_sub (integrable_testFunction active jump rate initial μ hinit C e V T hV)
    (integrable_initial_testFunction initial μ V hV)] at hchange
  have he : (∫ p : Sample A J, V (initial p.1) ∂law μ J) = ∫ a, V (initial a) ∂μ := by
    simpa only [measureReal_univ_eq_one, one_smul] using
      (integral_fun_fst (μ := μ) (ν := MarkedNoise.law J) (fun a => V (initial a)))
  rw [he] at hchange
  linarith

end CarryingCapacity.InitialFrozenDynkin
