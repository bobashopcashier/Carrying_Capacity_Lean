import CarryingCapacity.TimeDependentInitialCounting
import CarryingCapacity.TimeDependentGeneratorIntegral
import CarryingCapacity.TimeDependentPreStateTime

/-!
# Dynkin's identity for time-dependent randomly initialized frozen paths

The change in an arbitrary real test function is integrable without an
initial moment assumption: the finite active region controls every accepted
increment. The actual counting identity, compensation, and height integration
then give Dynkin's change-expectation identity. The usual separate-expectation
form requires only integrability of the test function of the initial record.
Rate nonnegativity and upper bounds are imposed only on the finite horizon.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace CarryingCapacity.TimeDependentDynkin
open CommonInitialNoise MarkedIntensity TimeDependentInitial TimeDependentInitialCompensation
  TimeDependentInitialCounting TimeDependentGeneratorIntegral PredictableSets

variable {A J E : Type*} [MeasurableSpace A] [Fintype J] [DecidableEq E]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ) (initial : A → E)

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
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ) :
    Integrable (fun p => V (process active jump rate initial C p T) - V (initial p.1))
      (law μ J) :=
  (integrable_finset_sum Finset.univ (fun j _ =>
    integrable_horizon_countingIntegral active jump rate initial μ hRate hinit C e V j T)).congr
      (ae_change_eq_countingIntegral active jump rate initial μ C e V T).symm

theorem integral_change_eq_intensity (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ) :
    (∫ p, V (process active jump rate initial C p T) - V (initial p.1) ∂law μ J) =
      ∑ j, ∫ p, ∫ q, horizonIncrement active jump rate initial C e V j T (p, q)
        ∂positiveVolume.prod positiveVolume ∂law μ J := by
  rw [integral_congr_ae (ae_change_eq_countingIntegral active jump rate initial μ C e V T),
    integral_finset_sum _ (fun j _ =>
      integrable_horizon_countingIntegral active jump rate initial μ hRate hinit C e V j T)]
  exact Finset.sum_congr rfl (fun j _ =>
    compensation_horizonIncrement active jump rate initial μ hRate hinit C e V j T)

theorem ae_horizon_intensity_eq_timeDrift (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (j : J) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ s ∈ Ioc 0 T, 0 ≤ rate j s y)
    (hbound : ∀ y ∈ active, ∀ s ∈ Ioc 0 T, rate j s y ≤ C) :
    (fun p => ∫ q, horizonIncrement active jump rate initial C e V j T (p, q)
      ∂positiveVolume.prod positiveVolume) =ᵐ[law μ J]
      (fun p => ∫ s in Ioc 0 T,
        labelDrift active jump rate V j s (preState active jump rate initial C e p s)
          ∂positiveVolume) := by
  simp_rw [horizonIncrement_eq_localizedIncrement]
  exact ae_intensityIntegral_eq_timeDrift (law μ J) active jump rate hRate V j _
    ((measurable_preState active jump rate initial hRate hinit C e).mono (predictable_le _) le_rfl)
      T C hq hbound

theorem integrable_timeGenerator_preState (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j s, s ∈ Ioc 0 T → 0 ≤ rate j s y)
    (hbound : ∀ y ∈ active, ∀ j s, s ∈ Ioc 0 T → rate j s y ≤ C) :
    Integrable (fun p => ∫ s in Ioc 0 T,
      frozenGenerator active jump rate V s (preState active jump rate initial C e p s)
        ∂positiveVolume) (law μ J) := by
  have hZ := (measurable_preState active jump rate initial hRate hinit C e).mono (predictable_le _) le_rfl
  have hi := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_timeDrift (law μ J) active jump rate hRate V j _ hZ T C
      (fun y hy s hs => hq y hy j s hs) (fun y hy s hs => hbound y hy j s hs))
  exact hi.congr
    (ae_sum_timeDrift_eq_generator (law μ J) active jump rate hRate V _ hZ T C hq hbound)

/-- The generator is identified inside the expectation from the actual
accepted increments and the proved predictable compensation theorem. -/
theorem dynkin_change_preState (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j s, s ∈ Ioc 0 T → 0 ≤ rate j s y)
    (hbound : ∀ y ∈ active, ∀ j s, s ∈ Ioc 0 T → rate j s y ≤ C) :
    (∫ p, V (process active jump rate initial C p T) - V (initial p.1) ∂law μ J) =
      ∫ p, ∫ s in Ioc 0 T,
        frozenGenerator active jump rate V s (preState active jump rate initial C e p s)
          ∂positiveVolume ∂law μ J := by
  have hZ := (measurable_preState active jump rate initial hRate hinit C e).mono (predictable_le _) le_rfl
  rw [integral_change_eq_intensity active jump rate initial μ hRate hinit C e V T]
  calc
    _ = ∑ j, ∫ p, ∫ s in Ioc 0 T,
        labelDrift active jump rate V j s (preState active jump rate initial C e p s)
          ∂positiveVolume ∂law μ J := by
      apply Finset.sum_congr rfl
      intro j _
      exact integral_congr_ae (ae_horizon_intensity_eq_timeDrift active jump rate initial
        μ hRate hinit C e V j T (fun y hy s hs => hq y hy j s hs) (fun y hy s hs => hbound y hy j s hs))
    _ = ∫ p, ∑ j, ∫ s in Ioc 0 T,
        labelDrift active jump rate V j s (preState active jump rate initial C e p s)
          ∂positiveVolume ∂law μ J := by
      symm
      exact integral_finset_sum _ (fun j _ => integrable_timeDrift (law μ J)
        active jump rate hRate V j _ hZ T C (fun y hy s hs => hq y hy j s hs) (fun y hy s hs => hbound y hy j s hs))
    _ = _ := integral_congr_ae
      (ae_sum_timeDrift_eq_generator (law μ J) active jump rate hRate V _ hZ T C hq hbound)

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
/-- The common noise event works at the sampled initial state and every
fallback in the actual product-space predictable construction. -/
theorem ae_initial_process_eq_preState_time (μ : Measure A) :
    ∀ᵐ p ∂law μ J, ∀ C e,
      (process active jump rate initial C p) =ᵐ[positiveVolume]
        (preState active jump rate initial C e p) := by
  filter_upwards [CommonInitialNoise.ae_noise μ
      (TimeDependentPreStateTime.ae_process_eq_preState_time active jump rate),
    TimeDependentInitial.ae_preState_eq_base active jump rate initial μ] with p hp he
  intro C e
  filter_upwards [hp C (initial p.1), FrozenPreStateTime.ae_time_pos] with t ht hpos
  exact ht.trans (he C e t hpos).symm

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
/-- Time-dependent integrands agree in all restricted time integrals. -/
theorem ae_initial_setIntegral_comp_eq_preState (μ : Measure A) :
    ∀ᵐ p ∂law μ J, ∀ C e (G : ℝ → E → ℝ) (B : Set ℝ),
      (∫ t in B, G t (process active jump rate initial C p t) ∂positiveVolume) =
      ∫ t in B, G t (preState active jump rate initial C e p t) ∂positiveVolume := by
  filter_upwards [ae_initial_process_eq_preState_time active jump rate initial μ] with p hp
  intro C e G B
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (hp C e)] with t ht
  exact congrArg (G t) ht

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] [BorelSpace E] in
theorem ae_timeGenerator_eq_preState (μ : Measure A)
    (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ) :
    (fun p => ∫ s in Ioc 0 T,
      frozenGenerator active jump rate V s (process active jump rate initial C p s)
        ∂positiveVolume) =ᵐ[law μ J]
    (fun p => ∫ s in Ioc 0 T,
      frozenGenerator active jump rate V s (preState active jump rate initial C e p s)
        ∂positiveVolume) := by
  filter_upwards [ae_initial_setIntegral_comp_eq_preState
    active jump rate initial μ] with p hp
  exact hp C e (frozenGenerator active jump rate V) (Ioc 0 T)

/-- The sum of actual intensity sections is the actual current-state frozen
generator compensator, sample by sample outside one null event. -/
theorem ae_sum_horizon_intensity_eq_timeGenerator (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j s, s ∈ Ioc 0 T → 0 ≤ rate j s y)
    (hbound : ∀ y ∈ active, ∀ j s, s ∈ Ioc 0 T → rate j s y ≤ C) :
    (fun p => ∑ j, ∫ q, horizonIncrement active jump rate initial C e V j T (p,q)
      ∂positiveVolume.prod positiveVolume) =ᵐ[law μ J]
    (fun p => ∫ s in Ioc 0 T,
      frozenGenerator active jump rate V s (process active jump rate initial C p s)
        ∂positiveVolume) := by
  have hZ := (measurable_preState active jump rate initial hRate hinit C e).mono
    (predictable_le _) le_rfl
  have he := ae_all_iff.mpr (fun j =>
    ae_horizon_intensity_eq_timeDrift active jump rate initial μ hRate hinit C e V j T
      (fun y hy s hs => hq y hy j s hs) (fun y hy s hs => hbound y hy j s hs))
  filter_upwards [he,
    ae_sum_timeDrift_eq_generator (law μ J) active jump rate hRate V _ hZ T C hq hbound,
    ae_timeGenerator_eq_preState active jump rate initial μ C e V T] with p hp hs hc
  exact (Finset.sum_congr rfl (fun j _ => hp j)).trans (hs.trans hc.symm)

/-- The actual current-state generator integral is integrable, not just its
predictable pre-state representative. -/
theorem integrable_timeGenerator (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j s, s ∈ Ioc 0 T → 0 ≤ rate j s y)
    (hbound : ∀ y ∈ active, ∀ j s, s ∈ Ioc 0 T → rate j s y ≤ C) :
    Integrable (fun p => ∫ s in Ioc 0 T,
      frozenGenerator active jump rate V s (process active jump rate initial C p s)
        ∂positiveVolume) (law μ J) :=
  (integrable_timeGenerator_preState active jump rate initial μ hRate hinit C e V T hq hbound).congr
    (ae_timeGenerator_eq_preState active jump rate initial μ C e V T).symm

/-- Dynkin's change identity has no initial test-function integrability
premise. The integrand uses the actual state at time s. -/
theorem dynkin_change (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j s, s ∈ Ioc 0 T → 0 ≤ rate j s y)
    (hbound : ∀ y ∈ active, ∀ j s, s ∈ Ioc 0 T → rate j s y ≤ C) :
    (∫ p, V (process active jump rate initial C p T) - V (initial p.1) ∂law μ J) =
      ∫ p, ∫ s in Ioc 0 T,
        frozenGenerator active jump rate V s (process active jump rate initial C p s)
          ∂positiveVolume ∂law μ J := by
  rw [integral_congr_ae (ae_timeGenerator_eq_preState active jump rate initial μ C e V T)]
  exact dynkin_change_preState active jump rate initial μ hRate hinit C e V T hq hbound

/-- The exact X(0) version also follows from the proved initial-value identity. -/
theorem dynkin_process_change (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j s, s ∈ Ioc 0 T → 0 ≤ rate j s y)
    (hbound : ∀ y ∈ active, ∀ j s, s ∈ Ioc 0 T → rate j s y ≤ C) :
    (∫ p, V (process active jump rate initial C p T) -
      V (process active jump rate initial C p 0) ∂law μ J) =
      ∫ p, ∫ s in Ioc 0 T,
        frozenGenerator active jump rate V s (process active jump rate initial C p s)
          ∂positiveVolume ∂law μ J := by
  calc
    _ = ∫ p, V (process active jump rate initial C p T) - V (initial p.1) ∂law μ J := by
      apply integral_congr_ae
      filter_upwards [ae_process_zero active jump rate initial μ] with p hp
      rw [hp C]
    _ = _ := dynkin_change active jump rate initial μ hRate hinit C e V T hq hbound

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
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ)
    (hV : Integrable (fun a => V (initial a)) μ) :
    Integrable (fun p => V (process active jump rate initial C p T)) (law μ J) := by
  have h := (integrable_testFunction_change active jump rate initial μ hRate hinit C e V T).add
    (integrable_initial_testFunction initial μ V hV)
  exact h.congr (Filter.Eventually.of_forall (fun p => sub_add_cancel _ _))

/-- The usual separate-expectation Dynkin formula requires exactly the
integrability of the initial test value; future integrability is proved. -/
theorem dynkin (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j s, s ∈ Ioc 0 T → 0 ≤ rate j s y)
    (hbound : ∀ y ∈ active, ∀ j s, s ∈ Ioc 0 T → rate j s y ≤ C)
    (hV : Integrable (fun a => V (initial a)) μ) :
    (∫ p, V (process active jump rate initial C p T) ∂law μ J) =
      (∫ a, V (initial a) ∂μ) +
      ∫ p, ∫ s in Ioc 0 T,
        frozenGenerator active jump rate V s (process active jump rate initial C p s)
          ∂positiveVolume ∂law μ J := by
  have hchange := dynkin_change active jump rate initial μ hRate hinit C e V T hq hbound
  rw [integral_sub (integrable_testFunction active jump rate initial μ hRate hinit C e V T hV)
    (integrable_initial_testFunction initial μ V hV)] at hchange
  have he : (∫ p : Sample A J, V (initial p.1) ∂law μ J) = ∫ a, V (initial a) ∂μ := by
    simpa only [measureReal_univ_eq_one, one_smul] using
      (integral_fun_fst (μ := μ) (ν := MarkedNoise.law J) (fun a => V (initial a)))
  rw [he] at hchange
  linarith

/-- The positive-time measure agrees with ordinary Lebesgue measure after
restriction to the integrated horizon. -/
theorem positiveVolume_restrict_Ioc_zero (T : ℝ) :
    positiveVolume.restrict (Ioc 0 T) = volume.restrict (Ioc 0 T) := by
  rw [positiveVolume, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (fun _ hx => hx.1.le)]

omit [TopologicalSpace E] [PolishSpace E] [BorelSpace E] in
/-- Fubini for the actual time-dependent generator, with product integrability
derived from the active-set rate cap on this finite horizon. -/
theorem integral_timeGenerator_swap (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j s, s ∈ Ioc 0 T → 0 ≤ rate j s y)
    (hbound : ∀ y ∈ active, ∀ j s, s ∈ Ioc 0 T → rate j s y ≤ C) :
    (∫ p, ∫ s in Ioc 0 T,
      frozenGenerator active jump rate V s (process active jump rate initial C p s)
        ∂positiveVolume ∂law μ J) =
      ∫ s in Ioc 0 T, ∫ p,
        frozenGenerator active jump rate V s (process active jump rate initial C p s) ∂law μ J := by
  simp_rw [positiveVolume_restrict_Ioc_zero]
  exact integral_integral_swap
    (integrable_generatorField (law μ J) active jump rate hRate V _
      (measurable_process active jump rate initial hRate hinit C) T C hq hbound)

/-- The usual expectation primitive for the actual frozen construction.
The inner generator expectation and its time integral are obtained by Fubini;
no expected-drift or Dynkin identity is an input hypothesis. -/
theorem dynkin_expectation_integral (μ : Measure A) [IsProbabilityMeasure μ]
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e : E) (V : E → ℝ) (T : ℝ)
    (hq : ∀ y ∈ active, ∀ j s, s ∈ Ioc 0 T → 0 ≤ rate j s y)
    (hbound : ∀ y ∈ active, ∀ j s, s ∈ Ioc 0 T → rate j s y ≤ C)
    (hV : Integrable (fun a => V (initial a)) μ) :
    (∫ p, V (process active jump rate initial C p T) ∂law μ J) =
      (∫ a, V (initial a) ∂μ) + ∫ s in Ioc 0 T, ∫ p,
        frozenGenerator active jump rate V s (process active jump rate initial C p s) ∂law μ J := by
  rw [dynkin active jump rate initial μ hRate hinit C e V T hq hbound hV,
    integral_timeGenerator_swap active jump rate initial μ hRate hinit C V T hq hbound]

end CarryingCapacity.TimeDependentDynkin
