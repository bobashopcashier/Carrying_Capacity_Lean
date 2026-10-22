import CarryingCapacity.FiniteSupportGlobal
import CarryingCapacity.FrozenGeneratorIntegral
import CarryingCapacity.FrozenPreStateTime

/-!
# The actual raw configuration drift for finite-support tests

The deterministic finite influence set identifies the global intensity
integrals with the raw empirical configuration generator. Nonexplosion and
common-noise agreement identify global pre-states with current states at
almost every time. Thus the actual current-state generator integral is
integrable over samples and is the compensator of the accepted increments.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal

namespace CarryingCapacity.GlobalFiniteSupportDrift
open ConfigurationLocalization FiniteSupportGeometry FiniteSupportGlobal MarkedIntensity
  FrozenGeneratorIntegral PredictableSets

variable {A : Type*} [MeasurableSpace A] {N D : ℕ}
  {κ : MomentScale} {q : Rates D (MomentLaw κ D)} (control : LyapunovControl κ q)
  (hN : 0 < N) (initial : A → Configuration N D)

/-- The already constructed predictable pre-state of the global configuration. -/
def preState (p : CommonInitialNoise.Sample A (Label N D)) (t : ℝ) : Configuration N D :=
  GlobalLocalizedCountingIdentity.preState (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q hN) initial 0 p t

variable (F : Configuration N D → ℝ) (hF : (Function.support F).Finite)

theorem labelDrift_eq_raw (j : Label N D) (z : Configuration N D) :
    labelDrift (influence F hF) jump (rate κ q hN) F j z =
      rate κ q hN j z * (F (jump j z) - F z) := by
  by_cases hz : z ∈ influence F hF
  · simp only [labelDrift, hz, if_true]
  · simp only [labelDrift, hz, if_false, increment_eq_zero_of_not_mem F hF z hz j, mul_zero]

theorem frozenGenerator_eq_raw (z : Configuration N D) :
    FrozenProcess.frozenGenerator (influence F hF) jump (rate κ q hN) F z =
      generator κ q hN F z := by
  by_cases hz : z ∈ influence F hF
  · simp only [FrozenProcess.frozenGenerator, hz, if_true, generator]
  · simp only [FrozenProcess.frozenGenerator, hz, if_false,
      generator_eq_zero_of_not_mem κ q hN F hF z hz]

variable (μ : Measure A) [IsProbabilityMeasure μ] (hinit : Measurable initial)
include hinit hF

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

/-- A label's actual global intensity integral equals its raw rate-weighted
increment integrated over time, with no influence-set restriction remaining. -/
theorem ae_intensityIntegral_eq_timeLabel (j : Label N D) (T : ℝ) :
    (fun p => ∫ r, integrand control hN initial F j T (p,r) ∂positiveVolume.prod positiveVolume)
      =ᵐ[CommonInitialNoise.law μ (Label N D)]
    (fun p => ∫ s in Ioc 0 T, rate κ q hN j (preState control hN initial p s) *
      (F (jump j (preState control hN initial p s)) - F (preState control hN initial p s))
        ∂positiveVolume) := by
  simp_rw [integrand_eq_localized control hN initial F hF j T]
  have h := ae_intensityIntegral_eq_timeDrift (CommonInitialNoise.law μ (Label N D))
    (influence F hF) jump (rate κ q hN) F j (preState control hN initial)
    ((GlobalLocalizedCountingIdentity.measurable_preState (lyapunov control)
      (finite_sublevel control hN) jump (rate κ q hN) initial 0 hinit).mono (predictable_le _) le_rfl)
    T (rateCap (q := q) hN F hF) (fun z _ => rate_nonnegative κ q hN j z)
    (fun z hz => rate_le_cap hN F hF z hz j)
  simpa only [labelDrift_eq_raw hN F hF, preState] using h

/-- The finite sum of genuine global intensity integrals is the raw
configuration generator integrated at the global pre-state. -/
theorem ae_sum_intensity_eq_timeGenerator_preState (T : ℝ) :
    (fun p => ∑ j : Label N D,
      ∫ r, integrand control hN initial F j T (p,r) ∂positiveVolume.prod positiveVolume)
      =ᵐ[CommonInitialNoise.law μ (Label N D)]
    (fun p => ∫ s in Ioc 0 T, generator κ q hN F (preState control hN initial p s)
      ∂positiveVolume) := by
  have hZ := (GlobalLocalizedCountingIdentity.measurable_preState (lyapunov control)
    (finite_sublevel control hN) jump (rate κ q hN) initial 0 hinit).mono (predictable_le _) le_rfl
  have heach := ae_all_iff.mpr (fun j : Label N D =>
    ae_intensityIntegral_eq_timeDrift (CommonInitialNoise.law μ (Label N D))
      (influence F hF) jump (rate κ q hN) F j (preState control hN initial) hZ T
      (rateCap (q := q) hN F hF) (fun z _ => rate_nonnegative κ q hN j z)
      (fun z hz => rate_le_cap hN F hF z hz j))
  have hsum := ae_sum_timeDrift_eq_generator (CommonInitialNoise.law μ (Label N D))
    (influence F hF) jump (rate κ q hN) F (preState control hN initial) hZ T
    (rateCap (q := q) hN F hF) (fun z _ j => rate_nonnegative κ q hN j z)
    (fun z hz j => rate_le_cap hN F hF z hz j)
  filter_upwards [heach, hsum] with p he hs
  calc
    _ = ∑ j : Label N D, ∫ s in Ioc 0 T,
        labelDrift (influence F hF) jump (rate κ q hN) F j (preState control hN initial p s)
          ∂positiveVolume := by
      apply Finset.sum_congr rfl
      intro j _
      simpa only [integrand_eq_localized control hN initial F hF j T, preState] using he j
    _ = _ := by
      rw [hs]
      simp only [frozenGenerator_eq_raw hN F hF]

/-- The actual time-integrated raw generator at the pre-state is integrable
under the full initial-record/noise law. -/
theorem integrable_timeGenerator_preState (T : ℝ) :
    Integrable (fun p => ∫ s in Ioc 0 T,
      generator κ q hN F (preState control hN initial p s) ∂positiveVolume)
      (CommonInitialNoise.law μ (Label N D)) :=
  (integrable_finset_sum Finset.univ (fun j _ =>
    (integrable_horizonIncrement control hN initial F hF μ hinit j T).integral_prod_left)).congr
      (ae_sum_intensity_eq_timeGenerator_preState control hN initial F hF μ hinit T)

omit hF hinit [IsProbabilityMeasure μ] in
/-- On one sample event, the actual global pre-state and current state agree
at almost every positive-Lebesgue time. Only countably many levels are combined. -/
theorem ae_preState_eq_process_time_of_exhaustion
    (hexhaust : ∀ᵐ p ∂CommonInitialNoise.law μ (Label N D), ∀ T : ℝ≥0, ∃ n : ℕ,
      (T : ℝ≥0∞) < ConfigurationLocalization.exit control hN initial n p) :
    ∀ᵐ p ∂CommonInitialNoise.law μ (Label N D),
      (preState control hN initial p) =ᵐ[positiveVolume]
        (ConfigurationNonexplosion.process control hN initial p) := by
  have hl := ae_all_iff.mpr (fun n : ℕ =>
    FrozenPreStateTime.ae_initial_process_eq_preState_time
      (ConfigurationLocalization.active control hN n) jump (rate κ q hN) initial μ)
  filter_upwards [hl,
    GlobalLocalizedCountingIdentity.ae_preState_eq_level (lyapunov control)
      (finite_sublevel control hN) jump (rate κ q hN) initial 0 μ,
    GlobalLocalizedProcess.ae_eq_path (lyapunov control) (finite_sublevel control hN)
      jump (rate κ q hN) initial 0 μ,
    hexhaust]
      with p hl he hg hx
  have htall := ae_all_iff.mpr (fun n : ℕ => hl n (ConfigurationLocalization.rateBound control hN n) 0)
  filter_upwards [htall, FrozenPreStateTime.ae_time_pos] with t ht htpos
  obtain ⟨n, hn⟩ := hx ⟨t, htpos.le⟩
  calc
    preState control hN initial p t =
        InitialFrozenPredictable.preState (ConfigurationLocalization.active control hN n)
          jump (rate κ q hN) initial (ConfigurationLocalization.rateBound control hN n) 0 p t :=
      (he n ⟨t, htpos.le⟩ hn t ⟨htpos, le_rfl⟩).1
    _ = ConfigurationLocalization.path control hN initial n p t := (ht n).symm
    _ = ConfigurationNonexplosion.process control hN initial p t :=
      (hg n t htpos.le (by simpa only [ConfigurationLocalization.exit, ← ENNReal.ofReal_coe_nnreal] using hn.le)).symm

omit hF in
/-- The initial Lyapunov moment supplies the exhaustion in the time-null identity. -/
theorem ae_preState_eq_process_time
    (hV : Integrable (fun a => lyapunov control (initial a)) μ) :
    ∀ᵐ p ∂CommonInitialNoise.law μ (Label N D),
      (preState control hN initial p) =ᵐ[positiveVolume]
        (ConfigurationNonexplosion.process control hN initial p) :=
  ae_preState_eq_process_time_of_exhaustion control hN initial μ
    (ConfigurationNonexplosion.ae_exhaustive control hN initial μ hinit hV)

/-- The same actual intensity integral is the generator evaluated at the
current state at time s, rather than only a predictable representative. -/
theorem ae_sum_intensity_eq_timeGenerator_of_exhaustion
    (hexhaust : ∀ᵐ p ∂CommonInitialNoise.law μ (Label N D), ∀ T : ℝ≥0, ∃ n : ℕ,
      (T : ℝ≥0∞) < ConfigurationLocalization.exit control hN initial n p) (T : ℝ) :
    (fun p => ∑ j : Label N D,
      ∫ r, integrand control hN initial F j T (p,r) ∂positiveVolume.prod positiveVolume)
      =ᵐ[CommonInitialNoise.law μ (Label N D)]
    (fun p => ∫ s in Ioc 0 T, generator κ q hN F
      (ConfigurationNonexplosion.process control hN initial p s) ∂positiveVolume) := by
  filter_upwards [ae_sum_intensity_eq_timeGenerator_preState control hN initial F hF μ hinit T,
    ae_preState_eq_process_time_of_exhaustion control hN initial μ hexhaust] with p hi he
  rw [hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae he] with t ht
  exact congrArg (generator κ q hN F) ht

/-- The moment hypothesis discharges actual exhaustion in the generator identity. -/
theorem ae_sum_intensity_eq_timeGenerator
    (hV : Integrable (fun a => lyapunov control (initial a)) μ) (T : ℝ) :
    (fun p => ∑ j : Label N D,
      ∫ r, integrand control hN initial F j T (p,r) ∂positiveVolume.prod positiveVolume)
      =ᵐ[CommonInitialNoise.law μ (Label N D)]
    (fun p => ∫ s in Ioc 0 T, generator κ q hN F
      (ConfigurationNonexplosion.process control hN initial p s) ∂positiveVolume) :=
  ae_sum_intensity_eq_timeGenerator_of_exhaustion control hN initial F hF μ hinit
    (ConfigurationNonexplosion.ae_exhaustive control hN initial μ hinit hV) T

/-- The actual current-state drift integral is integrable; no expected global
jump-activity bound or generator-integrability premise is imposed. -/
theorem integrable_timeGenerator
    (hV : Integrable (fun a => lyapunov control (initial a)) μ) (T : ℝ) :
    Integrable (fun p => ∫ s in Ioc 0 T, generator κ q hN F
      (ConfigurationNonexplosion.process control hN initial p s) ∂positiveVolume)
      (CommonInitialNoise.law μ (Label N D)) :=
  (integrable_finset_sum Finset.univ (fun j _ =>
    (integrable_horizonIncrement control hN initial F hF μ hinit j T).integral_prod_left)).congr
      (ae_sum_intensity_eq_timeGenerator control hN initial F hF μ hinit hV T)

end CarryingCapacity.GlobalFiniteSupportDrift
