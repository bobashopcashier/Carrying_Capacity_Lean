import CarryingCapacity.TimeDependentIntensity

/-!
# Integrating time-dependent frozen acceptance against intensity

The height cutoff disappears when it dominates the rates on the active set.
Bochner Fubini then identifies the finite-horizon intensity integral with
the time integral of the rate-weighted test-function increment. Nonnegativity
and bounds are required only during the integrated horizon.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace CarryingCapacity.TimeDependentGeneratorIntegral
open MarkedIntensity TimeDependentIntensity

variable {Ω E J : Type*} [DecidableEq E]

/-- The contribution of one jump label to the frozen generator. -/
def labelDrift (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)
    (V : E → ℝ) (j : J) (t : ℝ) (x : E) : ℝ :=
  if x ∈ active then rate j t x * (V (jump j x) - V x) else 0

/-- The genuine frozen generator at a deterministic time. -/
def frozenGenerator [Fintype J] (active : Finset E) (jump : J → E → E)
    (rate : J → ℝ → E → ℝ) (V : E → ℝ) (t : ℝ) (x : E) : ℝ :=
  FrozenProcess.frozenGenerator active jump (fun j => rate j t) V x

/-- A deterministic generator bound from the active set and a rate cap. -/
def generatorBound [Fintype J] (active : Finset E) (jump : J → E → E)
    (V : E → ℝ) (C : ℝ) : ℝ :=
  max C 0 * ∑ j, FrozenIntensity.incrementBound active jump V j

omit [DecidableEq E] in
theorem generatorBound_nonneg [Fintype J] (active : Finset E) (jump : J → E → E)
    (V : E → ℝ) (C : ℝ) : 0 ≤ generatorBound active jump V C := by
  exact mul_nonneg (le_max_right _ _)
    (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)))

/-- No bound on the inactive states or on other times is needed. -/
theorem norm_frozenGenerator_le [Fintype J] (active : Finset E) (jump : J → E → E)
    (rate : J → ℝ → E → ℝ) (V : E → ℝ) (C t : ℝ)
    (hq : ∀ x ∈ active, ∀ j, 0 ≤ rate j t x)
    (hbound : ∀ x ∈ active, ∀ j, rate j t x ≤ C) (x : E) :
    ‖frozenGenerator active jump rate V t x‖ ≤ generatorBound active jump V C := by
  by_cases hx : x ∈ active
  · simp only [frozenGenerator, FrozenProcess.frozenGenerator, if_pos hx]
    calc
      _ ≤ ∑ j, ‖rate j t x * (V (jump j x) - V x)‖ := norm_sum_le _ _
      _ ≤ ∑ j, max C 0 * FrozenIntensity.incrementBound active jump V j := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hq x hx j), Real.norm_eq_abs]
        exact mul_le_mul ((hbound x hx j).trans (le_max_left _ _))
          (Finset.single_le_sum (fun y _ => abs_nonneg (V (jump j y) - V y)) hx)
          (abs_nonneg _) (le_max_right _ _)
      _ = _ := (Finset.mul_sum _ _ _).symm
  · simpa only [frozenGenerator, FrozenProcess.frozenGenerator, if_neg hx, norm_zero]
      using generatorBound_nonneg active jump V C

theorem integral_height_localizedIncrement
    (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)
    (V : E → ℝ) (j : J) (Z : Ω → ℝ → E) (T C : ℝ)
    (hq : ∀ x ∈ active, ∀ s ∈ Ioc 0 T, 0 ≤ rate j s x)
    (hbound : ∀ x ∈ active, ∀ s ∈ Ioc 0 T, rate j s x ≤ C)
    (ω : Ω) (s : ℝ) :
    (∫ u, localizedIncrement active jump rate V j
      (fun p => Z p.1 p.2.1) T C (ω,(s,u)) ∂positiveVolume) =
      (Ioc 0 T).indicator (fun s => labelDrift active jump rate V j s (Z ω s)) s := by
  by_cases hs : s ∈ Ioc 0 T
  · have he : (fun u => localizedIncrement active jump rate V j
        (fun p => Z p.1 p.2.1) T C (ω,(s,u))) =
        FrozenIntensity.heightIncrement active jump (fun j => rate j s) V j (Z ω s) := by
      funext u
      by_cases hx : Z ω s ∈ active
      · have hh : u ≤ C ∧ u ≤ rate j s (Z ω s) ↔ u ≤ rate j s (Z ω s) :=
          ⟨fun h => h.2, fun h => ⟨h.trans (hbound _ hx s hs),h⟩⟩
        simp only [localizedIncrement, hs, hx, true_and, FrozenIntensity.heightIncrement, hh]
      · simp [localizedIncrement, FrozenIntensity.heightIncrement, hs, hx]
    rw [he, FrozenIntensity.integral_heightIncrement active jump (fun j => rate j s) V j _
      (fun hx => hq _ hx s hs),
      Set.indicator_of_mem hs]
    rfl
  · have he : (fun u => localizedIncrement active jump rate V j
        (fun p => Z p.1 p.2.1) T C (ω,(s,u))) = fun _ => 0 := by
      funext u
      simp [localizedIncrement, hs]
    rw [he, integral_zero, Set.indicator_of_not_mem hs]

section Integrability
variable [MeasurableSpace Ω] [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

/-- Time measurability of each rate section gives joint generator measurability. -/
theorem measurable_frozenGenerator [Fintype J] (active : Finset E) (jump : J → E → E)
    (rate : J → ℝ → E → ℝ) (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (V : E → ℝ) : Measurable (fun p : ℝ × E => frozenGenerator active jump rate V p.1 p.2) := by
  apply measurable_from_prod_countable
  intro x
  by_cases hx : x ∈ active
  · simp only [frozenGenerator, FrozenProcess.frozenGenerator, if_pos hx]
    exact Finset.measurable_sum _ (fun j _ => (hRate j x).mul_const _)
  · simpa only [frozenGenerator, FrozenProcess.frozenGenerator, if_neg hx] using
      (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ)))

/-- Actual joint sample-time integrability follows from finite active rates;
no expected activity or stochastic equation is assumed. -/
theorem integrable_generatorField [Fintype J] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (V : E → ℝ) (Z : Ω → ℝ → E)
    (hZ : Measurable (fun p : Ω × ℝ => Z p.1 p.2)) (T C : ℝ)
    (hq : ∀ x ∈ active, ∀ j t, t ∈ Ioc 0 T → 0 ≤ rate j t x)
    (hbound : ∀ x ∈ active, ∀ j t, t ∈ Ioc 0 T → rate j t x ≤ C) :
    Integrable (fun p : Ω × ℝ => frozenGenerator active jump rate V p.2 (Z p.1 p.2))
      (μ.prod (volume.restrict (Ioc 0 T))) := by
  letI : IsFiniteMeasure (volume.restrict (Ioc 0 T)) :=
    isFiniteMeasure_restrict.mpr (by simp)
  have hm := (measurable_frozenGenerator active jump rate hRate V).comp
    (measurable_snd.prodMk hZ)
  refine ⟨hm.aestronglyMeasurable, hasFiniteIntegral_of_bounded
    (C := generatorBound active jump V C) ?_⟩
  have ht : ∀ᵐ p : Ω × ℝ ∂μ.prod (volume.restrict (Ioc 0 T)), p.2 ∈ Ioc 0 T :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_snd)).mpr
      (Filter.Eventually.of_forall (fun _ => ae_restrict_mem measurableSet_Ioc))
  filter_upwards [ht] with p hp
  exact norm_frozenGenerator_le active jump rate V C p.2
    (fun x hx j => hq x hx j p.2 hp) (fun x hx j => hbound x hx j p.2 hp) (Z p.1 p.2)

theorem ae_intensityIntegral_eq_timeDrift
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (V : E → ℝ) (j : J) (Z : Ω → ℝ → E)
    (hZ : Measurable (fun p : Ω × (ℝ × ℝ) => Z p.1 p.2.1)) (T C : ℝ)
    (hq : ∀ x ∈ active, ∀ s ∈ Ioc 0 T, 0 ≤ rate j s x)
    (hbound : ∀ x ∈ active, ∀ s ∈ Ioc 0 T, rate j s x ≤ C) :
    (fun ω => ∫ p, localizedIncrement active jump rate V j
      (fun p => Z p.1 p.2.1) T C (ω,p) ∂positiveVolume.prod positiveVolume) =ᵐ[μ]
      (fun ω => ∫ s in Ioc 0 T, labelDrift active jump rate V j s (Z ω s) ∂positiveVolume) := by
  have hi := integrable_localizedIncrement μ active jump rate hRate V j _ hZ T C
  filter_upwards [hi.prod_right_ae] with ω hω
  rw [integral_prod _ hω]
  simp_rw [integral_height_localizedIncrement active jump rate V j Z T C hq hbound ω]
  exact integral_indicator measurableSet_Ioc

/-- Each time-integrated label drift is genuinely integrable over samples. -/
theorem integrable_timeDrift
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (V : E → ℝ) (j : J) (Z : Ω → ℝ → E)
    (hZ : Measurable (fun p : Ω × (ℝ × ℝ) => Z p.1 p.2.1)) (T C : ℝ)
    (hq : ∀ x ∈ active, ∀ s ∈ Ioc 0 T, 0 ≤ rate j s x)
    (hbound : ∀ x ∈ active, ∀ s ∈ Ioc 0 T, rate j s x ≤ C) :
    Integrable (fun ω => ∫ s in Ioc 0 T,
      labelDrift active jump rate V j s (Z ω s) ∂positiveVolume) μ :=
  (integrable_localizedIncrement μ active jump rate hRate V j _ hZ T C).integral_prod_left.congr
    (ae_intensityIntegral_eq_timeDrift μ active jump rate hRate V j Z hZ T C hq hbound)

theorem ae_integrable_timeLabelDrift
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (V : E → ℝ) (j : J) (Z : Ω → ℝ → E)
    (hZ : Measurable (fun p : Ω × (ℝ × ℝ) => Z p.1 p.2.1)) (T C : ℝ)
    (hq : ∀ x ∈ active, ∀ s ∈ Ioc 0 T, 0 ≤ rate j s x)
    (hbound : ∀ x ∈ active, ∀ s ∈ Ioc 0 T, rate j s x ≤ C) :
    ∀ᵐ ω ∂μ, IntegrableOn (fun s => labelDrift active jump rate V j s (Z ω s))
      (Ioc 0 T) positiveVolume := by
  have hi := integrable_localizedIncrement μ active jump rate hRate V j _ hZ T C
  filter_upwards [hi.prod_right_ae] with ω hω
  have hh := hω.integral_prod_left
  simp_rw [integral_height_localizedIncrement active jump rate V j Z T C hq hbound ω] at hh
  exact (integrable_indicator_iff measurableSet_Ioc).mp hh

theorem ae_sum_timeDrift_eq_generator [Fintype J]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (V : E → ℝ) (Z : Ω → ℝ → E)
    (hZ : Measurable (fun p : Ω × (ℝ × ℝ) => Z p.1 p.2.1)) (T C : ℝ)
    (hq : ∀ x ∈ active, ∀ j s, s ∈ Ioc 0 T → 0 ≤ rate j s x)
    (hbound : ∀ x ∈ active, ∀ j s, s ∈ Ioc 0 T → rate j s x ≤ C) :
    (fun ω => ∑ j, ∫ s in Ioc 0 T,
      labelDrift active jump rate V j s (Z ω s) ∂positiveVolume) =ᵐ[μ]
      (fun ω => ∫ s in Ioc 0 T,
        frozenGenerator active jump rate V s (Z ω s) ∂positiveVolume) := by
  have hi : ∀ᵐ ω ∂μ, ∀ j : J, IntegrableOn
      (fun s => labelDrift active jump rate V j s (Z ω s)) (Ioc 0 T) positiveVolume :=
    (ae_all_iff).mpr (fun j => ae_integrable_timeLabelDrift μ active jump rate hRate V j Z hZ T C
      (fun x hx s hs => hq x hx j s hs) (fun x hx s hs => hbound x hx j s hs))
  filter_upwards [hi] with ω hω
  rw [← integral_finset_sum _ (fun j _ => hω j)]
  apply integral_congr_ae
  filter_upwards [] with s
  by_cases hx : Z ω s ∈ active <;> simp [labelDrift, frozenGenerator, FrozenProcess.frozenGenerator, hx]

end Integrability
end CarryingCapacity.TimeDependentGeneratorIntegral
