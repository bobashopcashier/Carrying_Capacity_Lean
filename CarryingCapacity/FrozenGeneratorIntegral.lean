import CarryingCapacity.FrozenIntensity

/-!
# Integrating the actual frozen acceptance rule against intensity

The height cutoff disappears when it dominates the rates on the active set.
Bochner Fubini then identifies the finite-horizon intensity integral with
the time integral of the rate-weighted test-function increment.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace CarryingCapacity.FrozenGeneratorIntegral
open MarkedIntensity FrozenIntensity

variable {Ω E J : Type*} [DecidableEq E]

/-- The contribution of one jump label to the frozen generator. -/
def labelDrift (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)
    (V : E → ℝ) (j : J) (x : E) : ℝ :=
  if x ∈ active then rate j x * (V (jump j x) - V x) else 0

theorem integral_height_localizedIncrement
    (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)
    (V : E → ℝ) (j : J) (Z : Ω → ℝ → E) (T C : ℝ)
    (hq : ∀ x ∈ active, 0 ≤ rate j x) (hbound : ∀ x ∈ active, rate j x ≤ C)
    (ω : Ω) (s : ℝ) :
    (∫ u, localizedIncrement active jump rate V j
      (fun p => Z p.1 p.2.1) T C (ω,(s,u)) ∂positiveVolume) =
      (Ioc 0 T).indicator (fun s => labelDrift active jump rate V j (Z ω s)) s := by
  by_cases hs : s ∈ Ioc 0 T
  · have he : (fun u => localizedIncrement active jump rate V j
        (fun p => Z p.1 p.2.1) T C (ω,(s,u))) =
        heightIncrement active jump rate V j (Z ω s) := by
      funext u
      by_cases hx : Z ω s ∈ active
      · have hh : u ≤ C ∧ u ≤ rate j (Z ω s) ↔ u ≤ rate j (Z ω s) :=
          ⟨fun h => h.2, fun h => ⟨h.trans (hbound _ hx),h⟩⟩
        simp only [localizedIncrement, hs, hx, true_and, heightIncrement, hh]
      · simp [localizedIncrement, heightIncrement, hs, hx]
    rw [he, integral_heightIncrement active jump rate V j _ (hq _),
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

theorem ae_intensityIntegral_eq_timeDrift
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)
    (V : E → ℝ) (j : J) (Z : Ω → ℝ → E)
    (hZ : Measurable (fun p : Ω × (ℝ × ℝ) => Z p.1 p.2.1)) (T C : ℝ)
    (hq : ∀ x ∈ active, 0 ≤ rate j x) (hbound : ∀ x ∈ active, rate j x ≤ C) :
    (fun ω => ∫ p, localizedIncrement active jump rate V j
      (fun p => Z p.1 p.2.1) T C (ω,p) ∂positiveVolume.prod positiveVolume) =ᵐ[μ]
      (fun ω => ∫ s in Ioc 0 T, labelDrift active jump rate V j (Z ω s) ∂positiveVolume) := by
  have hi := integrable_localizedIncrement μ active jump rate V j _ hZ T C
  filter_upwards [hi.prod_right_ae] with ω hω
  rw [integral_prod _ hω]
  simp_rw [integral_height_localizedIncrement active jump rate V j Z T C hq hbound ω]
  exact integral_indicator measurableSet_Ioc

/-- Each time-integrated label drift is genuinely integrable over samples. -/
theorem integrable_timeDrift
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)
    (V : E → ℝ) (j : J) (Z : Ω → ℝ → E)
    (hZ : Measurable (fun p : Ω × (ℝ × ℝ) => Z p.1 p.2.1)) (T C : ℝ)
    (hq : ∀ x ∈ active, 0 ≤ rate j x) (hbound : ∀ x ∈ active, rate j x ≤ C) :
    Integrable (fun ω => ∫ s in Ioc 0 T,
      labelDrift active jump rate V j (Z ω s) ∂positiveVolume) μ :=
  (integrable_localizedIncrement μ active jump rate V j _ hZ T C).integral_prod_left.congr
    (ae_intensityIntegral_eq_timeDrift μ active jump rate V j Z hZ T C hq hbound)

theorem ae_integrable_timeLabelDrift
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)
    (V : E → ℝ) (j : J) (Z : Ω → ℝ → E)
    (hZ : Measurable (fun p : Ω × (ℝ × ℝ) => Z p.1 p.2.1)) (T C : ℝ)
    (hq : ∀ x ∈ active, 0 ≤ rate j x) (hbound : ∀ x ∈ active, rate j x ≤ C) :
    ∀ᵐ ω ∂μ, IntegrableOn (fun s => labelDrift active jump rate V j (Z ω s))
      (Ioc 0 T) positiveVolume := by
  have hi := integrable_localizedIncrement μ active jump rate V j _ hZ T C
  filter_upwards [hi.prod_right_ae] with ω hω
  have hh := hω.integral_prod_left
  simp_rw [integral_height_localizedIncrement active jump rate V j Z T C hq hbound ω] at hh
  exact (integrable_indicator_iff measurableSet_Ioc).mp hh

theorem ae_sum_timeDrift_eq_generator [Fintype J]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)
    (V : E → ℝ) (Z : Ω → ℝ → E)
    (hZ : Measurable (fun p : Ω × (ℝ × ℝ) => Z p.1 p.2.1)) (T C : ℝ)
    (hq : ∀ x ∈ active, ∀ j, 0 ≤ rate j x)
    (hbound : ∀ x ∈ active, ∀ j, rate j x ≤ C) :
    (fun ω => ∑ j, ∫ s in Ioc 0 T,
      labelDrift active jump rate V j (Z ω s) ∂positiveVolume) =ᵐ[μ]
      (fun ω => ∫ s in Ioc 0 T,
        FrozenProcess.frozenGenerator active jump rate V (Z ω s) ∂positiveVolume) := by
  have hi : ∀ᵐ ω ∂μ, ∀ j : J, IntegrableOn
      (fun s => labelDrift active jump rate V j (Z ω s)) (Ioc 0 T) positiveVolume :=
    (ae_all_iff).mpr (fun j => ae_integrable_timeLabelDrift μ active jump rate V j Z hZ T C
      (fun x hx => hq x hx j) (fun x hx => hbound x hx j))
  filter_upwards [hi] with ω hω
  rw [← integral_finset_sum _ (fun j _ => hω j)]
  apply integral_congr_ae
  filter_upwards [] with s
  by_cases hx : Z ω s ∈ active <;> simp [labelDrift, FrozenProcess.frozenGenerator, hx]

end Integrability
end CarryingCapacity.FrozenGeneratorIntegral
