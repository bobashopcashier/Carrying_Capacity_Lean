import CarryingCapacity.PredictableStepApproximation

/-!
# Predictable integrands restricted to an observed horizon

Replacing times after T by zero gives a measurable map from the history at T
and the deterministic mark plane into the positive-time predictable sigma
algebra. Thus a predictable integrand restricted to (s,T] is jointly measurable
using only that history, and its deterministic-intensity integral is adapted.
-/

noncomputable section
open MeasureTheory Set MeasurableSpace

namespace CarryingCapacity.PredictableHistoryTruncation
open PredictableSets

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Future points are sent to time zero, outside every predictable generator. -/
def truncatePoint (T : ℝ) (p : Ω × (ℝ × ℝ)) : Ω × (ℝ × ℝ) :=
  (p.1, (if p.2.1 ≤ T then p.2.1 else 0, p.2.2))

/-- Up to T, positive-time predictable information is contained in history T
jointly with the deterministic time-height plane. -/
theorem measurable_truncatePoint (F : Filtration ℝ mΩ) (T : ℝ) :
    @Measurable (Ω × (ℝ × ℝ)) (Ω × (ℝ × ℝ))
      ((F T).prod inferInstance) (predictable F) (truncatePoint T) := by
  apply @measurable_generateFrom (Ω × (ℝ × ℝ)) (Ω × (ℝ × ℝ))
    ((F T).prod inferInstance) (rectangles F) (truncatePoint T)
  rintro S ⟨s, t, A, B, m, hs, hA, hB, _, rfl⟩
  have he : truncatePoint T ⁻¹' rectangle A s t B = rectangle A s (min t T) B := by
    ext p
    by_cases hp : p.2.1 ≤ T
    · simp [truncatePoint, rectangle, mem_Ioc, le_min_iff, hp]
    · simp [truncatePoint, rectangle, mem_Ioc, le_min_iff, hp, not_lt.mpr hs]
  rw [he]
  by_cases hsT : s ≤ T
  · exact ((F.mono hsT) A hA).prod (measurableSet_Ioc.prod hB)
  · have hi : Ioc s (min t T) = ∅ := Ioc_eq_empty_of_le
      ((min_le_right t T).trans (not_le.mp hsT).le)
    simp only [rectangle, hi, empty_prod, prod_empty]
    exact @MeasurableSet.empty _ ((F T).prod inferInstance)

variable {V : Type*} [MeasurableSpace V] [Zero V]

/-- Window truncation of a predictable integrand uses only the terminal
history, even though the original field depends on the full sample. -/
theorem measurable_window (F : Filtration ℝ mΩ) (f : Ω × (ℝ × ℝ) → V)
    (hf : Measurable[predictable F] f) (s T : ℝ) :
    @Measurable (Ω × (ℝ × ℝ)) V ((F T).prod inferInstance) _
      ((rectangle univ s T univ).indicator f) := by
  have hc := hf.comp (measurable_truncatePoint F T)
  have hi : @Measurable (Ω × (ℝ × ℝ)) V ((F T).prod inferInstance) _
      ((rectangle univ s T univ).indicator (f ∘ truncatePoint T)) :=
    hc.indicator (MeasurableSet.univ.prod (measurableSet_Ioc.prod MeasurableSet.univ))
  convert hi using 1
  funext p
  by_cases hp : p.2.1 ∈ Ioc s T
  · simp [rectangle, Set.indicator_apply, truncatePoint, hp, hp.2]
  · simp [rectangle, Set.indicator_apply, hp]

section Integration
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [BorelSpace V]
  [SecondCountableTopology V]

/-- Integrating a predictable window against any deterministic sigma-finite
mark measure gives a history-measurable compensator. -/
theorem measurable_intensityIntegral (F : Filtration ℝ mΩ)
    (f : Ω × (ℝ × ℝ) → V) (hf : Measurable[predictable F] f)
    (ν : Measure (ℝ × ℝ)) [SFinite ν] (s T : ℝ) :
    Measurable[F T]
      (fun ω => ∫ q, (rectangle univ s T univ).indicator f (ω,q) ∂ν) := by
  have hw := measurable_window F f hf s T
  letI : MeasurableSpace Ω := F T
  have hw' : Measurable ((rectangle univ s T univ).indicator f) := hw
  exact (hw'.stronglyMeasurable.integral_prod_right').measurable

end Integration
end CarryingCapacity.PredictableHistoryTruncation
