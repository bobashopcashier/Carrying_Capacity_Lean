import CarryingCapacity.PredictableStepApproximation

/-!
# Deterministic time in the positive-time predictable sigma algebra

A Borel time-dependent coefficient can be evaluated predictably together with
a predictable countable-state process. Nonpositive times use a fixed fallback,
matching the existing positive-time predictable sigma algebra.
-/

noncomputable section
open MeasureTheory Set

namespace CarryingCapacity.PredictableTime
open PredictableSets PredictableStepApproximation

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]

def positiveTime (p : Ω × (ℝ × ℝ)) : ℝ := if 0 < p.2.1 then p.2.1 else 0

theorem measurable_positiveTime (F : Filtration ℝ mΩ) :
    Measurable[predictable F] (positiveTime (Ω := Ω)) :=
  measurable_of_leftContinuous F (fun s _ => s) (fun _ _ => measurable_const) 0
    (fun _ _ _ => continuous_id.continuousWithinAt)

/-- Separate time measurability suffices on a countable state space. -/
theorem measurable_coefficient [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
    (f : ℝ → E → ℝ) (hf : ∀ x, Measurable (fun t => f t x)) :
    Measurable (fun p : ℝ × E => f p.1 p.2) := by
  apply measurable_from_prod_countable
  exact hf

/-- Time and state can be evaluated together without continuity of the rate. -/
theorem measurable_evaluation [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
    (F : Filtration ℝ mΩ) (f : ℝ → E → ℝ) (hf : ∀ x, Measurable (fun t => f t x))
    (Z : Ω × (ℝ × ℝ) → E) (hZ : Measurable[predictable F] Z) :
    Measurable[predictable F] (fun p => f (positiveTime p) (Z p)) :=
  (measurable_coefficient f hf).comp ((measurable_positiveTime F).prodMk hZ)

end CarryingCapacity.PredictableTime
