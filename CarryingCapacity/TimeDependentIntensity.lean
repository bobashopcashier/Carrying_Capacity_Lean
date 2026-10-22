import CarryingCapacity.FrozenIntensity
import CarryingCapacity.PredictableTime

/-!
# Integrability of time-dependent accepted increments

The deterministic finite time-height box bounds every accepted increment,
regardless of variation of the measurable time coefficient. The state field
need only be jointly measurable. Pointwise height integration uses the actual
coefficient evaluated at that time.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal

namespace CarryingCapacity.TimeDependentIntensity
open MarkedIntensity FrozenIntensity

variable {Ω E J : Type*} [MeasurableSpace Ω] [DecidableEq E]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

/-- A bounded-horizon acceptance field using the actual event time. -/
def localizedIncrement (active : Finset E) (jump : J → E → E)
    (rate : J → ℝ → E → ℝ) (V : E → ℝ) (j : J)
    (Z : Ω × (ℝ × ℝ) → E) (T C : ℝ) (p : Ω × (ℝ × ℝ)) : ℝ :=
  if p.2.1 ∈ Ioc 0 T ∧ Z p ∈ active ∧ p.2.2 ≤ C ∧ p.2.2 ≤ rate j p.2.1 (Z p)
    then V (jump j (Z p)) - V (Z p) else 0

theorem measurable_localizedIncrement (active : Finset E) (jump : J → E → E)
    (rate : J → ℝ → E → ℝ) (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (V : E → ℝ) (j : J) (Z : Ω × (ℝ × ℝ) → E) (hZ : Measurable Z) (T C : ℝ) :
    Measurable (localizedIncrement active jump rate V j Z T C) := by
  have hr := (PredictableTime.measurable_coefficient (rate j) (hRate j)).comp
    (measurable_snd.fst.prodMk hZ)
  exact (((measurable_of_countable (fun x => V (jump j x))).comp hZ).sub
    ((measurable_of_countable V).comp hZ)).ite
      ((measurableSet_Ioc.preimage measurable_snd.fst).inter
        (((Finset.measurableSet active).preimage hZ).inter
          ((measurableSet_le measurable_snd.snd measurable_const).inter
            (measurableSet_le measurable_snd.snd hr)))) measurable_const

omit [MeasurableSpace Ω] [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] in
/-- The same finite increment bound works for arbitrary time coefficients. -/
theorem norm_localizedIncrement_le (active : Finset E) (jump : J → E → E)
    (rate : J → ℝ → E → ℝ) (V : E → ℝ) (j : J)
    (Z : Ω × (ℝ × ℝ) → E) (T C : ℝ) (p : Ω × (ℝ × ℝ)) :
    ‖localizedIncrement active jump rate V j Z T C p‖ ≤
      (univ ×ˢ (Ioc 0 T ×ˢ Iic C)).indicator
        (fun _ => incrementBound active jump V j) p :=
  FrozenIntensity.norm_localizedIncrement_le active jump (fun j x => rate j p.2.1 x)
    V j Z T C p

/-- Finite active set and box support derive actual product integrability. -/
theorem integrable_localizedIncrement (μ : Measure Ω) [IsProbabilityMeasure μ]
    (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)
    (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (V : E → ℝ) (j : J) (Z : Ω × (ℝ × ℝ) → E) (hZ : Measurable Z) (T C : ℝ) :
    Integrable (localizedIncrement active jump rate V j Z T C)
      (μ.prod (positiveVolume.prod positiveVolume)) := by
  have hbox : (μ.prod (positiveVolume.prod positiveVolume))
      (univ ×ˢ (Ioc 0 T ×ˢ Iic C)) < ∞ := by
    apply lt_of_le_of_lt (measure_mono (Set.prod_mono Subset.rfl
      (Set.prod_mono Ioc_subset_Iic_self Subset.rfl)))
    rw [Measure.prod_prod, measure_univ, one_mul, Measure.prod_prod,
      positiveVolume_Iic, positiveVolume_Iic]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hg : Integrable ((univ ×ˢ (Ioc 0 T ×ˢ Iic C)).indicator
      (fun _ : Ω × (ℝ × ℝ) => incrementBound active jump V j))
      (μ.prod (positiveVolume.prod positiveVolume)) :=
    (integrable_indicator_iff (MeasurableSet.univ.prod
      (measurableSet_Ioc.prod measurableSet_Iic))).mpr
      (integrableOn_const.mpr (Or.inr hbox))
  exact hg.mono' (measurable_localizedIncrement active jump rate hRate V j Z hZ T C).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_localizedIncrement_le active jump rate V j Z T C))

end CarryingCapacity.TimeDependentIntensity
