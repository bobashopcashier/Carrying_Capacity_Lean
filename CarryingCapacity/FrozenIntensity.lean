import CarryingCapacity.MarkedIntensity
import CarryingCapacity.ThinningKernel
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Finite-region integrability and the height-integrated generator

The actual frozen acceptance rule has a deterministic bound on a finite
active set. Restricting it to a finite time-height box therefore gives an
integrable signed increment under any probability law on the sample space.
Integrating its height coordinate gives the frozen generator exactly.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical ENNReal

namespace CarryingCapacity.FrozenIntensity
open MarkedIntensity

variable {E J : Type*} [DecidableEq E]

/-- The signed contribution accepted by one label at a fixed state. -/
def heightIncrement (active : Finset E) (jump : J → E → E)
    (rate : J → E → ℝ) (V : E → ℝ) (j : J) (x : E) (u : ℝ) : ℝ :=
  if x ∈ active ∧ u ≤ rate j x then V (jump j x) - V x else 0

theorem integrable_heightIncrement (active : Finset E) (jump : J → E → E)
    (rate : J → E → ℝ) (V : E → ℝ) (j : J) (x : E) :
    Integrable (heightIncrement active jump rate V j x) positiveVolume := by
  by_cases hx : x ∈ active
  · have he : heightIncrement active jump rate V j x =
        (Iic (rate j x)).indicator (fun _ => V (jump j x) - V x) := by
      funext u
      simp [heightIncrement, hx, Set.indicator]
    rw [he, integrable_indicator_iff measurableSet_Iic]
    apply integrableOn_const.mpr (Or.inr _)
    rw [positiveVolume_Iic]
    exact ENNReal.ofReal_lt_top
  · have he : heightIncrement active jump rate V j x = fun _ => 0 := by
      funext u
      simp [heightIncrement, hx]
    rw [he]
    exact integrable_zero _ _ _

theorem integral_heightIncrement (active : Finset E) (jump : J → E → E)
    (rate : J → E → ℝ) (V : E → ℝ) (j : J) (x : E)
    (hq : x ∈ active → 0 ≤ rate j x) :
    (∫ u, heightIncrement active jump rate V j x u ∂positiveVolume) =
      if x ∈ active then rate j x * (V (jump j x) - V x) else 0 := by
  by_cases hx : x ∈ active
  · have he : heightIncrement active jump rate V j x =
        (Iic (rate j x)).indicator (fun _ => V (jump j x) - V x) := by
      funext u
      simp [heightIncrement, hx, Set.indicator]
    rw [he, integral_indicator_const _ measurableSet_Iic, measureReal_def,
      positiveVolume_Iic, ENNReal.toReal_ofReal (hq hx)]
    simp [hx, smul_eq_mul]
  · simp [heightIncrement, hx]

/-- Summing the actual height integrals gives precisely the existing generator. -/
theorem sum_integral_heightIncrement [Fintype J]
    (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)
    (V : E → ℝ) (x : E) (hq : ∀ j, x ∈ active → 0 ≤ rate j x) :
    (∑ j, ∫ u, heightIncrement active jump rate V j x u ∂positiveVolume) =
      FrozenProcess.frozenGenerator active jump rate V x := by
  simp_rw [integral_heightIncrement active jump rate V _ x (hq _)]
  by_cases hx : x ∈ active <;> simp [FrozenProcess.frozenGenerator, hx]

section Sample
variable {Ω : Type*} [MeasurableSpace Ω]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

/-- A finite-horizon accepted increment with the same height cutoff as the
constructed frozen path. The state input may be any measurable sample-time field. -/
def localizedIncrement (active : Finset E) (jump : J → E → E)
    (rate : J → E → ℝ) (V : E → ℝ) (j : J)
    (Z : Ω × (ℝ × ℝ) → E) (T C : ℝ) (p : Ω × (ℝ × ℝ)) : ℝ :=
  if p.2.1 ∈ Ioc 0 T ∧ Z p ∈ active ∧ p.2.2 ≤ C ∧ p.2.2 ≤ rate j (Z p)
    then V (jump j (Z p)) - V (Z p) else 0

theorem measurable_localizedIncrement (active : Finset E) (jump : J → E → E)
    (rate : J → E → ℝ) (V : E → ℝ) (j : J)
    (Z : Ω × (ℝ × ℝ) → E) (hZ : Measurable Z) (T C : ℝ) :
    Measurable (localizedIncrement active jump rate V j Z T C) := by
  apply Measurable.ite
  · exact (measurableSet_Ioc.preimage measurable_snd.fst).inter
      (((Finset.measurableSet active).preimage hZ).inter
        ((measurableSet_le measurable_snd.snd measurable_const).inter
          (measurableSet_le measurable_snd.snd ((measurable_of_countable (rate j)).comp hZ))))
  · exact ((measurable_of_countable (fun x => V (jump j x))).comp hZ).sub
      ((measurable_of_countable V).comp hZ)
  · exact measurable_const

/-- A deterministic bound depending only on the finite active states. -/
def incrementBound (active : Finset E) (jump : J → E → E) (V : E → ℝ) (j : J) : ℝ :=
  ∑ x ∈ active, |V (jump j x) - V x|

omit [MeasurableSpace Ω] [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] in
theorem norm_localizedIncrement_le (active : Finset E) (jump : J → E → E)
    (rate : J → E → ℝ) (V : E → ℝ) (j : J)
    (Z : Ω × (ℝ × ℝ) → E) (T C : ℝ) (p : Ω × (ℝ × ℝ)) :
    ‖localizedIncrement active jump rate V j Z T C p‖ ≤
      (univ ×ˢ (Ioc 0 T ×ˢ Iic C)).indicator
        (fun _ => incrementBound active jump V j) p := by
  have hnonneg : 0 ≤ incrementBound active jump V j :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  by_cases h : p.2.1 ∈ Ioc 0 T ∧ Z p ∈ active ∧ p.2.2 ≤ C ∧ p.2.2 ≤ rate j (Z p)
  · rw [localizedIncrement, if_pos h, Set.indicator_of_mem (show
        p ∈ univ ×ˢ (Ioc 0 T ×ˢ Iic C) from ⟨mem_univ _,h.1,h.2.2.1⟩), Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun y : E => |V (jump j y) - V y|)
      (fun _ _ => abs_nonneg _) h.2.1
  · rw [localizedIncrement, if_neg h, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hnonneg) p

/-- No stochastic moment assumption is needed for a finite active region:
the deterministic time-height box and finite increment bound give integrability. -/
theorem integrable_localizedIncrement (μ : Measure Ω) [IsProbabilityMeasure μ]
    (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ)
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
  exact hg.mono' (measurable_localizedIncrement active jump rate V j Z hZ T C).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_localizedIncrement_le active jump rate V j Z T C))

end Sample
end CarryingCapacity.FrozenIntensity
