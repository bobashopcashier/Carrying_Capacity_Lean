import CarryingCapacity.MarkedPoissonMeasure
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Infinite-intensity sets have infinite actual count

The finite Poisson laws and increasing bounded boxes imply that every fixed
measurable planar set of infinite intensity has infinite random-measure mass
almost surely. The proof uses the explicit Poisson lower tails, which vanish
when the parameter tends to infinity. No infinite-intensity count law is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

namespace CarryingCapacity.MarkedInfiniteIntensity
open MarkedNoise MarkedIntensity MarkedSetCounts MarkedSetPoissonLimit
  MarkedBoxApproximation

variable {J : Type*}

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

/-- A fixed finite lower tail vanishes as the Poisson parameter grows. -/
theorem tendsto_poisson_Iic_zero {α : Type*} {l : Filter α} (r : α → ℝ≥0)
    (hr : Tendsto (fun a => (r a : ℝ)) l atTop) (k : ℕ) :
    Tendsto (fun a => poissonMeasure (r a) (Iic k)) l (𝓝 0) := by
  have hs (n : ℕ) : Tendsto (fun a => poissonMeasure (r a) {n}) l (𝓝 0) := by
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp hr).div_const
      (n.factorial : ℝ)
    have he := (ENNReal.continuous_ofReal.tendsto (0 / (n.factorial : ℝ))).comp h
    simpa only [zero_div, ENNReal.ofReal_zero, poissonMeasure,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      poissonPMF, poissonPMFReal, mul_comm] using he
  have h := tendsto_finset_sum (Finset.Iic k) (fun n _ => hs n)
  simpa only [Finset.sum_const_zero, sum_measure_singleton, Finset.coe_Iic] using h

theorem intensity_box_ne_top (n : ℕ) :
    (positiveVolume.prod positiveVolume) (box n) ≠ ∞ := by
  apply ne_top_of_le_ne_top _ (measure_mono (show box n ⊆ Iic (n : ℝ) ×ˢ Iic (n : ℝ) from
    fun p hp => ⟨hp.1.2, show p.2 ≤ (n : ℝ) from le_of_lt hp.2⟩))
  rw [Measure.prod_prod, positiveVolume_Iic]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- The finite parameters of the bounded intersections tend to infinity. -/
theorem tendsto_setRate_inter_box (S : Set (ℝ × ℝ))
    (hinf : (positiveVolume.prod positiveVolume) S = ∞) :
    Tendsto (fun n => (setRate (S ∩ box n) : ℝ)) atTop atTop := by
  have hm : Monotone (fun n => S ∩ box n) := fun _ _ h => inter_subset_inter_right S (box_mono h)
  have ht := tendsto_measure_iUnion_atTop (μ := positiveVolume.prod positiveVolume) hm
  have he : (⋃ n, S ∩ box n) = S ∩ ⋃ n, box n := by ext p; simp
  rw [he, measure_inter_conull intensity_compl_iUnion_box, hinf] at ht
  apply ENNReal.tendsto_ofReal_nhds_top.mp
  convert ht using 1
  funext n
  exact ENNReal.ofReal_toReal (measure_ne_top_of_subset inter_subset_right (intensity_box_ne_top n))

/-- Every fixed upper bound on the mass has probability zero. -/
theorem measure_countingMeasure_le_eq_zero (j : J) (S : Set (ℝ × ℝ))
    (hS : MeasurableSet S) (hinf : (positiveVolume.prod positiveVolume) S = ∞) (k : ℕ) :
    law J {ω | countingMeasure j ω S ≤ (k : ℝ≥0∞)} = 0 := by
  have hb (n : ℕ) : law J {ω | countingMeasure j ω S ≤ (k : ℝ≥0∞)} ≤
      poissonMeasure (setRate (S ∩ box n)) (Iic k) := by
    rw [← MarkedPoissonMeasure.count_map j (S ∩ box n) (hS.inter (measurableSet_box n))
      (measure_ne_top_of_subset inter_subset_right (intensity_box_ne_top n)),
      Measure.map_apply (measurable_count j _ (hS.inter (measurableSet_box n))) measurableSet_Iic]
    apply measure_mono_ae
    filter_upwards [ae_countingMeasure_eq_count j (S ∩ box n) (hS.inter (measurableSet_box n))
      (measure_ne_top_of_subset inter_subset_right (intensity_box_ne_top n))] with ω hω
    intro hle
    have hm : countingMeasure j ω (S ∩ box n) ≤ countingMeasure j ω S := measure_mono inter_subset_left
    rw [hω] at hm
    exact_mod_cast hm.trans hle
  exact le_antisymm (ge_of_tendsto' (tendsto_poisson_Iic_zero _
    (tendsto_setRate_inter_box S hinf) k) hb) (zero_le _)

/-- Actual infinite mass, rather than the total natural count version, on
every fixed measurable set of infinite intensity. -/
theorem ae_countingMeasure_eq_top (j : J) (S : Set (ℝ × ℝ))
    (hS : MeasurableSet S) (hinf : (positiveVolume.prod positiveVolume) S = ∞) :
    ∀ᵐ ω ∂law J, countingMeasure j ω S = ∞ := by
  have hk (k : ℕ) : ∀ᵐ ω ∂law J, ¬ countingMeasure j ω S ≤ (k : ℝ≥0∞) := by
    simpa only [ae_iff, not_not, mem_setOf_eq] using
      measure_countingMeasure_le_eq_zero j S hS hinf k
  filter_upwards [ae_all_iff.mpr hk] with ω hω
  by_contra hf
  obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hf
  exact hω k hk.le

/-- The law of the genuine mass on an infinite-intensity set is the point mass at infinity. -/
theorem countingMeasure_map_eq_dirac_top (j : J) (S : Set (ℝ × ℝ))
    (hS : MeasurableSet S) (hinf : (positiveVolume.prod positiveVolume) S = ∞) :
    Measure.map (fun ω : Sample J => countingMeasure j ω S) (law J) = Measure.dirac ∞ := by
  rw [Measure.map_congr (ae_countingMeasure_eq_top j S hS hinf)]
  simp

end CarryingCapacity.MarkedInfiniteIntensity
