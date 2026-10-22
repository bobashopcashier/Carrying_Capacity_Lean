import CarryingCapacity.MarkedSetCounts
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Finite-intensity sets can be truncated to bounded positive-time boxes

The actual intensity gives zero mass to nonpositive times. Increasing positive
time-height boxes therefore exhaust it. Finite target intensity gives vanishing
truncation errors and a simultaneous summable sequence for any finite family.
-/

noncomputable section
open MeasureTheory Set Filter symmDiff
open scoped ENNReal NNReal BigOperators Topology

namespace CarryingCapacity.MarkedBoxApproximation
open MarkedIntensity

local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

/-- Boxes matched to the existing bounded time-grid count theorem. -/
def box (n : ℕ) : Set (ℝ × ℝ) := Ioc 0 (n : ℝ) ×ˢ Iio (n : ℝ)

theorem measurableSet_box (n : ℕ) : MeasurableSet (box n) :=
  measurableSet_Ioc.prod measurableSet_Iio

theorem box_mono : Monotone box := by
  intro n m hnm p hp
  have h : (n : ℝ) ≤ m := by exact_mod_cast hnm
  exact ⟨⟨hp.1.1, hp.1.2.trans h⟩, hp.2.trans_le h⟩

theorem iUnion_box : (⋃ n, box n) = Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := by
  ext p
  constructor
  · intro h
    obtain ⟨n, hn⟩ := mem_iUnion.mp h
    exact ⟨hn.1.1, mem_univ _⟩
  · intro h
    obtain ⟨n, hn⟩ := exists_nat_gt (max p.1 p.2)
    exact mem_iUnion.mpr ⟨n, ⟨h.1, ((le_max_left _ _).trans_lt hn).le⟩,
      (le_max_right _ _).trans_lt hn⟩

theorem intensity_compl_iUnion_box :
    (positiveVolume.prod positiveVolume) (⋃ n, box n)ᶜ = 0 := by
  rw [iUnion_box]
  have he : (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))ᶜ = Iic 0 ×ˢ (univ : Set ℝ) := by
    ext p
    simp
  rw [he, Measure.prod_prod, positiveVolume_Iic]
  simp

/-- Continuity from above applies because the target set has finite intensity. -/
theorem tendsto_intensity_diff_box (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (hfin : (positiveVolume.prod positiveVolume) S ≠ ∞) :
    Tendsto (fun n => (positiveVolume.prod positiveVolume) (S \ box n)) atTop (𝓝 0) := by
  have hm : Antitone (fun n => S \ box n) := by
    intro n m hnm p hp
    exact ⟨hp.1, fun h => hp.2 (box_mono hnm h)⟩
  have hz : (positiveVolume.prod positiveVolume) (⋂ n, S \ box n) = 0 := by
    apply measure_mono_null _ intensity_compl_iUnion_box
    intro p hp hbox
    obtain ⟨n, hn⟩ := mem_iUnion.mp hbox
    exact (mem_iInter.mp hp n).2 hn
  have ht := tendsto_measure_iInter_atTop
    (fun n => (hS.diff (measurableSet_box n)).nullMeasurableSet) hm
    ⟨0, measure_ne_top_of_subset diff_subset hfin⟩
  simpa only [Function.comp_def, hz] using ht

theorem inter_box_symmDiff (S : Set (ℝ × ℝ)) (n : ℕ) :
    (S ∩ box n) ∆ S = S \ box n := by
  ext p
  simp only [mem_symmDiff, mem_inter_iff, mem_diff]
  tauto

/-- One common cutoff at each approximation index gives summable errors for
every coordinate in an arbitrary finite family of finite-intensity sets. -/
theorem exists_summable_box_truncations {ι : Type*} [Fintype ι]
    (S : ι → Set (ℝ × ℝ)) (hS : ∀ i, MeasurableSet (S i))
    (hfin : ∀ i, (positiveVolume.prod positiveVolume) (S i) ≠ ∞) :
    ∃ m : ℕ → ℕ, ∀ i,
      (∑' n, (positiveVolume.prod positiveVolume) ((S i ∩ box (m n)) ∆ S i)) ≠ ∞ := by
  have hc (n : ℕ) : ∃ m : ℕ, ∀ i,
      (positiveVolume.prod positiveVolume) (S i \ box m) < (2 : ℝ≥0∞)⁻¹ ^ n := by
    have hi (i : ι) : ∀ᶠ m in atTop,
        (positiveVolume.prod positiveVolume) (S i \ box m) < (2 : ℝ≥0∞)⁻¹ ^ n :=
      (tendsto_intensity_diff_box (S i) (hS i) (hfin i)).eventually
        (Iio_mem_nhds (ENNReal.pow_pos (by norm_num : (0 : ℝ≥0∞) < (2 : ℝ≥0∞)⁻¹) n))
    exact (eventually_all.mpr hi).exists
  choose m hm using hc
  refine ⟨m, fun i => ?_⟩
  simp_rw [inter_box_symmDiff]
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum (fun n => (hm n i).le))
  rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  norm_num

end CarryingCapacity.MarkedBoxApproximation
