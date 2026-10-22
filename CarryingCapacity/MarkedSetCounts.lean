import CarryingCapacity.MarkedIntensity
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Actual counts and approximation bounds on measurable planar sets

The shared marked counting measure is the counting measure of its actual
indexed atoms. Every measurable set of finite intensity therefore has a finite
natural count almost surely. The probability that two counts differ is bounded
by the intensity of their symmetric difference. These results do not assume a
Poisson law on arbitrary measurable sets.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter symmDiff
open scoped ENNReal NNReal BigOperators

namespace CarryingCapacity.MarkedSetCounts
open MarkedNoise MarkedIntensity

variable {J : Type*}

/-- Exact atom counting, including infinite values and arbitrary samples. -/
theorem countingMeasure_eq_count_preimage (j : J) (ω : Sample J)
    (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) :
    countingMeasure j ω S = Measure.count ((point j ω) ⁻¹' S) := by
  rw [countingMeasure, Measure.sum_apply _ hS, Measure.count,
    Measure.sum_apply _ (hS.preimage (measurable_of_countable _))]
  apply tsum_congr
  intro n
  simp only [Measure.dirac_apply' _ hS,
    Measure.dirac_apply' _ (hS.preimage (measurable_of_countable _)), mem_preimage]
  by_cases hn : point j ω n ∈ S <;> simp [hn]

/-- Finite actual mass is a natural number, with no simplicity assumption:
coincident indexed atoms are counted with their multiplicities. -/
theorem exists_nat_count_of_lt_top (j : J) (ω : Sample J)
    (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (hfin : countingMeasure j ω S < ∞) :
    ∃ n : ℕ, countingMeasure j ω S = n := by
  rw [countingMeasure_eq_count_preimage j ω S hS] at hfin ⊢
  have hf := Measure.count_apply_lt_top.mp hfin
  exact ⟨hf.toFinset.card, Measure.count_apply_finite _ hf⟩

/-- Any nonzero actual count is at least one, even on exceptional samples. -/
theorem one_le_countingMeasure_of_ne_zero (j : J) (ω : Sample J)
    (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (h : countingMeasure j ω S ≠ 0) : 1 ≤ countingMeasure j ω S := by
  rw [countingMeasure_eq_count_preimage j ω S hS] at h ⊢
  obtain ⟨n, hn⟩ := Measure.count_ne_zero_iff.mp h
  calc
    1 = Measure.count ({n} : Set (ℕ × ℕ)) := (Measure.count_singleton n).symm
    _ ≤ Measure.count ((point j ω) ⁻¹' S) := measure_mono (singleton_subset_iff.mpr hn)

/-- A total natural-valued version of a measurable set count. On finite-intensity
sets it equals the genuine mass almost surely; infinite masses map to zero. -/
def count (j : J) (S : Set (ℝ × ℝ)) (ω : Sample J) : ℕ :=
  ⌊(countingMeasure j ω S).toReal⌋₊

theorem measurable_count (j : J) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) :
    Measurable (count j S) :=
  (((Measure.measurable_coe hS).comp (measurable_countingMeasure j)).ennreal_toReal).nat_floor

/-- Finite intensity proves almost-sure finiteness of the actual count. -/
theorem ae_countingMeasure_lt_top (j : J) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (hfin : (positiveVolume.prod positiveVolume) S ≠ ∞) :
    ∀ᵐ ω ∂law J, countingMeasure j ω S < ∞ := by
  apply ae_lt_top ((Measure.measurable_coe hS).comp (measurable_countingMeasure j))
  change (∫⁻ ω, countingMeasure j ω S ∂law J) ≠ ∞
  rwa [lintegral_counting_set j S hS]

/-- The natural count represents the original random measure on every fixed
measurable finite-intensity set. -/
theorem ae_countingMeasure_eq_count (j : J) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (hfin : (positiveVolume.prod positiveVolume) S ≠ ∞) :
    ∀ᵐ ω ∂law J, countingMeasure j ω S = (count j S ω : ℝ≥0∞) := by
  filter_upwards [ae_countingMeasure_lt_top j S hS hfin] with ω hω
  obtain ⟨n, hn⟩ := exists_nat_count_of_lt_top j ω S hS hω
  simp only [count, hn, ENNReal.toReal_natCast, Nat.floor_natCast]

/-- The natural count has the exact intensity expectation in extended reals. -/
theorem lintegral_count (j : J) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (hfin : (positiveVolume.prod positiveVolume) S ≠ ∞) :
    (∫⁻ ω, (count j S ω : ℝ≥0∞) ∂law J) = (positiveVolume.prod positiveVolume) S := by
  rw [lintegral_congr_ae ((ae_countingMeasure_eq_count j S hS hfin).mono (fun _ h => h.symm))]
  exact lintegral_counting_set j S hS

/-- Finite intensity gives genuine integrability of the real-valued count. -/
theorem integrable_count (j : J) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (hfin : (positiveVolume.prod positiveVolume) S ≠ ∞) :
    Integrable (fun ω => (count j S ω : ℝ)) (law J) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_count j S hS)).aestronglyMeasurable
    (Eventually.of_forall (fun _ => Nat.cast_nonneg _))).mp
  simpa only [Function.comp_def, ENNReal.ofReal_natCast, lintegral_count j S hS hfin] using hfin

/-- The ordinary expectation is precisely the finite intensity. -/
theorem integral_count (j : J) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (hfin : (positiveVolume.prod positiveVolume) S ≠ ∞) :
    (∫ ω, (count j S ω : ℝ) ∂law J) = (positiveVolume.prod positiveVolume).real S := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun _ => Nat.cast_nonneg _))
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_count j S hS)).aestronglyMeasurable]
  simp only [ENNReal.ofReal_natCast, lintegral_count j S hS hfin, Measure.real]

/-- A changed count requires at least one atom in the symmetric difference. -/
theorem one_le_symmDiff_of_countingMeasure_ne (j : J) (ω : Sample J)
    (S T : Set (ℝ × ℝ)) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hne : countingMeasure j ω S ≠ countingMeasure j ω T) :
    1 ≤ countingMeasure j ω (S ∆ T) := by
  apply one_le_countingMeasure_of_ne_zero j ω (S ∆ T) (hS.symmDiff hT)
  intro hzero
  exact hne (measure_congr (measure_symmDiff_eq_zero_iff.mp hzero))

/-- Quantitative comparison for genuine masses, with no boundedness or
finite-intensity requirement. -/
theorem measure_countingMeasure_ne_le (j : J)
    (S T : Set (ℝ × ℝ)) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (law J) {ω | countingMeasure j ω S ≠ countingMeasure j ω T} ≤
      (positiveVolume.prod positiveVolume) (S ∆ T) := by
  rw [← lintegral_counting_set j (S ∆ T) (hS.symmDiff hT)]
  exact meas_le_lintegral₀
    (((Measure.measurable_coe (hS.symmDiff hT)).comp (measurable_countingMeasure j)).aemeasurable)
    (fun ω hω => one_le_symmDiff_of_countingMeasure_ne j ω S T hS hT hω)

/-- The same bound applies to the natural-valued counts. It is the direct
bridge from intensity approximation to agreement in probability. -/
theorem measure_count_ne_le (j : J)
    (S T : Set (ℝ × ℝ)) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (law J) {ω | count j S ω ≠ count j T ω} ≤
      (positiveVolume.prod positiveVolume) (S ∆ T) := by
  apply (measure_mono ?_).trans (measure_countingMeasure_ne_le j S T hS hT)
  intro ω hω hEq
  exact hω (congrArg (fun x : ℝ≥0∞ => ⌊x.toReal⌋₊) hEq)

/-- Summable intensity approximation gives actual eventual equality of
natural counts almost surely, by the proved discrepancy bound and Borel-Cantelli. -/
theorem ae_eventually_count_eq (j : J) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S)
    (Sₙ : ℕ → Set (ℝ × ℝ)) (hSₙ : ∀ n, MeasurableSet (Sₙ n))
    (hsum : (∑' n, (positiveVolume.prod positiveVolume) (Sₙ n ∆ S)) ≠ ∞) :
    ∀ᵐ ω ∂law J, ∀ᶠ n in atTop, count j (Sₙ n) ω = count j S ω := by
  have hne : (∑' n, (law J) {ω | count j (Sₙ n) ω ≠ count j S ω}) ≠ ∞ :=
    ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum (fun n =>
      measure_count_ne_le j (Sₙ n) S (hSₙ n) hS))
  simpa only [mem_setOf_eq, not_not] using ae_eventually_not_mem hne

/-- The eventual agreement is simultaneous over every finite vector of
measurable sets. This is the input needed for multivariate law limits. -/
theorem ae_eventually_countVector_eq {ι : Type*} [Fintype ι]
    (j : J) (S : ι → Set (ℝ × ℝ)) (hS : ∀ i, MeasurableSet (S i))
    (Sₙ : ℕ → ι → Set (ℝ × ℝ)) (hSₙ : ∀ n i, MeasurableSet (Sₙ n i))
    (hsum : ∀ i, (∑' n, (positiveVolume.prod positiveVolume) (Sₙ n i ∆ S i)) ≠ ∞) :
    ∀ᵐ ω ∂law J, ∀ᶠ n in atTop,
      (fun i => count j (Sₙ n i) ω) = (fun i => count j (S i) ω) := by
  have h (i : ι) := ae_eventually_count_eq j (S i) (hS i)
    (fun n => Sₙ n i) (fun n => hSₙ n i) (hsum i)
  filter_upwards [ae_all_iff.mpr h] with ω hω
  filter_upwards [eventually_all.mpr hω] with n hn
  exact funext hn

end CarryingCapacity.MarkedSetCounts
