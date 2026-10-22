import CarryingCapacity.MarkedInfiniteIntensity
import CarryingCapacity.IndependentNoiseLabels

/-!
# Complete measurable-set laws of the constructed marked Poisson measures

Finite intensity gives the usual Poisson distribution embedded in extended
nonnegative reals; infinite intensity gives the point mass at infinity. Every
finite disjoint measurable family has the product of these distributions.
The full array law also holds simultaneously for any finite selection of
distinct noise labels, with disjointness required only within each label.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace CarryingCapacity.MarkedFullPoissonLaw
open MarkedNoise MarkedIntensity MarkedSetCounts MarkedSetPoissonLimit

/-- The extended Poisson count law, including an infinite intensity. -/
def massLaw (r : ℝ≥0∞) : Measure ℝ≥0∞ :=
  if r = ∞ then Measure.dirac ∞
  else Measure.map (fun n : ℕ => (n : ℝ≥0∞)) (poissonMeasure r.toNNReal)

instance massLaw_probability (r : ℝ≥0∞) : IsProbabilityMeasure (massLaw r) := by
  unfold massLaw
  split_ifs
  · infer_instance
  · exact MeasureTheory.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

variable {J ι : Type*} [Fintype ι]

/-- Every measurable set has its actual extended Poisson mass law. -/
theorem countingMeasure_set_map (j : J) (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) :
    Measure.map (fun ω : Sample J => countingMeasure j ω S) (law J) =
      massLaw ((positiveVolume.prod positiveVolume) S) := by
  by_cases hf : (positiveVolume.prod positiveVolume) S = ∞
  · simpa only [massLaw, hf, if_pos rfl] using
      MarkedInfiniteIntensity.countingMeasure_map_eq_dirac_top j S hS hf
  · simpa only [massLaw, hf, if_false] using
      MarkedPoissonMeasure.countingMeasure_set_map j S hS hf

/-- Joint independence of disjoint measurable set masses, with no finiteness
restriction. Infinite-intensity coordinates are proved almost-sure constants. -/
theorem independent_countingMeasure (j : J) (S : ι → Set (ℝ × ℝ))
    (hS : ∀ i, MeasurableSet (S i))
    (hdis : Pairwise (fun i k => Disjoint (S i) (S k))) :
    iIndepFun (fun i ω => countingMeasure j ω (S i)) (law J) := by
  classical
  let finitePart (i : ι) : Set (ℝ × ℝ) :=
    if (positiveVolume.prod positiveVolume) (S i) = ∞ then ∅ else S i
  have hsubset (i : ι) : finitePart i ⊆ S i := by
    dsimp only [finitePart]
    split_ifs <;> simp
  have hm (i : ι) : MeasurableSet (finitePart i) := by
    dsimp only [finitePart]
    split_ifs
    · exact MeasurableSet.empty
    · exact hS i
  have hf (i : ι) : (positiveVolume.prod positiveVolume) (finitePart i) ≠ ∞ := by
    dsimp only [finitePart]
    split_ifs with hi
    · simp
    · exact hi
  have hd : Pairwise (fun i k => Disjoint (finitePart i) (finitePart k)) :=
    fun i k hik => (hdis hik).mono (hsubset i) (hsubset k)
  let restore (i : ι) (x : ℝ≥0∞) : ℝ≥0∞ :=
    if (positiveVolume.prod positiveVolume) (S i) = ∞ then ∞ else x
  have hr (i : ι) : Measurable (restore i) := by
    dsimp only [restore]
    split_ifs
    · exact measurable_const
    · exact measurable_id
  have hi := (MarkedPoissonMeasure.independent_countingMeasure j finitePart hm hd hf).comp restore hr
  apply hi.congr
  intro i
  by_cases ht : (positiveVolume.prod positiveVolume) (S i) = ∞
  · filter_upwards [MarkedInfiniteIntensity.ae_countingMeasure_eq_top j (S i) (hS i) ht] with ω hω
    simp [Function.comp_def, restore, ht, hω]
  · exact Eventually.of_forall (fun ω => by simp [Function.comp_def, restore, finitePart, ht])

/-- Full product law of the genuine random-measure mass vector for arbitrary
disjoint measurable sets, allowing both finite and infinite intensities. -/
theorem countingMeasure_map (j : J) (S : ι → Set (ℝ × ℝ))
    (hS : ∀ i, MeasurableSet (S i))
    (hdis : Pairwise (fun i k => Disjoint (S i) (S k))) :
    Measure.map (fun ω : Sample J => fun i => countingMeasure j ω (S i)) (law J) =
      Measure.pi (fun i => massLaw ((positiveVolume.prod positiveVolume) (S i))) := by
  have hm (i : ι) : Measurable (fun ω : Sample J => countingMeasure j ω (S i)) :=
    (Measure.measurable_coe (hS i)).comp (measurable_countingMeasure j)
  have he := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hm i).aemeasurable)).mp
    (independent_countingMeasure j S hS hdis)
  simpa only [countingMeasure_set_map j _ (hS _)] using he

/-- Full mass-array law across distinct labels. Planar sets belonging to
different labels may overlap, and individual intensities may be infinite. -/
theorem countingMeasure_arrays_map {L : Type*} [Fintype L]
    (labels : L → J) (hlabels : Function.Injective labels)
    (S : L → ι → Set (ℝ × ℝ)) (hS : ∀ l i, MeasurableSet (S l i))
    (hdis : ∀ l, Pairwise (fun i k => Disjoint (S l i) (S l k))) :
    Measure.map (fun ω : Sample J => fun l i => countingMeasure (labels l) ω (S l i)) (law J) =
      Measure.pi (fun l => Measure.pi
        (fun i => massLaw ((positiveVolume.prod positiveVolume) (S l i)))) := by
  have hi := ((IndependentNoiseLabels.independent_countingMeasures J).precomp hlabels).comp
    (fun l ν => fun i => ν (S l i))
    (fun l => measurable_pi_lambda _ (fun i => Measure.measurable_coe (hS l i)))
  have hm (l : L) : Measurable (fun ω : Sample J => fun i => countingMeasure (labels l) ω (S l i)) :=
    measurable_pi_lambda _ (fun i =>
      (Measure.measurable_coe (hS l i)).comp (measurable_countingMeasure (labels l)))
  have he := (iIndepFun_iff_map_fun_eq_pi_map (fun l => (hm l).aemeasurable)).mp hi
  simpa only [countingMeasure_map _ _ (hS _) (hdis _)] using he

end CarryingCapacity.MarkedFullPoissonLaw
