import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Independence after augmentation by ambient null sets

The augmentation uses the almost-everywhere filter of the given ambient
measure, not the measure trimmed to the smaller sigma algebra. Each augmented
event agrees almost everywhere with an original event, so the independence
identity extends without changing the measure or the random variables.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter

namespace CarryingCapacity.NullAugmentedIndependence

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {H K : MeasurableSpace Ω}

/-- Augment a sigma algebra by all null sets of the specified ambient measure. -/
def augmentation (H : MeasurableSpace Ω) (μ : @Measure Ω mΩ) : MeasurableSpace Ω :=
  EventuallyMeasurableSpace H (ae μ)

theorem le_augmentation (H : MeasurableSpace Ω) (μ : @Measure Ω mΩ) :
    H ≤ augmentation H μ := EventuallyMeasurableSpace.measurable_le

theorem measurableSet_augmentation_iff (H : MeasurableSpace Ω) (μ : @Measure Ω mΩ)
    (s : Set Ω) : MeasurableSet[augmentation H μ] s ↔
      ∃ t, MeasurableSet[H] t ∧ s =ᵐ[μ] t := Iff.rfl

/-- An augmented history remains a sub-sigma algebra of the completed ambient space. -/
theorem augmentation_le_completedSpace (hH : H ≤ mΩ) :
    augmentation H μ ≤ EventuallyMeasurableSpace mΩ (ae μ) := by
  rintro s ⟨t, ht, hst⟩
  exact ⟨t, hH _ ht, hst⟩

/-- Left augmentation preserves the exact independence identity for the original measure. -/
theorem indep_augment_left (h : Indep H K μ) : Indep (augmentation H μ) K μ := by
  apply (Indep_iff _ _ _).mpr
  rintro s t ⟨s', hs', hss'⟩ ht
  have hinter : (s ∩ t : Set Ω) =ᵐ[μ] (s' ∩ t : Set Ω) := by
    filter_upwards [hss'] with ω hω
    exact congrArg (fun p : Prop => p ∧ t ω) hω
  calc
    μ (s ∩ t) = μ (s' ∩ t) := measure_congr hinter
    _ = μ s' * μ t := (Indep_iff _ _ _).mp h s' t hs' ht
    _ = μ s * μ t := by rw [measure_congr hss']

theorem indep_augment_right (h : Indep H K μ) : Indep H (augmentation K μ) μ :=
  (indep_augment_left h.symm).symm

/-- Both independent sigma algebras may contain all ambient null sets. -/
theorem indep_augment_both (h : Indep H K μ) :
    Indep (augmentation H μ) (augmentation K μ) μ :=
  indep_augment_right (indep_augment_left h)

theorem indep_augment_left_iff : Indep (augmentation H μ) K μ ↔ Indep H K μ :=
  ⟨fun h => indep_of_indep_of_le_left h (le_augmentation H μ), indep_augment_left⟩

theorem indep_augment_both_iff :
    Indep (augmentation H μ) (augmentation K μ) μ ↔ Indep H K μ := by
  constructor
  · intro h
    exact indep_of_indep_of_le_right
      (indep_of_indep_of_le_left h (le_augmentation H μ)) (le_augmentation K μ)
  · exact indep_augment_both

/-- Passing to the actual completion does not alter any independence identity. -/
theorem indep_completion_iff : Indep H K μ.completion ↔ Indep H K μ := by
  rw [Indep_iff, Indep_iff]
  rfl

theorem indep_augment_both_completion (h : Indep H K μ) :
    Indep (augmentation H μ) (augmentation K μ) μ.completion :=
  indep_completion_iff.mpr (indep_augment_both h)

/-- Functions measurable in augmented independent histories are independent,
with their original values on every sample. -/
theorem indepFun_of_measurable_augments {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {f : Ω → A} {g : Ω → B}
    (h : Indep H K μ) (hf : Measurable[augmentation H μ] f)
    (hg : Measurable[augmentation K μ] g) : IndepFun f g μ := by
  change Indep _ _ μ
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left (indep_augment_both h) hf.comap_le) hg.comap_le

theorem indepFun_of_measurable_augment_left {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {f : Ω → A} {g : Ω → B}
    (h : Indep H K μ) (hf : Measurable[augmentation H μ] f)
    (hg : Measurable[K] g) : IndepFun f g μ :=
  indepFun_of_measurable_augments h hf (hg.mono (le_augmentation K μ) le_rfl)

end CarryingCapacity.NullAugmentedIndependence
