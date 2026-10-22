import CarryingCapacity.UsualFiltration
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Martingales in the usual natural filtration

Right continuity and an integrable bound on each compact time interval allow
a raw martingale to pass to the completed right-continuous filtration. The
proof uses equality of integrals over past events and dominated convergence;
adaptedness by itself is not used to infer preservation of the martingale.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace CarryingCapacity.UsualMartingale
open UsualFiltration

/-- Integral identities at times strictly after the observed past determine a
right-continuous, locally dominated martingale at the endpoint as well. -/
theorem martingale_of_right_integrals {S : Type*} [MeasurableSpace S]
    (Q : Measure S) [IsProbabilityMeasure Q] (U : Filtration ℝ≥0 ‹MeasurableSpace S›)
    (Y : ℝ≥0 → S → ℝ) (hadapt : Adapted U Y)
    (hint : ∀ t, Integrable (Y t) Q)
    (hright : ∀ᵐ ω ∂Q, ∀ s : ℝ≥0, ContinuousWithinAt (fun t => Y t ω) (Ici s) s)
    (hbound : ∀ T : ℝ≥0, ∃ b : S → ℝ, Integrable b Q ∧
      ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → ‖Y t ω‖ ≤ b ω)
    (hsets : ∀ (s u t : ℝ≥0), s < u → u ≤ t → ∀ B : Set S,
      MeasurableSet[U s] B → (∫ ω in B, Y u ω ∂Q) = ∫ ω in B, Y t ω ∂Q) :
    Martingale Y U Q := by
  refine ⟨hadapt, fun s t hst => ?_⟩
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (U.le s) (hint t)
    (fun B _ _ => (hint s).integrableOn) ?_ (hadapt s).aestronglyMeasurable
  intro B hB _
  rcases eq_or_lt_of_le hst with rfl | hst
  · rfl
  obtain ⟨b,hb,hdom⟩ := hbound t
  have hlim : Tendsto (fun u : ℝ≥0 => ∫ ω in B, Y u ω ∂Q)
      (𝓝[>] s) (𝓝 (∫ ω in B, Y s ω ∂Q)) := by
    apply tendsto_integral_filter_of_dominated_convergence b
      (Filter.Eventually.of_forall (fun u => (hint u).aestronglyMeasurable.restrict))
    · filter_upwards [show ∀ᶠ u : ℝ≥0 in 𝓝[>] s, u ≤ t from
        (eventually_le_nhds hst).filter_mono nhdsWithin_le_nhds] with u hu
      exact (ae_restrict_of_ae hdom).mono (fun ω hω => hω u hu)
    · exact hb.integrableOn
    · filter_upwards [ae_restrict_of_ae hright] with ω hω
      exact (hω s).mono Ioi_subset_Ici_self
  have heq : ∀ᶠ u : ℝ≥0 in 𝓝[>] s,
      (∫ ω in B, Y u ω ∂Q) = ∫ ω in B, Y t ω ∂Q := by
    filter_upwards [self_mem_nhdsWithin,
      show ∀ᶠ u : ℝ≥0 in 𝓝[>] s, u ≤ t from
        (eventually_le_nhds hst).filter_mono nhdsWithin_le_nhds] with u hsu hut
    exact hsets s u t hsu hut B hB
  exact tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (heq.mono (fun _ h => h.symm)))

variable {Ω : Type*} [m : MeasurableSpace Ω] (P : Measure Ω)

theorem trim_completedLaw :
    (completedLaw P).trim (show m ≤ completedSpace P from
      EventuallyMeasurableSpace.measurable_le) = P := by
  ext S hS
  rw [trim_measurableSet_eq _ hS]
  rfl

theorem integrable_completedLaw {f : Ω → ℝ} (hf : Integrable f P) :
    Integrable f (completedLaw P) := by
  apply integrable_of_integrable_trim (show m ≤ completedSpace P from
    EventuallyMeasurableSpace.measurable_le)
  rwa [trim_completedLaw]

theorem integral_completedLaw {f : Ω → ℝ} (hf : StronglyMeasurable f) :
    ∫ ω, f ω ∂completedLaw P = ∫ ω, f ω ∂P := by
  have h := integral_trim (μ := completedLaw P) (show m ≤ completedSpace P from
    EventuallyMeasurableSpace.measurable_le) hf
  rwa [trim_completedLaw P] at h

theorem setIntegral_completedLaw {f : Ω → ℝ} (hf : StronglyMeasurable f)
    {S : Set Ω} (hS : MeasurableSet S) :
    ∫ ω in S, f ω ∂completedLaw P = ∫ ω in S, f ω ∂P := by
  rw [← integral_indicator (show MeasurableSet[completedSpace P] S from
    EventuallyMeasurableSpace.measurable_le S hS), ← integral_indicator hS]
  exact integral_completedLaw P (hf.indicator hS)

variable (F : Filtration ℝ m)

/-- Restrict a real-time filtration to nonnegative times. -/
def nonnegative : Filtration ℝ≥0 m where
  seq t := F (t : ℝ)
  mono' := fun _ _ h => F.mono h
  le' t := F.le (t : ℝ)

/-- The usual augmented filtration at nonnegative times. -/
def usualNonnegative : Filtration ℝ≥0 (completedSpace P) where
  seq t := usualAt P F (t : ℝ)
  mono' := fun _ _ h => at_mono P F h
  le' t := at_le_completedSpace P F (t : ℝ)

variable [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → ℝ}
  (hX : Martingale X (nonnegative F) P)
include hX

theorem setIntegral_completedAt {s t : ℝ≥0} (hst : s ≤ t)
    {S : Set Ω} (hS : MeasurableSet[completedAt P F s] S) :
    ∫ ω in S, X s ω ∂completedLaw P = ∫ ω in S, X t ω ∂completedLaw P := by
  obtain ⟨B,hB,he⟩ := hS
  have he' : S =ᵐ[completedLaw P] B := he
  rw [setIntegral_congr_set he', setIntegral_congr_set he',
    setIntegral_completedLaw P ((hX.adapted s).mono (F.le s)) (F.le s B hB),
    setIntegral_completedLaw P ((hX.adapted t).mono (F.le t)) (F.le s B hB)]
  exact hX.setIntegral_eq hst hB

/-- A right-continuous raw martingale with integrable compact-time domination
is a martingale in the completed right-continuous augmentation. -/
theorem martingale_usual
    (hright : ∀ᵐ ω ∂P, ∀ s : ℝ≥0,
      ContinuousWithinAt (fun t => X t ω) (Ici s) s)
    (hbound : ∀ T : ℝ≥0, ∃ b : Ω → ℝ, Integrable b P ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T → ‖X t ω‖ ≤ b ω) :
    Martingale X (usualNonnegative P F) (completedLaw P) := by
  have hadapt : Adapted (usualNonnegative P F) X :=
    fun t => (hX.adapted t).mono (raw_le_usualAt P F t)
  have hint : ∀ t, Integrable (X t) (completedLaw P) :=
    fun t => integrable_completedLaw P (hX.integrable t)
  let Q := completedLaw P
  let U := usualNonnegative P F
  have hbQ : ∀ T : ℝ≥0, ∃ b : Ω → ℝ, Integrable b Q ∧
      ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → ‖X t ω‖ ≤ b ω := by
    intro T
    obtain ⟨b,hb,hd⟩ := hbound T
    exact ⟨b,integrable_completedLaw P hb,hd⟩
  have hrQ : ∀ᵐ ω ∂Q, ∀ s : ℝ≥0,
      ContinuousWithinAt (fun t => X t ω) (Ici s) s := hright
  have hsets : ∀ (s u t : ℝ≥0), s < u → u ≤ t → ∀ S : Set Ω,
      MeasurableSet[U s] S → (∫ ω in S, X u ω ∂Q) = ∫ ω in S, X t ω ∂Q := by
    intro s u t hsu hut S hS
    exact setIntegral_completedAt P F hX hut
      (at_le_completedAt P F (show (s : ℝ) < (u : ℝ) from hsu) S hS)
  letI : MeasurableSpace Ω := completedSpace P
  refine ⟨hadapt, fun s t hst => ?_⟩
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq
    (U.le s) (hint t)
    (fun S _ _ => (hint s).integrableOn) ?_ (hadapt s).aestronglyMeasurable
  intro S hS _
  rcases eq_or_lt_of_le hst with rfl | hst
  · rfl
  obtain ⟨b,hb,hdom⟩ := hbQ t
  have hlim : Tendsto (fun u : ℝ≥0 => ∫ ω in S, X u ω ∂Q)
      (𝓝[>] s) (𝓝 (∫ ω in S, X s ω ∂Q)) := by
    apply tendsto_integral_filter_of_dominated_convergence b
      (Filter.Eventually.of_forall (fun u => (hint u).aestronglyMeasurable.restrict))
    · filter_upwards [show ∀ᶠ u : ℝ≥0 in 𝓝[>] s, u ≤ t from
        (eventually_le_nhds hst).filter_mono nhdsWithin_le_nhds] with u hu
      exact (ae_restrict_of_ae hdom).mono (fun ω hω => hω u hu)
    · exact hb.integrableOn
    · filter_upwards [ae_restrict_of_ae hrQ] with ω hω
      exact (hω s).mono (Ioi_subset_Ici_self)
  have heq : ∀ᶠ u : ℝ≥0 in 𝓝[>] s,
      (∫ ω in S, X u ω ∂Q) = ∫ ω in S, X t ω ∂Q := by
    filter_upwards [self_mem_nhdsWithin,
      show ∀ᶠ u : ℝ≥0 in 𝓝[>] s, u ≤ t from
        (eventually_le_nhds hst).filter_mono nhdsWithin_le_nhds] with u hsu hut
    exact hsets s u t hsu hut S hS
  exact tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (heq.mono (fun _ h => h.symm)))

end CarryingCapacity.UsualMartingale
