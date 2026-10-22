import CarryingCapacity.InitialPredictableIntegral
import Mathlib.Probability.ConditionalExpectation

/-!
# Conditional compensation on the actual initial-noise history

Multiplying a predictable future-window integrand by a past event preserves
predictability. The proved signed compensation identity therefore holds on
every past-measurable event. Conditional-expectation uniqueness gives zero
conditional mean for the actual compensated counting integral on that window.
No conditional compensation or martingale identity is an input assumption.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace CarryingCapacity.InitialConditionalCompensation
open CommonInitialNoise InitialPredictableCompensation InitialPredictableIntegral
  PredictableSets MarkedIntensity

variable {A J : Type*} [MeasurableSpace A]
local instance : SigmaFinite positiveVolume := positiveVolume_spanning.sigmaFinite

/-- A deterministic future-window restriction of a marked integrand. -/
def window (f : SamplePoint A J → ℝ) (s t : ℝ) : SamplePoint A J → ℝ :=
  (rectangle univ s t univ).indicator f

theorem measurable_window (f : SamplePoint A J → ℝ)
    (hf : Measurable[predictable (filtration A J)] f) (s t : ℝ) (hs : 0 ≤ s) :
    Measurable[predictable (filtration A J)] (window f s t) :=
  hf.indicator (measurableSet_predictable_rectangle (filtration A J) s t hs
    univ MeasurableSet.univ univ MeasurableSet.univ)

/-- Actual counting integral minus its deterministic-intensity integral. -/
def compensatedWindow (j : J) (f : SamplePoint A J → ℝ) (s t : ℝ)
    (p : Sample A J) : ℝ :=
  (∫ q, window f s t (p,q) ∂MarkedNoise.countingMeasure j p.2) -
    ∫ q, window f s t (p,q) ∂positiveVolume.prod positiveVolume

omit [MeasurableSpace A] in
/-- Additivity of deterministic window restrictions. -/
theorem window_prefix_sub (f : SamplePoint A J → ℝ) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) : window f 0 t - window f 0 s = window f s t := by
  funext p
  simp only [Pi.sub_apply, window, rectangle, Set.indicator_apply, mem_prod,
    mem_univ, true_and, and_true, mem_Ioc]
  by_cases h0 : 0 < p.2.1
  · by_cases hp : p.2.1 ≤ s
    · have ht : p.2.1 ≤ t := hp.trans hst
      simp [h0, hp, ht, not_lt.mpr hp]
    · simp [h0, hp, lt_of_not_ge hp]
  · have hp : ¬ s < p.2.1 := not_lt.mpr ((not_lt.mp h0).trans hs)
    simp [h0, hp]

variable (μ : Measure A) [IsProbabilityMeasure μ]

theorem integrable_compensatedWindow (j : J) (f : SamplePoint A J → ℝ)
    (hf : Measurable[predictable (filtration A J)] f) (s t : ℝ) (hs : 0 ≤ s)
    (hi : Integrable (window f s t) (productIntensity μ J)) :
    Integrable (compensatedWindow j f s t) (law μ J) :=
  (integrable_counting_integral μ j _ (measurable_window f hf s t hs).stronglyMeasurable hi).sub
    hi.integral_prod_left

/-- Restricting to a history event preserves the actual signed compensation
identity for a later predictable window. -/
theorem setIntegral_counting_eq_intensity (j : J) (f : SamplePoint A J → ℝ)
    (hf : Measurable[predictable (filtration A J)] f) (s t : ℝ) (hs : 0 ≤ s)
    (hi : Integrable (window f s t) (productIntensity μ J))
    (B : Set (Sample A J)) (hB : MeasurableSet[filtration A J s] B) :
    (∫ p in B, ∫ q, window f s t (p,q) ∂MarkedNoise.countingMeasure j p.2 ∂law μ J) =
      ∫ p in B, ∫ q, window f s t (p,q) ∂positiveVolume.prod positiveVolume ∂law μ J := by
  let g : SamplePoint A J → ℝ := (rectangle B s t univ).indicator f
  have hg : Measurable[predictable (filtration A J)] g :=
    hf.indicator (measurableSet_predictable_rectangle (filtration A J) s t hs
      B hB univ MeasurableSet.univ)
  have hBa : MeasurableSet B := (filtration A J).le s B hB
  have he : g = (Prod.fst ⁻¹' B).indicator (window f s t) := by
    funext p
    rcases p with ⟨p, u, v⟩
    by_cases hb : p ∈ B <;> by_cases ht : u ∈ Ioc s t <;>
      simp [g, window, rectangle, Set.indicator_apply, hb, ht]
  have hgi : Integrable g (productIntensity μ J) := by
    rw [he]
    exact hi.indicator (hBa.preimage measurable_fst)
  have hc := compensation_integrable μ j g hg.stronglyMeasurable hgi
  have inner (ν : Sample A J → Measure (ℝ × ℝ)) :
      (fun p => ∫ q, g (p,q) ∂ν p) =
        B.indicator (fun p => ∫ q, window f s t (p,q) ∂ν p) := by
    funext p
    rw [he]
    by_cases hb : p ∈ B <;> simp [Set.indicator_apply, hb]
  rw [inner (fun p => MarkedNoise.countingMeasure j p.2),
    inner (fun _ => positiveVolume.prod positiveVolume),
    integral_indicator hBa, integral_indicator hBa] at hc
  exact hc

/-- The actual compensated predictable window has zero mean on every past event. -/
theorem setIntegral_compensatedWindow_eq_zero (j : J) (f : SamplePoint A J → ℝ)
    (hf : Measurable[predictable (filtration A J)] f) (s t : ℝ) (hs : 0 ≤ s)
    (hi : Integrable (window f s t) (productIntensity μ J))
    (B : Set (Sample A J)) (hB : MeasurableSet[filtration A J s] B) :
    (∫ p in B, compensatedWindow j f s t p ∂law μ J) = 0 := by
  simp only [compensatedWindow]
  rw [integral_sub
    (integrable_counting_integral μ j _ (measurable_window f hf s t hs).stronglyMeasurable hi).integrableOn
    hi.integral_prod_left.integrableOn,
    setIntegral_counting_eq_intensity μ j f hf s t hs hi B hB, sub_self]

/-- Conditional zero mean is derived from the actual compensation theorem
and past-event testing, rather than postulated for the integrator. -/
theorem conditional_compensatedWindow (j : J) (f : SamplePoint A J → ℝ)
    (hf : Measurable[predictable (filtration A J)] f) (s t : ℝ) (hs : 0 ≤ s)
    (hi : Integrable (window f s t) (productIntensity μ J)) :
    (law μ J)[compensatedWindow j f s t | filtration A J s] =ᵐ[law μ J]
      fun _ => (0 : ℝ) := by
  apply (ae_eq_condExp_of_forall_setIntegral_eq (g := fun _ => (0 : ℝ))
    ((filtration A J).le s) (integrable_compensatedWindow μ j f hf s t hs hi)
    (fun B _ _ => integrable_zero _ _ ((law μ J).restrict B)) ?_ stronglyMeasurable_const.aestronglyMeasurable).symm
  intro B hB _
  rw [integral_zero, setIntegral_compensatedWindow_eq_zero μ j f hf s t hs hi B hB]

omit [IsProbabilityMeasure μ] in
/-- Integrability on two prefixes implies integrability on their difference window. -/
theorem integrable_window_of_prefixes (f : SamplePoint A J → ℝ) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t)
    (his : Integrable (window f 0 s) (productIntensity μ J))
    (hit : Integrable (window f 0 t) (productIntensity μ J)) :
    Integrable (window f s t) (productIntensity μ J) := by
  rw [← window_prefix_sub f s t hs hst]
  exact hit.sub his

/-- Actual compensated prefix differences equal the corresponding future
window, with section integrability derived from predictable compensation. -/
theorem ae_compensated_prefix_sub (j : J) (f : SamplePoint A J → ℝ)
    (hf : Measurable[predictable (filtration A J)] f) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t)
    (his : Integrable (window f 0 s) (productIntensity μ J))
    (hit : Integrable (window f 0 t) (productIntensity μ J)) :
    (fun p => compensatedWindow j f 0 t p - compensatedWindow j f 0 s p) =ᵐ[law μ J]
      compensatedWindow j f s t := by
  filter_upwards [ae_integrable_counting μ j _ (measurable_window f hf 0 s le_rfl).stronglyMeasurable his,
    ae_integrable_counting μ j _ (measurable_window f hf 0 t le_rfl).stronglyMeasurable hit,
    his.prod_right_ae, hit.prod_right_ae] with p hcs hct his hit
  have he : (fun q => window f s t (p,q)) =
      (fun q => window f 0 t (p,q) - window f 0 s (p,q)) := by
    funext q
    exact (congrFun (window_prefix_sub f s t hs hst) (p,q)).symm
  simp only [compensatedWindow]
  rw [he, integral_sub hct hcs, integral_sub hit his]
  ring

end CarryingCapacity.InitialConditionalCompensation
