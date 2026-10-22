import CarryingCapacity.SynchronousStoppedRunningSupremum

/-!
# Removing localization from an expected running-supremum estimate

Exhausting exit times leave the entire finite-horizon path unchanged eventually.
Fatou then transfers the proved localized comparison to the genuine running
supremum. Its integrability follows from a finite bound on the initial cost and
integrated activity; it is not a premise of the comparison.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical Topology ENNReal NNReal

namespace CarryingCapacity.StoppedComparisonLocalization
open SynchronousRunningSupremum SynchronousStoppedRunningSupremum CommonFrozenExit

/-- A cutoff beyond the horizon leaves the supremum over every real time
unchanged, including the terminal time. -/
theorem intervalSup_stopped_eq (f : ℝ → ℝ≥0∞) (T : ℝ≥0) (σ : ℝ≥0∞)
    (hσ : (T : ℝ≥0∞) ≤ σ) :
    intervalSup (stopped σ f) T = intervalSup f T := by
  unfold intervalSup
  apply iSup_congr
  intro t
  apply stopped_eq_of_le σ f t t.property.1
  exact (ENNReal.ofReal_le_ofReal t.property.2).trans
    (by simpa only [ENNReal.ofReal_coe_nnreal] using hσ)

/-- Monotone exhausting cutoffs give eventual equality of whole-horizon
suprema. No measurability or stopping-time assumption is needed for this
deterministic fact. -/
theorem eventually_intervalSup_stopped_eq (f : ℝ → ℝ≥0∞) (T : ℝ≥0)
    (σ : ℕ → ℝ≥0∞) (hmono : Monotone σ)
    (hexhaust : ∀ S : ℝ≥0, ∃ n, (S : ℝ≥0∞) < σ n) :
    ∀ᶠ n in atTop, intervalSup (stopped (σ n) f) T = intervalSup f T := by
  obtain ⟨n,hn⟩ := hexhaust T
  filter_upwards [eventually_ge_atTop n] with m hm
  exact intervalSup_stopped_eq f T (σ m) (hn.le.trans (hmono hm))

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- Actual exhausting samplewise exits give almost-sure convergence of the
whole-horizon stopped suprema to the unrestricted supremum. -/
theorem ae_tendsto_intervalSup_stopped (f : Ω → ℝ → ℝ≥0∞) (T : ℝ≥0)
    (σ : ℕ → Ω → ℝ≥0∞)
    (hmono : ∀ᵐ ω ∂P, Monotone (fun n => σ n ω))
    (hexhaust : ∀ᵐ ω ∂P, ∀ S : ℝ≥0, ∃ n, (S : ℝ≥0∞) < σ n ω) :
    ∀ᵐ ω ∂P, Tendsto (fun n => intervalSup (stopped (σ n ω) (f ω)) T)
      atTop (𝓝 (intervalSup (f ω) T)) := by
  filter_upwards [hmono,hexhaust] with ω hm he
  apply tendsto_const_nhds.congr'
  exact (eventually_intervalSup_stopped_eq (f ω) T (fun n => σ n ω) hm he).mono
    (fun _ h => h.symm)

/-- A uniform extended expectation bound survives almost-sure convergence
of nonnegative localized costs, by Fatou. -/
theorem lintegral_le_of_ae_tendsto (S : Ω → ℝ≥0∞) (Sn : ℕ → Ω → ℝ≥0∞)
    (hm : ∀ n, AEMeasurable (Sn n) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Sn n ω) atTop (𝓝 (S ω)))
    (B : ℝ≥0∞) (hb : ∀ n, (∫⁻ ω, Sn n ω ∂P) ≤ B) :
    (∫⁻ ω, S ω ∂P) ≤ B := by
  have he : S =ᵐ[P] (fun ω => liminf (fun n => Sn n ω) atTop) :=
    hlim.mono (fun _ h => h.liminf_eq.symm)
  rw [lintegral_congr_ae he]
  refine (lintegral_liminf_le' hm).trans ?_
  exact liminf_le_of_frequently_le' (Eventually.of_forall hb).frequently

/-- Eventual path agreement is enough; no dominated convergence assumption
on the localized suprema is imposed. -/
theorem lintegral_le_of_ae_eventuallyEq (S : Ω → ℝ≥0∞) (Sn : ℕ → Ω → ℝ≥0∞)
    (hm : ∀ n, AEMeasurable (Sn n) P)
    (he : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, Sn n ω = S ω)
    (B : ℝ≥0∞) (hb : ∀ n, (∫⁻ ω, Sn n ω ∂P) ≤ B) :
    (∫⁻ ω, S ω ∂P) ≤ B := by
  apply lintegral_le_of_ae_tendsto P S Sn hm _ B hb
  filter_upwards [he] with ω hω
  exact tendsto_const_nhds.congr' (hω.mono (fun _ h => h.symm))

/-- Removing the localization indicator can only increase a nonnegative
activity integral. Combined with Fatou this proves the unlocalized estimate
from the actual localized estimates, even before finiteness is established. -/
theorem lintegral_le_of_localized_comparison
    (S : Ω → ℝ≥0∞) (Sn : ℕ → Ω → ℝ≥0∞)
    (hm : ∀ n, AEMeasurable (Sn n) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Sn n ω) atTop (𝓝 (S ω)))
    (σ : ℕ → Ω → ℝ≥0∞) (a : ℝ≥0∞) (A : Ω → ℝ → ℝ≥0∞)
    (μtime : Measure ℝ) (T : ℝ)
    (hb : ∀ n, (∫⁻ ω, Sn n ω ∂P) ≤ a +
      ∫⁻ ω, ∫⁻ s in Ioc 0 T, if ENNReal.ofReal s ≤ σ n ω then A ω s else 0 ∂μtime ∂P) :
    (∫⁻ ω, S ω ∂P) ≤ a + ∫⁻ ω, ∫⁻ s in Ioc 0 T, A ω s ∂μtime ∂P := by
  apply lintegral_le_of_ae_tendsto P S Sn hm hlim
  intro n
  refine (hb n).trans (add_le_add_left (lintegral_mono (fun ω => ?_)) a)
  apply lintegral_mono
  intro s
  dsimp only
  split_ifs
  · exact le_rfl
  · exact zero_le _

/-- Finite extended expectation bounds imply genuine real integrability
and retain the corresponding real expectation inequality. -/
theorem integrable_and_integral_le (S : Ω → ℝ≥0∞) (hS : AEMeasurable S P)
    (B : ℝ≥0∞) (hB : B ≠ ⊤) (hb : (∫⁻ ω, S ω ∂P) ≤ B) :
    Integrable (fun ω => (S ω).toReal) P ∧
      (∫ ω, (S ω).toReal ∂P) ≤ B.toReal := by
  have hfin := ne_top_of_le_ne_top hB hb
  refine ⟨integrable_toReal_of_lintegral_ne_top hS hfin, ?_⟩
  rw [integral_toReal hS (ae_lt_top' hS hfin)]
  exact ENNReal.toReal_mono hB hb

/-- The integrable-domination version of localization removal derives
measurability, almost-sure finiteness, integrability and the real bound for
the unrestricted cost from the localized inequalities. -/
theorem finite_comparison_of_localization
    (S : Ω → ℝ≥0∞) (Sn : ℕ → Ω → ℝ≥0∞)
    (hm : ∀ n, AEMeasurable (Sn n) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => Sn n ω) atTop (𝓝 (S ω)))
    (σ : ℕ → Ω → ℝ≥0∞) (a : ℝ≥0∞) (A : Ω → ℝ → ℝ≥0∞)
    (μtime : Measure ℝ) (T : ℝ) (ha : a ≠ ⊤)
    (hA : (∫⁻ ω, ∫⁻ s in Ioc 0 T, A ω s ∂μtime ∂P) ≠ ⊤)
    (hb : ∀ n, (∫⁻ ω, Sn n ω ∂P) ≤ a +
      ∫⁻ ω, ∫⁻ s in Ioc 0 T, if ENNReal.ofReal s ≤ σ n ω then A ω s else 0 ∂μtime ∂P) :
    AEMeasurable S P ∧ (∀ᵐ ω ∂P, S ω < ⊤) ∧
      Integrable (fun ω => (S ω).toReal) P ∧
      (∫ ω, (S ω).toReal ∂P) ≤
        a.toReal + (∫⁻ ω, ∫⁻ s in Ioc 0 T, A ω s ∂μtime ∂P).toReal := by
  have hS : AEMeasurable S P := aemeasurable_of_tendsto_metrizable_ae' hm hlim
  have hbound := lintegral_le_of_localized_comparison P S Sn hm hlim σ a A μtime T hb
  have hfinite : a + (∫⁻ ω, ∫⁻ s in Ioc 0 T, A ω s ∂μtime ∂P) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ha,hA⟩
  have hi := integrable_and_integral_le P S hS _ hfinite hbound
  rw [ENNReal.toReal_add ha hA] at hi
  exact ⟨hS,ae_lt_top' hS (ne_top_of_le_ne_top hfinite hbound),hi⟩

end CarryingCapacity.StoppedComparisonLocalization
