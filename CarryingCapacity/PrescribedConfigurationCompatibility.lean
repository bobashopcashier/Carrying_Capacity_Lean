import CarryingCapacity.PrescribedConfigurationLocalization
import CarryingCapacity.PredictableExitMask

/-!
# Exact first-exit compatibility on the supplied space

The larger frozen system reaches every smaller threshold at exactly the
smaller system's own first exit. The supplied global process stopped there
equals the actual smaller frozen path, including the crossing jump.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal Topology

namespace CarryingCapacity.PrescribedConfigurationCompatibility
open CommonFrozenExit ConfigurationLocalization PrescribedPoissonRealization
  PrescribedConfigurationLocalization

/-- Agreement through an attained first exit identifies the genuine first-exit infima. -/
theorem exitTime_eq_of_agrees {E : Type*} (S : Set E) (f g : ℝ → E)
    (hattained : exitTime S f ≠ ⊤ → f (exitTime S f).toReal ∉ S)
    (heq : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t ≤ exitTime S f → g t = f t) :
    exitTime S g = exitTime S f := by
  apply le_antisymm
  · by_cases htop : exitTime S f = ⊤
    · rw [htop]
      exact le_top
    · have hh := hattained htop
      rw [← heq (exitTime S f).toReal ENNReal.toReal_nonneg
        (by rw [ENNReal.ofReal_toReal htop])] at hh
      have hb := exitTime_le_of_not_mem S g ENNReal.toReal_nonneg hh
      rwa [ENNReal.ofReal_toReal htop] at hb
  · by_cases htop : exitTime S f = ⊤
    · rw [htop]
      apply le_of_eq
      symm
      apply (exitTime_eq_top_iff_forall_mem S g).mpr
      intro t ht
      rw [heq t ht (by rw [htop]; exact le_top)]
      exact (exitTime_eq_top_iff_forall_mem S f).mp htop t ht
    · rw [← ENNReal.ofReal_toReal htop]
      apply (PredictableExitMask.le_exitTime_iff_before_mem S g _).mpr
      intro t ht hlt
      have hbefore : ENNReal.ofReal t < exitTime S f := by
        rw [← ENNReal.ofReal_toReal htop]
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht).mpr hlt
      rw [heq t ht hbefore.le]
      exact mem_before_exit S f ht hbefore

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N) (initial : A → Configuration N D)
  (M : Label N D → Ω → Measure (ℝ × ℝ)) (ξ : Ω → A)
  (P : Measure Ω) [IsProbabilityMeasure P]
  (hM : ∀ j, Measurable (M j)) (hPoisson : PoissonObservationLaw.HasDisjointLaws P (Label N D) M)
  (hξ : Measurable ξ) (hIndependent : IndepFun ξ (fun ω => fun j => M j ω) P)
include hM hPoisson hξ hIndependent

theorem ae_exit_attained : ∀ᵐ ω ∂P, ∀ n : ℕ,
    exit control hN initial M ξ n ω ≠ ⊤ →
      (n : ℝ) + 1 ≤ lyapunov control
        (path control hN initial M ξ n ω (exit control hN initial M ξ n ω).toReal) := by
  have hc : ∀ n : ℕ, ∀ᵐ p ∂CommonInitialNoise.law (P.map ξ) (Label N D),
      ConfigurationLocalization.exit control hN initial n p ≠ ⊤ →
      ConfigurationLocalization.path control hN initial n p
        (ConfigurationLocalization.exit control hN initial n p).toReal ∉ active control hN n := by
    intro n
    filter_upwards [CommonInitialNoise.ae_noise (P.map ξ)
      (CommonFrozenExit.ae_firstExit_attained (active control hN n) jump (rate κ q hN))]
      with p hp
    exact hp (rateBound control hN n) (initial p.1)
  filter_upwards [ae_record (Label N D) M ξ P hM hPoisson hξ hIndependent
    (ae_all_iff.mpr hc)] with ω hω
  intro n hn
  simpa only [mem_active, not_lt] using hω n hn

/-- The larger frozen process reaches the smaller level at precisely the same time. -/
theorem ae_lower_exit_eq : ∀ᵐ ω ∂P, ∀ n m : ℕ, n ≤ m →
    exitTime {z | lyapunov control z < (n : ℝ) + 1}
      (path control hN initial M ξ m ω) = exit control hN initial M ξ n ω := by
  filter_upwards [ae_exit_attained control hN initial M ξ P hM hPoisson hξ hIndependent,
    ae_compatible control hN initial M ξ P hM hPoisson hξ hIndependent] with ω hatt hcomp
  intro n m hnm
  rw [exit_eq_firstExit]
  apply exitTime_eq_of_agrees
  · intro hfin
    have hf : exit control hN initial M ξ n ω ≠ ⊤ := by
      rwa [exit_eq_firstExit]
    simpa only [exit_eq_firstExit] using not_lt.mpr (hatt n hf)
  · intro t ht hbefore
    apply hcomp n m hnm t ht
    rwa [exit_eq_firstExit]

/-- This is the exact pair of stopped-path equalities displayed in the manuscript. -/
theorem ae_stopped_compatibility : ∀ᵐ ω ∂P, ∀ n m : ℕ, n ≤ m → ∀ t : ℝ, 0 ≤ t →
    stopped (exitTime {z | lyapunov control z < (n : ℝ) + 1}
      (path control hN initial M ξ m ω)) (path control hN initial M ξ m ω) t =
        stopped (exit control hN initial M ξ n ω) (path control hN initial M ξ n ω) t ∧
    stopped (exit control hN initial M ξ n ω) (path control hN initial M ξ n ω) t =
      path control hN initial M ξ n ω t := by
  filter_upwards [ae_lower_exit_eq control hN initial M ξ P hM hPoisson hξ hIndependent,
    ae_stopped_compatible control hN initial M ξ P hM hPoisson hξ hIndependent]
    with ω hex hcomp
  intro n m hnm t ht
  have hself := hcomp n n le_rfl t ht
  refine ⟨?_,hself⟩
  rw [hex n m hnm,hself]
  exact hcomp n m hnm t ht

variable (hinit : Measurable initial)
  (hV : Integrable (fun a => lyapunov control (initial a)) (P.map ξ))
include hinit hV

/-- The global supplied path stopped at the actual localization exit is the frozen path. -/
theorem ae_global_stopped_eq : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
    stopped (exit control hN initial M ξ n ω)
      (PrescribedConfigurationProcess.process control hN initial M ξ ω) t =
        path control hN initial M ξ n ω t := by
  filter_upwards [ae_agrees_on_horizon control hN initial M ξ P hM hPoisson hξ hIndependent hinit hV,
    ae_stopped_compatible control hN initial M ξ P hM hPoisson hξ hIndependent]
    with ω hglobal hcomp
  intro n t ht
  obtain ⟨k,hk⟩ := hglobal ⟨t,ht⟩
  have hs := hcomp n (max n k) (le_max_left _ _) t ht
  rw [← hs]
  unfold stopped
  split_ifs
  · exact hk (max n k) (le_max_right _ _) t ht le_rfl
  · exact hk (max n k) (le_max_right _ _) _
      (le_min ht ENNReal.toReal_nonneg) (min_le_left _ _)

/-- The genuine global integer-level exit is exactly the frozen exit. This
identifies the manuscript's `τ_R` and `σ_R`, including the overshooting jump. -/
theorem ae_global_exit_eq : ∀ᵐ ω ∂P, ∀ n : ℕ,
    exitTime {z | lyapunov control z < (n : ℝ) + 1}
      (PrescribedConfigurationProcess.process control hN initial M ξ ω) =
        exit control hN initial M ξ n ω := by
  filter_upwards [ae_exit_attained control hN initial M ξ P hM hPoisson hξ hIndependent,
    ae_global_stopped_eq control hN initial M ξ P hM hPoisson hξ hIndependent hinit hV]
    with ω hatt hglobal
  intro n
  rw [exit_eq_firstExit]
  apply exitTime_eq_of_agrees
  · intro hfin
    have hf : exit control hN initial M ξ n ω ≠ ⊤ := by
      rwa [exit_eq_firstExit]
    simpa only [exit_eq_firstExit] using not_lt.mpr (hatt n hf)
  · intro t ht hbefore
    have hs := hglobal n t ht
    have hb : ENNReal.ofReal t ≤ exit control hN initial M ξ n ω := by
      rwa [exit_eq_firstExit]
    by_cases htop : exit control hN initial M ξ n ω = ⊤
    · simpa only [stopped,htop,if_true] using hs
    · have htσ : t ≤ (exit control hN initial M ξ n ω).toReal := by
        simpa only [ENNReal.toReal_ofReal ht] using ENNReal.toReal_mono htop hb
      simpa only [stopped,htop,if_false,min_eq_left htσ] using hs

end CarryingCapacity.PrescribedConfigurationCompatibility
