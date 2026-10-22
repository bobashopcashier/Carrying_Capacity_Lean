import CarryingCapacity.PrescribedConfigurationProcess
import CarryingCapacity.PrescribedObservableLaws

/-!
# The actual frozen particle family on supplied Poisson measures

Level `n` means the paper's positive integer threshold `R = n + 1`.
Every level uses the same supplied initial record and Poisson measures.
The exits are the genuine first exits, and their stopping-time property uses
the completed right-continuous natural filtration of these supplied inputs.
All expectation and exit estimates are transported from the constructed
canonical paths using the proved input law, never supplied as hypotheses.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.PrescribedConfigurationLocalization
open ConfigurationLocalization PrescribedPoissonRealization

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N) (initial : A → Configuration N D)
  (M : Label N D → Ω → Measure (ℝ × ℝ)) (ξ : Ω → A)

/-- The actual frozen path, at the positive integer threshold `n + 1`. -/
def path (n : ℕ) (ω : Ω) (t : ℝ) : Configuration N D :=
  ConfigurationLocalization.path control hN initial n (record (Label N D) M ξ ω) t

/-- Its exact first exit, including infinity when no exit occurs. -/
def exit (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ConfigurationLocalization.exit control hN initial n (record (Label N D) M ξ ω)

omit [MeasurableSpace Ω] [MeasurableSpace A] in
theorem exit_eq_firstExit (n : ℕ) (ω : Ω) :
    exit control hN initial M ξ n ω =
      CommonFrozenExit.exitTime {z | lyapunov control z < (n : ℝ) + 1}
        (path control hN initial M ξ n ω) := by
  change CommonFrozenExit.exitTime (active control hN n : Set (Configuration N D)) _ = _
  congr 1
  ext z
  exact mem_active control hN n z

omit [MeasurableSpace Ω] [MeasurableSpace A] in
/-- The deterministic finite one-jump enlargement controls every active initial state. -/
theorem path_mem_enlargement (n : ℕ) (ω : Ω)
    (hactive : lyapunov control (initial (ξ ω)) < (n : ℝ) + 1) (t : ℝ) :
    path control hN initial M ξ n ω t ∈
      Freezing.oneStepEnlargement (active control hN n) jump := by
  obtain h | h := CommonInitialNoise.process_mem_or_eq_initial
    (active control hN n) jump (rate κ q hN) initial
    (rateBound control hN n) (record (Label N D) M ξ ω) t
  · exact h
  · rw [show path control hN initial M ξ n ω t = initial (ξ ω) from h]
    exact Freezing.active_subset_enlargement (active control hN n) jump
      ((mem_active control hN n _).mpr hactive)

omit [MeasurableSpace Ω] [MeasurableSpace A] in
/-- Initially inactive samples are constant, without a probabilistic exception. -/
theorem path_outside (n : ℕ) (ω : Ω)
    (hactive : (n : ℝ) + 1 ≤ lyapunov control (initial (ξ ω))) (t : ℝ) :
    path control hN initial M ξ n ω t = initial (ξ ω) :=
  CommonFrozenProcess.process_outside (active control hN n) jump (rate κ q hN)
    (rateBound control hN n) (by simpa only [mem_active, not_lt] using hactive) _ t

attribute [local irreducible] PrescribedPoissonRealization.record

theorem measurable_path (hinit : Measurable initial)
    (hM : ∀ j, Measurable (M j)) (hξ : Measurable ξ) (n : ℕ) :
    Measurable (fun p : Ω × ℝ => path control hN initial M ξ n p.1 p.2) := by
  have hc := LyapunovLocalization.measurable_path (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q hN) initial hinit n
  have hr : Measurable (fun p : Ω × ℝ => (record (Label N D) M ξ p.1,p.2)) :=
    (((measurable_record (Label N D) M ξ hM hξ).comp measurable_fst).prodMk measurable_snd)
  exact hc.comp hr

variable (P : Measure Ω) [IsProbabilityMeasure P]
  (hM : ∀ j, Measurable (M j)) (hPoisson : PoissonObservationLaw.HasDisjointLaws P (Label N D) M)
  (hξ : Measurable ξ) (hIndependent : IndepFun ξ (fun ω => fun j => M j ω) P)
include hM hPoisson hξ hIndependent

theorem adapted_path (hinit : Measurable initial) (n : ℕ) :
    Adapted (UsualFiltration.filtration P
      (PrescribedPoissonFiltration.rawFiltration (Label N D) M ξ hM hξ))
      (fun t ω => path control hN initial M ξ n ω t) := by
  intro t
  exact (PrescribedPoissonFiltration.measurable_realized_at (Label N D) M ξ P
    hM hPoisson hξ hIndependent _ t
    (LyapunovLocalization.measurable_path_at (lyapunov control) (finite_sublevel control hN)
      jump (rate κ q hN) initial hinit n t)).stronglyMeasurable

theorem exit_stopping (hinit : Measurable initial) (n : ℕ) :
    IsStoppingTime (UsualFiltration.extendedFiltration P
      (PrescribedPoissonFiltration.rawFiltration (Label N D) M ξ hM hξ))
      (exit control hN initial M ξ n) := by
  apply UsualFiltration.isStoppingTime_extended
  intro t ht
  exact PrescribedPoissonFiltration.measurable_record_completedHistories (Label N D) M ξ P
    hM hPoisson hξ hIndependent t
    (CommonInitialStopping.measurableSet_firstExit_le (P.map ξ)
      (active control hN n) jump (rate κ q hN) initial hinit (rateBound control hN n) ht)

theorem aemeasurable_exit (hinit : Measurable initial) (n : ℕ) :
    AEMeasurable (exit control hN initial M ξ n) P :=
  PrescribedObservableLaws.aemeasurable_comp (Label N D) M ξ P hM hPoisson hξ hIndependent _
    (LyapunovLocalization.aemeasurable_exit (lyapunov control) (finite_sublevel control hN)
      jump (rate κ q hN) initial (P.map ξ) hinit n)

theorem ae_initial (n : ℕ) : ∀ᵐ ω ∂P,
    path control hN initial M ξ n ω 0 = initial (ξ ω) := by
  have h := CommonInitialNoise.ae_process_zero (active control hN n) jump (rate κ q hN)
    initial (P.map ξ)
  filter_upwards [ae_record (Label N D) M ξ P hM hPoisson hξ hIndependent h] with ω hω
  have hh := hω (rateBound control hN n)
  have hf : (record (Label N D) M ξ ω).1 = ξ ω := by unfold record; rfl
  rw [hf] at hh
  exact hh

theorem ae_cadlag (n : ℕ) : ∀ᵐ ω ∂P,
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (path control hN initial M ξ n ω) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ z : Configuration N D,
      Tendsto (path control hN initial M ξ n ω) (𝓝[<] t) (𝓝 z)) := by
  have h := CommonInitialNoise.ae_process_cadlag (active control hN n) jump (rate κ q hN)
    initial (P.map ξ)
  filter_upwards [ae_record (Label N D) M ξ P hM hPoisson hξ hIndependent h] with ω hω
  exact hω (rateBound control hN n)

/-- All levels have monotone exits on one probability-one event. -/
theorem ae_exit_mono : ∀ᵐ ω ∂P, Monotone (fun n => exit control hN initial M ξ n ω) :=
  ae_record (Label N D) M ξ P hM hPoisson hξ hIndependent
    (ConfigurationLocalization.ae_exit_mono control hN initial (P.map ξ))

/-- The larger frozen path stopped at the smaller exact exit is the smaller path. -/
theorem ae_stopped_compatible : ∀ᵐ ω ∂P, ∀ n m : ℕ, n ≤ m → ∀ t : ℝ, 0 ≤ t →
    CommonFrozenExit.stopped (exit control hN initial M ξ n ω)
      (path control hN initial M ξ m ω) t = path control hN initial M ξ n ω t :=
  ae_record (Label N D) M ξ P hM hPoisson hξ hIndependent
    (LyapunovLocalization.ae_stopped_compatible (lyapunov control) (finite_sublevel control hN)
      jump (rate κ q hN) initial (P.map ξ))

/-- Freezing retains the exit jump and makes later stopping immaterial. -/
theorem ae_stopped_self : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t →
    CommonFrozenExit.stopped (exit control hN initial M ξ n ω)
      (path control hN initial M ξ n ω) t = path control hN initial M ξ n ω t := by
  filter_upwards [ae_stopped_compatible control hN initial M ξ P hM hPoisson hξ hIndependent]
    with ω hω
  exact fun n t ht => hω n n le_rfl t ht

/-- Compatibility holds through the first exit, including overshoots. -/
theorem ae_compatible : ∀ᵐ ω ∂P, ∀ n m : ℕ, n ≤ m → ∀ t : ℝ, 0 ≤ t →
    ENNReal.ofReal t ≤ exit control hN initial M ξ n ω →
      path control hN initial M ξ m ω t = path control hN initial M ξ n ω t :=
  ae_record (Label N D) M ξ P hM hPoisson hξ hIndependent
    (ConfigurationLocalization.ae_compatible control hN initial (P.map ξ))

section Estimates
variable (hinit : Measurable initial)
  (hV : Integrable (fun a => lyapunov control (initial a)) (P.map ξ))
include hinit hV

theorem integrable_path_lyapunov (n : ℕ) (t : ℝ) :
    Integrable (fun ω => lyapunov control (path control hN initial M ξ n ω t)) P := by
  letI : IsProbabilityMeasure (P.map ξ) := isProbabilityMeasure_map hξ.aemeasurable
  have hc := ActualNonexplosion.integrable_localized_value (lyapunov control)
    (finite_sublevel control hN) jump (rate κ q hN) initial 0 (P.map ξ) hinit hV n t
  have hp := measurePreserving_record (Label N D) M ξ P hM hPoisson hξ hIndependent
  exact (hp.integrable_comp hc.aestronglyMeasurable).mpr hc

/-- The actual frozen expectation obeys the explicit uniform exponential bound. -/
theorem expectation_le (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ ω, lyapunov control (path control hN initial M ξ n ω t) ∂P) ≤
      (1 + ∫ a, lyapunov control (initial a) ∂P.map ξ) *
        Real.exp ((2 * driftConstant control) * t) - 1 := by
  letI : IsProbabilityMeasure (P.map ξ) := isProbabilityMeasure_map hξ.aemeasurable
  have hi := ActualNonexplosion.integrable_localized_value (lyapunov control)
    (finite_sublevel control hN) jump (rate κ q hN) initial 0 (P.map ξ) hinit hV n t
  have hp := measurePreserving_record (Label N D) M ξ P hM hPoisson hξ hIndependent
  have he := integral_map hp.measurable.aemeasurable
    (show AEStronglyMeasurable
      (fun p => lyapunov control (ConfigurationLocalization.path control hN initial n p t))
      (P.map (record (Label N D) M ξ)) from hp.map_eq.symm ▸ hi.aestronglyMeasurable)
  rw [hp.map_eq] at he
  exact he.symm.trans_le (ActualNonexplosion.localized_expectation_le (lyapunov control)
    (finite_sublevel control hN) jump (rate κ q hN) initial 0 (P.map ξ) hinit
    (2 * driftConstant control) (mul_nonneg (by norm_num) (driftConstant_nonnegative control))
    (lyapunov_nonnegative control) (fun z j => rate_nonnegative κ q hN j z) hV
    (ConfigurationNonexplosion.generator_affine_bound control hN) n t ht)

/-- The same constant works simultaneously for every time in the selected horizon. -/
theorem expectation_le_on_horizon (n : ℕ) (T : ℝ) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    (∫ ω, lyapunov control (path control hN initial M ξ n ω t) ∂P) ≤
      Real.exp ((2 * driftConstant control) * T) *
        (1 + ∫ a, lyapunov control (initial a) ∂P.map ξ) := by
  have hv : 0 ≤ (∫ a, lyapunov control (initial a) ∂P.map ξ) :=
    integral_nonneg (fun a => lyapunov_nonnegative control (initial a))
  have he : Real.exp ((2 * driftConstant control) * t) ≤
      Real.exp ((2 * driftConstant control) * T) := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left htT (mul_nonneg (by norm_num) (driftConstant_nonnegative control)))
  have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ 1 +
    (∫ a, lyapunov control (initial a) ∂P.map ξ) by linarith)
  have hb := expectation_le control hN initial M ξ P hM hPoisson hξ hIndependent hinit hV n t ht
  nlinarith

/-- The genuine supplied-space first exit has the reciprocal Lyapunov tail bound. -/
theorem exit_probability_le (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    P {ω | exit control hN initial M ξ n ω ≤ ENNReal.ofReal T} ≤
      ENNReal.ofReal ((1 + ∫ a, lyapunov control (initial a) ∂P.map ξ) *
        Real.exp ((2 * driftConstant control) * T) - 1) / ((n + 1 : ℕ) : ℝ≥0∞) := by
  letI : IsProbabilityMeasure (P.map ξ) := isProbabilityMeasure_map hξ.aemeasurable
  have hm := LyapunovLocalization.aemeasurable_exit (lyapunov control) (finite_sublevel control hN)
    jump (rate κ q hN) initial (P.map ξ) hinit n
  have he := PrescribedObservableLaws.measure_preimage (Label N D) M ξ P hM hPoisson hξ
    hIndependent {p | ConfigurationLocalization.exit control hN initial n p ≤ ENNReal.ofReal T}
    (nullMeasurableSet_le hm aemeasurable_const)
  exact he.trans_le (ConfigurationNonexplosion.exit_probability_le control hN initial
    (P.map ξ) hinit hV n T hT)

theorem ae_exhaustive : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ n : ℕ,
    (T : ℝ≥0∞) < exit control hN initial M ξ n ω := by
  letI : IsProbabilityMeasure (P.map ξ) := isProbabilityMeasure_map hξ.aemeasurable
  exact ae_record (Label N D) M ξ P hM hPoisson hξ hIndependent
    (ConfigurationNonexplosion.ae_exhaustive control hN initial (P.map ξ) hinit hV)

/-- The prescribed global process is the actual patch of this frozen family. -/
theorem ae_agrees_on_horizon : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ n, ∀ m, n ≤ m →
    ∀ t : ℝ, 0 ≤ t → t ≤ T →
      PrescribedConfigurationProcess.process control hN initial M ξ ω t =
        path control hN initial M ξ m ω t := by
  letI : IsProbabilityMeasure (P.map ξ) := isProbabilityMeasure_map hξ.aemeasurable
  have hc := ae_record (Label N D) M ξ P hM hPoisson hξ hIndependent
    (ConfigurationNonexplosion.ae_agrees_on_horizon control hN initial (P.map ξ) hinit hV)
  filter_upwards [hc, PrescribedConfigurationProcess.ae_eq_autonomous control hN initial M ξ
    hinit hM hξ P hPoisson hIndependent (P.map ξ) rfl hV] with ω hω hEq
  intro T
  obtain ⟨n,hn⟩ := hω T
  exact ⟨n, fun m hm t ht htT => (hEq t ht).trans (hn m hm t ht htT)⟩

end Estimates
end CarryingCapacity.PrescribedConfigurationLocalization
