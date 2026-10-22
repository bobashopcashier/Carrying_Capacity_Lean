import CarryingCapacity.PrescribedConfigurationEstimates

/-!
# The actual supplied-space exit event

The first exit is attained on every right-locally-constant path. The actual
supplied process has that regularity almost surely, so its crossing bound is
also the bound for `{τ_R ≤ T}`, with the initial and terminal times retained.
-/

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace CarryingCapacity.PrescribedConfigurationExit
open ConfigurationLocalization PrescribedConfigurationEstimates

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N) (initial : A → Configuration N D)
  (M : Label N D → Ω → Measure (ℝ × ℝ)) (ξ : Ω → A)
  (hinit : Measurable initial) (hM : ∀ j, Measurable (M j)) (hξ : Measurable ξ)
  (P : Measure Ω) [IsProbabilityMeasure P]
  (hPoisson : PoissonObservationLaw.HasDisjointLaws P (Label N D) M)
  (hIndependent : IndepFun ξ (fun ω j => M j ω) P)
  (hV : Integrable (fun a => lyapunov control (initial a)) (P.map ξ))

local notation "X" => PrescribedConfigurationProcess.process control hN initial M ξ
local notation "V" => (lyapunov control : Configuration N D → ℝ)

include hinit hM hξ hPoisson hIndependent hV

attribute [local irreducible] PrescribedPoissonRealization.record
attribute [local irreducible] PrescribedConfigurationProcess.process

theorem ae_right_constant : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
    ∃ b, t < b ∧ ∀ s ∈ Ico t b, X ω s = X ω t := by
  letI : IsProbabilityMeasure (P.map ξ) := isProbabilityMeasure_map hξ.aemeasurable
  filter_upwards [PrescribedConfigurationProcess.ae_cadlag control hN initial M ξ
    hinit hM hξ P hPoisson hIndependent (P.map ξ) rfl hV] with ω hω
  exact fun t ht => DiscreteCausalUniqueness.exists_right_constant _ t (hω.1 t ht)

/-- One probability-one event identifies all real thresholds and horizons. -/
theorem ae_firstExit_le_iff_crossing : ∀ᵐ ω ∂P, ∀ R T : ℝ, 0 ≤ T →
    (firstExit control hN initial M ξ R ω ≤ ENNReal.ofReal T ↔
      ω ∈ GlobalLyapunovExit.crossingEvent V X R T) := by
  filter_upwards [ae_right_constant control hN initial M ξ hinit hM hξ P
    hPoisson hIndependent hV] with ω hω
  intro R T hT
  simpa only [firstExit, GlobalLyapunovExit.firstExit, GlobalLyapunovExit.crossingEvent,
    mem_setOf_eq, not_lt] using
    ExitTimeMeasurability.exitTime_le_iff_exists {x | V x < R} (X ω) hω T hT

/-- Measurability of the original exit, retaining its definition on exceptional paths. -/
theorem aemeasurable_firstExit (R : ℝ) :
    AEMeasurable (firstExit control hN initial M ξ R) P := by
  have hproc : Measurable (fun p : Ω × ℝ => X p.1 p.2) :=
    PrescribedConfigurationProcess.measurable_process control hN initial M ξ hinit hM hξ
  have heval (t : ℝ) : Measurable (fun ω : Ω => X ω t) :=
    hproc.comp (show Measurable (fun ω : Ω => (ω, t)) from
      measurable_id.prodMk measurable_const)
  exact ExitTimeMeasurability.aemeasurable_exitTime (fun t ω => X ω t)
    (fun t _ => heval t)
    {x | V x < R} (measurableSet_lt (measurable_of_countable V) measurable_const) P
    (ae_right_constant control hN initial M ξ hinit hM hξ P hPoisson hIndependent hV)

/-- Equation (3.18) for the genuine first exit on the supplied probability space. -/
theorem firstExit_probability_le (R T : ℝ) (hR : 0 < R) (hT : 0 ≤ T) :
    P {ω | firstExit control hN initial M ξ R ω ≤ ENNReal.ofReal T} ≤
      ENNReal.ofReal (2 * ((1 + ∫ a, V (initial a) ∂P.map ξ) *
        Real.exp ((2 * driftConstant control) * T)) / R) := by
  have he : {ω | firstExit control hN initial M ξ R ω ≤ ENNReal.ofReal T}
      =ᵐ[P] GlobalLyapunovExit.crossingEvent V X R T := by
    filter_upwards [ae_firstExit_le_iff_crossing control hN initial M ξ hinit hM hξ P
      hPoisson hIndependent hV] with ω hω
    exact propext (hω R T hT)
  rw [measure_congr he]
  exact crossing_probability_le control hN initial M ξ hinit hM hξ P
    hPoisson hIndependent hV T hT R hR

end CarryingCapacity.PrescribedConfigurationExit
