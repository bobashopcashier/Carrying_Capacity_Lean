import CarryingCapacity.CommonInitialStopping
import CarryingCapacity.Freezing

/-!
# Lyapunov exit bounds for the actual initialized frozen process

The exact first-exit event agrees almost surely with the frozen state lying
outside its active sublevel. Markov's inequality therefore bounds this actual
exit probability by the expectation of the nonnegative Lyapunov function.
Uniform finite-horizon expectation bounds then give almost-sure exhaustion.
No exit estimate, non-explosion, or stopping identity is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace CarryingCapacity.InitialLyapunovExit
open CommonInitialNoise

variable {A E J : Type*} [MeasurableSpace A] [DecidableEq E] [Fintype J]

/-- The actual exit event is the Lyapunov threshold event, including initial
states which already lie outside the active region. No raw measurability of
the exact exit functional is asserted or needed for this outer-measure identity. -/
theorem measure_firstExit_eq_threshold (μ : Measure A)
    (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ) (initial : A → E)
    (V : E → ℝ) (R C T : ℝ) (hT : 0 ≤ T)
    (hactive : ∀ x, x ∈ active ↔ V x < R) :
    (law μ J) {p | firstExit active jump rate initial C p ≤ ENNReal.ofReal T} =
      (law μ J) {p | R ≤ V (process active jump rate initial C p T)} := by
  apply measure_congr
  filter_upwards [CommonInitialStopping.ae_firstExit_le_iff_outside
    μ active jump rate initial] with p hp
  apply propext
  change (firstExit active jump rate initial C p ≤ ENNReal.ofReal T) ↔
    R ≤ V (process active jump rate initial C p T)
  exact (hp C T hT).trans (by simp only [hactive, not_lt])

/-- Markov's inequality for the genuine first exit of the actual frozen path.
Only terminal-value integrability is input; the exit event identity is derived. -/
theorem measure_firstExit_le (μ : Measure A)
    (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ) (initial : A → E)
    (V : E → ℝ) (hV : ∀ x, 0 ≤ V x) (R C T : ℝ) (hR : 0 < R) (hT : 0 ≤ T)
    (hactive : ∀ x, x ∈ active ↔ V x < R)
    (hi : Integrable (fun p => V (process active jump rate initial C p T)) (law μ J)) :
    (law μ J) {p | firstExit active jump rate initial C p ≤ ENNReal.ofReal T} ≤
      ENNReal.ofReal (∫ p, V (process active jump rate initial C p T) ∂law μ J) /
        ENNReal.ofReal R := by
  rw [measure_firstExit_eq_threshold μ active jump rate initial V R C T hT hactive]
  have he : {p : Sample A J | R ≤ V (process active jump rate initial C p T)} =
      {p | ENNReal.ofReal R ≤ ENNReal.ofReal (V (process active jump rate initial C p T))} := by
    ext p
    exact (ENNReal.ofReal_le_ofReal_iff (hV _)).symm
  rw [he, ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun p => hV _))]
  exact meas_ge_le_lintegral_div hi.aemeasurable.ennreal_ofReal
    (ne_of_gt (ENNReal.ofReal_pos.mpr hR)) ENNReal.ofReal_ne_top

/-- Any separately proved terminal expectation bound supplies a concrete
finite-horizon bound for the actual first exit. -/
theorem measure_firstExit_le_of_expectation_le (μ : Measure A)
    (active : Finset E) (jump : J → E → E) (rate : J → E → ℝ) (initial : A → E)
    (V : E → ℝ) (hV : ∀ x, 0 ≤ V x) (R C T B : ℝ) (hR : 0 < R) (hT : 0 ≤ T)
    (hactive : ∀ x, x ∈ active ↔ V x < R)
    (hi : Integrable (fun p => V (process active jump rate initial C p T)) (law μ J))
    (hmean : (∫ p, V (process active jump rate initial C p T) ∂law μ J) ≤ B) :
    (law μ J) {p | firstExit active jump rate initial C p ≤ ENNReal.ofReal T} ≤
      ENNReal.ofReal B / ENNReal.ofReal R :=
  (measure_firstExit_le μ active jump rate initial V hV R C T hR hT hactive hi).trans
    (ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal hmean) _)

/-- Level-uniform expectation bounds at integer horizons imply that actual
first exits of the sublevel-frozen constructions exhaust every finite horizon.
Monotonicity and compatibility are proved separately from the common noise. -/
theorem ae_exhaustive_of_expectation_bounds (μ : Measure A)
    (active : ℕ → Finset E) (jump : J → E → E) (rate : J → E → ℝ)
    (initial : A → E) (cutoff : ℕ → ℝ) (V : E → ℝ) (hV : ∀ x, 0 ≤ V x)
    (hactive : ∀ n x, x ∈ active n ↔ V x < ((n + 1 : ℕ) : ℝ))
    (B : ℕ → ℝ)
    (hi : ∀ n k : ℕ, Integrable
      (fun p => V (process (active n) jump rate initial (cutoff n) p k)) (law μ J))
    (hmean : ∀ n k : ℕ,
      (∫ p, V (process (active n) jump rate initial (cutoff n) p k) ∂law μ J) ≤ B k) :
    ∀ᵐ p ∂law μ J, ∀ T : ℝ≥0, ∃ n : ℕ,
      (T : ℝ≥0∞) < firstExit (active n) jump rate initial (cutoff n) p := by
  apply Freezing.ae_exhaustive_of_reciprocal_bounds (law μ J)
    (fun n => firstExit (active n) jump rate initial (cutoff n))
    (fun k => ENNReal.ofReal (B k)) (fun _ => ENNReal.ofReal_ne_top)
  intro k n
  simpa only [ENNReal.ofReal_natCast] using
    measure_firstExit_le_of_expectation_le μ (active n) jump rate initial V hV
      ((n + 1 : ℕ) : ℝ) (cutoff n) (k : ℝ) (B k)
      (by positivity) (Nat.cast_nonneg k) (hactive n) (hi n k) (hmean n k)

end CarryingCapacity.InitialLyapunovExit
