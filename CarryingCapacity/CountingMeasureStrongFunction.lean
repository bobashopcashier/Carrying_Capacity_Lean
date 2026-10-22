import CarryingCapacity.MarkedNoiseObservation
import CarryingCapacity.TimeDependentGlobalProcess

/-!
# The actual process as a measurable function of initial data and counting measures

The decoder is a proved measurable inverse of actual count observations on a
canonical probability-one event. Composing the existing jointly measurable
process with it removes any dependence on hidden clock/mark coordinates.
This file establishes the global strong-function factorization. It does not
yet transfer Poisson laws on an arbitrary space or identify time-local natural
filtrations; those require separate law and causal reconstruction arguments.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace CarryingCapacity.CountingMeasureStrongFunction
open MarkedNoiseObservation

variable (J : Type*) [Countable J]

abbrev MeasureFamily := J → Measure (ℝ × ℝ)

/-- Recover the canonical records using only the supplied counting-measure family. -/
def noiseFromMeasures (M : MeasureFamily J) : MarkedNoise.Sample J :=
  decode J (observeMeasures J M)

theorem measurable_noiseFromMeasures : Measurable (noiseFromMeasures J) :=
  (measurable_decode J).comp (measurable_observeMeasures J)

theorem ae_noiseFromMeasures : ∀ᵐ ω ∂MarkedNoise.law J,
    noiseFromMeasures J (fun j => MarkedNoise.countingMeasure j ω) = ω :=
  ae_decode_observe J

/-- No random input beyond the initial record and actual counting measures. -/
def realizePath {A E : Type*} (X : CommonInitialNoise.Sample A J → ℝ → E)
    (p : (A × MeasureFamily J) × ℝ) : E :=
  X (p.1.1, noiseFromMeasures J p.1.2) p.2

theorem measurable_realizePath {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    (X : CommonInitialNoise.Sample A J → ℝ → E)
    (hX : Measurable (fun p : CommonInitialNoise.Sample A J × ℝ => X p.1 p.2)) :
    Measurable (realizePath J X) :=
  hX.comp ((measurable_fst.fst.prodMk
    ((measurable_noiseFromMeasures J).comp measurable_fst.snd)).prodMk measurable_snd)

/-- One noise event identifies the entire realized path for every initial record
and every real time, rather than merely separate fixed-time versions. -/
theorem ae_realizePath_eq {A E : Type*} [MeasurableSpace A]
    (X : CommonInitialNoise.Sample A J → ℝ → E) (μ : Measure A) :
    ∀ᵐ p ∂CommonInitialNoise.law μ J, ∀ t,
      realizePath J X ((p.1, fun j => MarkedNoise.countingMeasure j p.2), t) = X p t := by
  filter_upwards [CommonInitialNoise.ae_noise μ (ae_noiseFromMeasures J)] with p hp
  intro t
  simp only [realizePath, hp, Prod.mk.eta]

section ActualProcess
variable {A E : Type*} [MeasurableSpace A] [Fintype J] [DecidableEq E]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
  (V : E → ℝ) (hfinite : ∀ R : ℝ, {x | V x < R}.Finite)
  (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (hbounded : ∀ n : ℕ, ∃ C : ℝ,
    ∀ x ∈ LyapunovLocalization.active V hfinite n, ∀ j t, rate j t x ≤ C)
  (initial : A → E) (e : E)

/-- The existing localized-and-patched process, now with actual measure inputs. -/
def processFromMeasures (p : (A × MeasureFamily J) × ℝ) : E :=
  realizePath J (TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e) p

theorem measurable_processFromMeasures
    (hRate : ∀ j x, Measurable (fun t => rate j t x)) (hinit : Measurable initial) :
    Measurable (processFromMeasures J V hfinite jump rate hbounded initial e) :=
  measurable_realizePath J _
    (TimeDependentGlobalProcess.measurable_process V hfinite jump rate hbounded initial e hRate hinit)

omit [Fintype J] [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [PolishSpace E] [BorelSpace E] in
/-- The actual all-time canonical path factors through its initial record and
counting measures on one full-probability event. No exhaustion or solution
identity is assumed for this factorization. -/
theorem ae_processFromMeasures_eq (μ : Measure A) :
    ∀ᵐ p ∂CommonInitialNoise.law μ J, ∀ t,
      processFromMeasures J V hfinite jump rate hbounded initial e
        ((p.1, fun j => MarkedNoise.countingMeasure j p.2), t) =
      TimeDependentGlobalProcess.process V hfinite jump rate hbounded initial e p t :=
  ae_realizePath_eq J _ μ

end ActualProcess
end CarryingCapacity.CountingMeasureStrongFunction
