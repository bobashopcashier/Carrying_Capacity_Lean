import CarryingCapacity.PrescribedConfigurationProcess
import CarryingCapacity.PrescribedObservableLaws
import CarryingCapacity.PopulationFixedTimeChaos

/-!
# Fixed-time propagation of chaos on the supplied Poisson space

The finite vector is extracted from the actual supplied interacting process.
Its exact law is the canonical vector law because the original initial vector
and reconstructed Poisson inputs have the proved product law. Corollary 6.4
therefore transfers without an assumed equality of output laws or any extra
initialization hypothesis.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal

namespace CarryingCapacity.PrescribedFixedTimeChaos
open ConfigurationLocalization PrescribedPoissonRealization CoupledLawConvergence

variable {Ω : Type*} [MeasurableSpace Ω]
  {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q)
  (M : (n : ℕ) → Label (n + 1) D → Ω → Measure (ℝ × ℝ))
  (ξ : (n : ℕ) → Ω → Configuration (n + 1) D)

/-- First `k` coordinates of the actual supplied process. Only the finitely
many population rows smaller than `k` use zero padding. -/
def vector (n k : ℕ) (t : ℝ) (ω : Ω) : Fin k → State D :=
  PopulationFixedTimeChaos.first k
    (PrescribedConfigurationProcess.process control (Nat.succ_pos n) id (M n) (ξ n) ω t)

omit [MeasurableSpace Ω] in
theorem vector_apply (n k : ℕ) (hkn : k ≤ n + 1) (t : ℝ) (ω : Ω) (i : Fin k) :
    vector control M ξ n k t ω i =
      PrescribedConfigurationProcess.process control (Nat.succ_pos n) id (M n) (ξ n) ω t
        (Fin.castLE hkn i) :=
  PopulationFixedTimeChaos.first_cast hkn _ i

variable (hM : ∀ n j, Measurable (M n j)) (hξ : ∀ n, Measurable (ξ n))
include hM hξ

theorem measurable_vector (n k : ℕ) (t : ℝ) :
    Measurable (vector control M ξ n k t) :=
  (PopulationFixedTimeChaos.measurable_first k).comp
    ((PrescribedConfigurationProcess.measurable_process control (Nat.succ_pos n) id
      (M n) (ξ n) measurable_id (hM n) (hξ n)).of_uncurry_right)

variable (P : Measure Ω) [IsProbabilityMeasure P]

/-- The actual pushforward probability law in the weak topology. -/
def vectorLaw (n k : ℕ) (t : ℝ) : ProbabilityMeasure (Fin k → State D) :=
  imageLaw P (vector control M ξ n k t) (measurable_vector control M ξ hM hξ n k t)

variable (hPoisson : ∀ n, PoissonObservationLaw.HasDisjointLaws P (Label (n + 1) D) (M n))
  (hIndependent : ∀ n, IndepFun (ξ n) (fun ω j => M n j ω) P)
include hPoisson hIndependent

/-- Exact vector-law identification follows from the input realization. -/
theorem vectorLaw_eq_canonical (n k : ℕ) (t : ℝ) :
    vectorLaw control M ξ hM hξ P n k t =
      PopulationFixedTimeChaos.canonicalLaw control n (imageLaw P (ξ n) (hξ n)) k t := by
  apply Subtype.ext
  exact PrescribedObservableLaws.map_comp (Label (n + 1) D) (M n) (ξ n)
    P (hM n) (hPoisson n) (hξ n) (hIndependent n)
    (PopulationFixedTimeChaos.vector control (Nat.succ_pos n) id k t)
    (PopulationFixedTimeChaos.measurable_vector control (Nat.succ_pos n) id measurable_id k t).aemeasurable

variable (hActivity : MomentActivityBound κ q) (ν : MomentLaw κ D)
  (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)
  (hex : ∀ n, ExchangeableMatching.ExchangeableLaw (P.map (ξ n)))
  (hΨ : ∀ n, Integrable (fun ω => lyapunov control (ξ n ω)) P)
  (C : ℝ) (hbound : ∀ n, (∫ ω, lyapunov control (ξ n ω) ∂P) ≤ C)
  (hconv : TendstoInMeasure P
    (fun n ω => wasserstein (empiricalLaw κ (Nat.succ_pos n) (ξ n ω)) ν) atTop 0)
include hex hΨ hbound hconv

/-- Corollary 6.4 for the actual supplied finite systems, with limiting law
exactly the product of the constructed nonlinear marginals. -/
theorem vectorLaws_tendsto (k : ℕ) (t : Icc (0 : ℝ) T) :
    Tendsto (fun n => vectorLaw control M ξ hM hξ P n k t)
      atTop (𝓝 (PopulationFixedTimeChaos.productLaw control hActivity ν T hT hCoupling hMoment k t)) := by
  have h := PopulationFixedTimeChaos.canonical_laws_tendsto control hActivity ν T hT hCoupling hMoment
    P ξ hξ hex hΨ C hbound hconv k t
  exact h.congr' (Eventually.of_forall (fun n =>
    (vectorLaw_eq_canonical control M ξ hM hξ P hPoisson hIndependent n k t).symm))

end CarryingCapacity.PrescribedFixedTimeChaos
