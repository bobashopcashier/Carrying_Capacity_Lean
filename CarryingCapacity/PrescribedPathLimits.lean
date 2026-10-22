import CarryingCapacity.PrescribedPopulationLimits
import CarryingCapacity.PopulationPathChaos

/-!
# Genuine J1 limits on the supplied Poisson probability space

Both empirical paths and focal vector paths are the existing genuine J1 path
maps evaluated at the reconstructed original inputs. Their measurability and
exact laws are derived, and transfer the canonical convergence theorems without
an assumed equality of process laws. Focal coordinates retain one common time
change in the vector-valued path space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology ENNReal NNReal

namespace CarryingCapacity.PrescribedPathLimits
open CommonInitialNoise ConfigurationLocalization PrescribedPoissonRealization
open PopulationCouplingInitialization CoupledPathLawConvergence SkorokhodJ1

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (T : ℝ≥0)
  {Ω : Type*} [MeasurableSpace Ω]
  (M : ∀ n, Label (n + 1) D → Ω → Measure (ℝ × ℝ))
  (z : ∀ n, Ω → Configuration (n + 1) D)

def empiricalPath (n : ℕ) (ω : Ω) : Path T (MomentLaw κ D) :=
  PopulationSkorokhodLimit.empiricalPath control T (Nat.succ_pos n) id
    (record (Label (n + 1) D) (M n) (z n) ω)

def focalPath (n k : ℕ) (ω : Ω) : Path T (Fin k → AdaptedState κ D) :=
  PopulationPathChaos.interactingPath control (Nat.succ_pos n) id T k
    (record (Label (n + 1) D) (M n) (z n) ω)

variable (P : Measure Ω) [IsProbabilityMeasure P]
  (hM : ∀ n j, Measurable (M n j))
  (hPoisson : ∀ n, PoissonObservationLaw.HasDisjointLaws P (Label (n + 1) D) (M n))
  (hz : ∀ n, Measurable (z n))
  (hIndependent : ∀ n, IndepFun (z n) (fun ω j => M n j ω) P)
  (hΨ : ∀ n, Integrable (fun ω => lyapunov control (z n ω)) P)

omit [IsProbabilityMeasure P] in
include hz hΨ in
theorem initial_integrable (n : ℕ) : Integrable (lyapunov control) (P.map (z n)) :=
  integrable_initial_of_map control (P.map (z n)) P id (z n)
    measurable_id (hz n) (by simp) (hΨ n)

include hM hPoisson hz hIndependent hΨ

theorem aemeasurable_empiricalPath (n : ℕ) :
    AEMeasurable (empiricalPath control T M z n) P := by
  letI : IsProbabilityMeasure (P.map (z n)) := isProbabilityMeasure_map (hz n).aemeasurable
  exact PrescribedObservableLaws.aemeasurable_comp (Label (n + 1) D) (M n) (z n)
    P (hM n) (hPoisson n) (hz n) (hIndependent n) _
    (PopulationSkorokhodLimit.aemeasurable_empiricalPath control T (Nat.succ_pos n) id
      (P.map (z n)) measurable_id (initial_integrable control z P hz hΨ n))

theorem aemeasurable_focalPath (n k : ℕ) : AEMeasurable (focalPath control T M z n k) P := by
  letI : IsProbabilityMeasure (P.map (z n)) := isProbabilityMeasure_map (hz n).aemeasurable
  exact PrescribedObservableLaws.aemeasurable_comp (Label (n + 1) D) (M n) (z n)
    P (hM n) (hPoisson n) (hz n) (hIndependent n) _
    (PopulationPathChaos.aemeasurable_interactingPath control (Nat.succ_pos n) id T k
      (P.map (z n)) measurable_id (initial_integrable control z P hz hΨ n))

/-- One event identifies every evaluation of the empirical path with the
actual supplied-input particle trajectory, including the terminal time. -/
theorem ae_empiricalPath_apply (n : ℕ) : ∀ᵐ ω ∂P, ∀ t : Time T,
    empiricalPath control T M z n ω t = empiricalLaw κ (Nat.succ_pos n)
      (ConfigurationTimeDependent.process control (Nat.succ_pos n) id
        (record (Label (n + 1) D) (M n) (z n) ω) t) := by
  letI : IsProbabilityMeasure (P.map (z n)) := isProbabilityMeasure_map (hz n).aemeasurable
  exact ae_record (Label (n + 1) D) (M n) (z n) P (hM n) (hPoisson n) (hz n)
    (hIndependent n) (PopulationSkorokhodLimit.ae_empiricalPath_apply control T
      (Nat.succ_pos n) id (P.map (z n)) measurable_id (initial_integrable control z P hz hΨ n))

theorem ae_focalPath_apply (n k : ℕ) : ∀ᵐ ω ∂P, ∀ t : Time T,
    focalPath control T M z n k ω t = PopulationPathChaos.adaptedFirst κ k
      (ConfigurationTimeDependent.process control (Nat.succ_pos n) id
        (record (Label (n + 1) D) (M n) (z n) ω) t) := by
  letI : IsProbabilityMeasure (P.map (z n)) := isProbabilityMeasure_map (hz n).aemeasurable
  exact ae_record (Label (n + 1) D) (M n) (z n) P (hM n) (hPoisson n) (hz n)
    (hIndependent n) (PopulationPathChaos.ae_interactingPath_apply control
      (Nat.succ_pos n) id T k (P.map (z n)) measurable_id (initial_integrable control z P hz hΨ n))

def empiricalPathLaw (n : ℕ) : ProbabilityMeasure (Path T (MomentLaw κ D)) :=
  imageLaw P (empiricalPath control T M z n)
    (aemeasurable_empiricalPath control T M z P hM hPoisson hz hIndependent hΨ n)

def focalPathLaw (n k : ℕ) : ProbabilityMeasure (Path T (Fin k → AdaptedState κ D)) :=
  imageLaw P (focalPath control T M z n k)
    (aemeasurable_focalPath control T M z P hM hPoisson hz hIndependent hΨ n k)

theorem empiricalPathLaw_eq (n : ℕ) :
    empiricalPathLaw control T M z P hM hPoisson hz hIndependent hΨ n =
      PopulationSkorokhodLimit.canonicalLaw control T n (imageLaw P (z n) (hz n).aemeasurable)
        (initial_integrable control z P hz hΨ n) := by
  letI : IsProbabilityMeasure (P.map (z n)) := isProbabilityMeasure_map (hz n).aemeasurable
  apply Subtype.ext
  exact PrescribedObservableLaws.map_comp (Label (n + 1) D) (M n) (z n)
    P (hM n) (hPoisson n) (hz n) (hIndependent n) _
    (PopulationSkorokhodLimit.aemeasurable_empiricalPath control T (Nat.succ_pos n) id
      (P.map (z n)) measurable_id (initial_integrable control z P hz hΨ n))

theorem focalPathLaw_eq (n k : ℕ) :
    focalPathLaw control T M z P hM hPoisson hz hIndependent hΨ n k =
      PopulationPathChaos.canonicalLaw control (Nat.succ_pos n) P (z n) (hz n) (hΨ n) T k := by
  letI : IsProbabilityMeasure (P.map (z n)) := isProbabilityMeasure_map (hz n).aemeasurable
  apply Subtype.ext
  exact PrescribedObservableLaws.map_comp (Label (n + 1) D) (M n) (z n)
    P (hM n) (hPoisson n) (hz n) (hIndependent n) _
    (PopulationPathChaos.aemeasurable_interactingPath control (Nat.succ_pos n) id T k
      (P.map (z n)) measurable_id (initial_integrable control z P hz hΨ n))

variable (hActivity : MomentActivityBound κ q) (ν : MomentLaw κ D)
  (hCoupling : MomentCouplingBound κ q) (hMoment : Integrable control.function ν.measure)
  (hex : ∀ n, ExchangeableMatching.ExchangeableLaw (P.map (z n)))
  (C : ℝ) (hbound : ∀ n, (∫ ω, lyapunov control (z n ω) ∂P) ≤ C)
  (hconv : TendstoInMeasure P
    (fun n ω => wasserstein (empiricalLaw κ (Nat.succ_pos n) (z n ω)) ν) atTop 0)

include hex hbound hconv

/-- Weak convergence of the actual empirical J1 laws on the supplied space. -/
theorem empiricalPathLaws_tendsto :
    Tendsto (fun n => empiricalPathLaw control T M z P hM hPoisson hz hIndependent hΨ n)
      atTop (𝓝 (ConcentratingLaw.pointLaw
        (PopulationSkorokhodLimit.limitPath control T hActivity ν hCoupling hMoment))) := by
  have h := PopulationSkorokhodLimit.canonical_laws_tendsto
    control T hActivity ν hCoupling hMoment P z hz hex hΨ C hbound hconv
  exact h.congr' (Eventually.of_forall (fun n =>
    (empiricalPathLaw_eq control T M z P hM hPoisson hz hIndependent hΨ n).symm))

/-- Propagation of chaos in one vector-valued J1 space on the supplied space. -/
theorem focalPathLaws_tendsto (k : ℕ) :
    Tendsto (fun n => focalPathLaw control T M z P hM hPoisson hz hIndependent hΨ n k)
      atTop (𝓝 (NonlinearSkorokhodArray.pathLaw control hActivity ν T hCoupling hMoment k)) := by
  have h := PopulationPathChaos.canonical_laws_tendsto
    control hActivity ν T hCoupling hMoment P z hz hex hΨ C hbound hconv k
  exact h.congr' (Eventually.of_forall (fun n =>
    (focalPathLaw_eq control T M z P hM hPoisson hz hIndependent hΨ n k).symm))

end CarryingCapacity.PrescribedPathLimits
