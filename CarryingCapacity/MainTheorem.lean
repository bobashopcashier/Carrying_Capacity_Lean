import CarryingCapacity.PrescribedConfigurationProcess
import CarryingCapacity.PrescribedPathLimits
import CarryingCapacity.NonlinearForwardUniqueness

/-!
# The complete general moment-dependent mean-field theorem

The four clauses of manuscript Theorem 2.7 are assembled for the actual
systems driven by supplied Poisson measures. The conclusion records concrete
solution properties and limits. No solution, comparison, or convergence
conclusion is an input to `main_theorem`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.MainTheorem
open ConfigurationLocalization

variable {Ω : Type*} [MeasurableSpace Ω]
  {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}

/-- The actual coordinate thinning equations, with the candidate's own left
limits. The uniqueness class has no additional moment or adaptation premise. -/
def CoordinateSolution {N : ℕ} (hN : 0 < N)
    (M : Label N D → Ω → Measure (ℝ × ℝ)) (ξ : Ω → Configuration N D)
    (P : Measure Ω) (X : Ω → ℝ → Configuration N D) : Prop :=
  (∀ᵐ ω ∂P,
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (X ω) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : Configuration N D,
      Tendsto (X ω) (𝓝[<] t) (𝓝 y))) ∧
  (∀ᵐ ω ∂P, X ω 0 = ξ ω) ∧
  (∀ i : Fin N × Fin D, ∀ᵐ ω ∂P, ∀ S : ℝ≥0,
    (X ω S i.1 i.2 : ℝ) - (ξ ω i.1 i.2 : ℝ) =
      ∑ j, ∫ z, TimeDependentEquationUniqueness.increment jump
        (ConfigurationTimeDependent.timeRate κ q hN) (Function.leftLim (X ω))
        (fun x => (x i.1 i.2 : ℝ)) j S z ∂M j ω)

/-- A measurable strong solution of the actual supplied equation, with finite
activity on every finite horizon and pathwise uniqueness for the same inputs. -/
structure StrongSystem (control : LyapunovControl κ q) {N : ℕ} (hN : 0 < N)
    (M : Label N D → Ω → Measure (ℝ × ℝ)) (ξ : Ω → Configuration N D)
    (P : Measure Ω) (hM : ∀ j, Measurable (M j)) (hξ : Measurable ξ) : Prop where
  measurable : Measurable (fun p : Ω × ℝ =>
    PrescribedConfigurationProcess.process control hN id M ξ p.1 p.2)
  adapted : Adapted (UsualFiltration.filtration P
    (PrescribedPoissonFiltration.rawFiltration (Label N D) M ξ hM hξ))
    (fun t ω => PrescribedConfigurationProcess.process control hN id M ξ ω t)
  solution : CoordinateSolution (q := q) hN M ξ P
    (PrescribedConfigurationProcess.process control hN id M ξ)
  integrable_increments : ∀ᵐ ω ∂P, ∀ (S : ℝ≥0) (f : Configuration N D → ℝ) (j : Label N D),
    Integrable (PrescribedConfigurationProcess.increment control hN id M ξ f j S ω) (M j ω)
  nonexplosive : ∀ᵐ ω ∂P, ∀ S : ℝ≥0, ∃ times : Finset ℝ,
    (times : Set ℝ) ⊆ Ioc 0 S ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ S →
      (∀ u ∈ times, u ∉ Ioc s t) →
        PrescribedConfigurationProcess.process control hN id M ξ ω s =
          PrescribedConfigurationProcess.process control hN id M ξ ω t
  unique : ∀ Y : Ω → ℝ → Configuration N D,
    CoordinateSolution (q := q) hN M ξ P Y →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Y ω t = PrescribedConfigurationProcess.process control hN id M ξ ω t

/-- Existence and pathwise uniqueness are packaged for the same explicit
supplied realization; the constructed path satisfies the uniqueness class. -/
theorem strong_system (control : LyapunovControl κ q) {N : ℕ} (hN : 0 < N)
    (M : Label N D → Ω → Measure (ℝ × ℝ)) (ξ : Ω → Configuration N D)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hM : ∀ j, Measurable (M j))
    (hPoisson : PoissonObservationLaw.HasDisjointLaws P (Label N D) M)
    (hξ : Measurable ξ) (hIndependent : IndepFun ξ (fun ω j => M j ω) P)
    (hΨ : Integrable (fun ω => lyapunov control (ξ ω)) P) :
    StrongSystem control hN M ξ P hM hξ := by
  letI : IsProbabilityMeasure (P.map ξ) := isProbabilityMeasure_map hξ.aemeasurable
  have hV : Integrable (fun x : Configuration N D => lyapunov control (id x)) (P.map ξ) :=
    PopulationCouplingInitialization.integrable_initial_of_map control (P.map ξ) P id ξ
      measurable_id hξ (by simp) hΨ
  have hc := PrescribedConfigurationProcess.ae_cadlag control hN id M ξ
    measurable_id hM hξ P hPoisson hIndependent (P.map ξ) rfl hV
  have hz := PrescribedConfigurationProcess.ae_initial control hN id M ξ
    hM hξ P hPoisson hIndependent (P.map ξ) rfl
  have hpre := PrescribedConfigurationProcess.ae_tendsto_preState control hN id M ξ
    measurable_id hM hξ P hPoisson hIndependent (P.map ξ) rfl hV
  refine ⟨PrescribedConfigurationProcess.measurable_process control hN id M ξ measurable_id hM hξ,
    PrescribedConfigurationProcess.adapted_process control hN id M ξ measurable_id hM hξ
      P hPoisson hIndependent,
    ⟨hc,hz,?_⟩,
    PrescribedConfigurationProcess.ae_integrable_increment control hN id M ξ
      measurable_id hM hξ P hPoisson hIndependent (P.map ξ) rfl hV,
    PrescribedConfigurationProcess.ae_finite_activity control hN id M ξ
      measurable_id hM hξ P hPoisson hIndependent (P.map ξ) rfl hV, ?_⟩
  · intro i
    have he := PrescribedConfigurationProcess.ae_counting_identity control hN id M ξ
      measurable_id hM hξ P hPoisson hIndependent (P.map ξ) rfl hV
      (fun x => (x i.1 i.2 : ℝ))
    filter_upwards [hpre,he] with ω hp heq
    intro S
    refine (heq S).trans ?_
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    apply Eventually.of_forall
    intro z
    by_cases ht : z.1 ∈ Ioc 0 (S : ℝ)
    · have hl := leftLim_eq_of_tendsto (neBot_iff.mp inferInstance) (hp z.1 ht.1)
      simp only [TimeDependentEquationUniqueness.increment, hl,
        PrescribedConfigurationProcess.increment, ConfigurationTimeDependent.timeRate_apply]
    · simp only [TimeDependentEquationUniqueness.increment,
        PrescribedConfigurationProcess.increment, ht, false_and, if_false]
  · intro Y hY
    exact PrescribedConfigurationProcess.ae_unique_of_coordinate_equations control hN id M ξ
      measurable_id hM hξ P hPoisson hIndependent (P.map ξ) rfl hV Y hY.1 hY.2.1 hY.2.2

variable (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ≥0) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)
  (M : ∀ n, Label (n + 1) D → Ω → Measure (ℝ × ℝ))
  (ξ : ∀ n, Ω → Configuration (n + 1) D)
  (P : Measure Ω) [IsProbabilityMeasure P]
  (hM : ∀ n j, Measurable (M n j))
  (hPoisson : ∀ n, PoissonObservationLaw.HasDisjointLaws P (Label (n + 1) D) (M n))
  (hξ : ∀ n, Measurable (ξ n))
  (hIndependent : ∀ n, IndepFun (ξ n) (fun ω j => M n j ω) P)
  (hΨ : ∀ n, Integrable (fun ω => lyapunov control (ξ n ω)) P)

local notation "v" => NonlinearFixedPoint.environment control hActivity ν T T.coe_nonneg hCoupling hMoment

/-- The four conclusions of Theorem 2.7, with the actual supplied finite
systems and the actual nonlinear law curve. Additional fields identify the
limiting paths as independent nonlinear copies through their path laws, initial
and marginal laws, and counting equations. -/
structure Conclusions : Prop where
  finite_systems : ∀ n, StrongSystem control (Nat.succ_pos n) (M n) (ξ n) P (hM n) (hξ n)
  nonlinear_solution : NonlinearForwardUniqueness.IsMomentBoundedSolution control.function q ν T v
  nonlinear_continuous : ContinuousOn v (Icc 0 (T : ℝ))
  nonlinear_unique : ∀ w : ℝ → MomentLaw κ D,
    NonlinearForwardUniqueness.IsMomentBoundedSolution control.function q ν T w → EqOn w v (Icc 0 T)
  nonlinear_envelope : ∀ t ∈ Icc 0 (T : ℝ),
    LyapunovFlowSpace.lyapunovIntegral control.function (v t) ≤
      ENNReal.ofReal (LyapunovFlowSpace.exponentialEnvelope (∫ x, control.function x ∂ν.measure)
        (DeterministicEnvironmentLyapunov.driftConstant control) t)
  empirical_uniform : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => P {ω | ENNReal.ofReal ε <
    PrescribedPopulationLimits.runningError control hActivity ν T T.coe_nonneg hCoupling hMoment M ξ n ω})
    atTop (𝓝 0)
  moment_uniform : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => P {ω | ENNReal.ofReal ε <
    PrescribedPopulationLimits.runningMomentError control hActivity ν T T.coe_nonneg hCoupling hMoment M ξ n ω})
    atTop (𝓝 0)
  empirical_path_limit : Tendsto (fun n => PrescribedPathLimits.empiricalPathLaw
    control T M ξ P hM hPoisson hξ hIndependent hΨ n) atTop
      (𝓝 (ConcentratingLaw.pointLaw (PopulationSkorokhodLimit.limitPath control T hActivity ν hCoupling hMoment)))
  focal_path_limit : ∀ k : ℕ, Tendsto (fun n => PrescribedPathLimits.focalPathLaw
    control T M ξ P hM hPoisson hξ hIndependent hΨ n k) atTop
      (𝓝 (NonlinearSkorokhodArray.pathLaw control hActivity ν T hCoupling hMoment k))
  independent_limit_paths : ∀ k : ℕ, iIndepFun
    (NonlinearSkorokhodArray.coordinatePath control hActivity ν T hCoupling hMoment k)
    (NonlinearSkorokhodArray.inputLaw ν k)
  limit_path_marginals : ∀ (k : ℕ) (i : Fin k),
    (NonlinearSkorokhodArray.inputLaw ν k).map
      (NonlinearSkorokhodArray.coordinatePath control hActivity ν T hCoupling hMoment k i) =
    (CommonInitialNoise.law ν.measure (Jump D)).map
      (NonlinearSkorokhodArray.singlePath control hActivity ν T hCoupling hMoment)
  limit_process_initial_law :
    (CommonInitialNoise.law ν.measure (Jump D)).map
      (fun p => NonlinearFixedPoint.process control hActivity ν T T.coe_nonneg hCoupling hMoment p 0) =
      ν.measure
  limit_process_marginal : ∀ t : Icc (0 : ℝ) T,
    (CommonInitialNoise.law ν.measure (Jump D)).map
      (fun p => NonlinearFixedPoint.process control hActivity ν T T.coe_nonneg hCoupling hMoment p t) =
      (v t).measure
  limit_process_left_limits : ∀ᵐ p ∂CommonInitialNoise.law ν.measure (Jump D), ∀ t : ℝ, 0 < t →
    NonlinearFixedPoint.preState control hActivity ν T T.coe_nonneg hCoupling hMoment p t =
      Function.leftLim (NonlinearFixedPoint.process control hActivity ν T T.coe_nonneg hCoupling hMoment p) t
  limit_process_counting_equation : ∀ f : State D → ℝ,
    ∀ᵐ p ∂CommonInitialNoise.law ν.measure (Jump D), ∀ S : ℝ≥0, (S : ℝ) ≤ T →
      f (NonlinearFixedPoint.process control hActivity ν T T.coe_nonneg hCoupling hMoment p S) - f p.1 =
        ∑ j, ∫ z : ℝ × ℝ,
          (if z.1 ∈ Ioc 0 (S : ℝ) ∧ z.2 ≤ q.rate j
            (NonlinearFixedPoint.preState control hActivity ν T T.coe_nonneg hCoupling hMoment p z.1) (v z.1)
          then f (Jump.advance j
            (NonlinearFixedPoint.preState control hActivity ν T T.coe_nonneg hCoupling hMoment p z.1)) -
              f (NonlinearFixedPoint.preState control hActivity ν T T.coe_nonneg hCoupling hMoment p z.1)
          else 0) ∂MarkedNoise.countingMeasure j p.2

/-- Theorem 2.7 in one statement. The assumptions are the manuscript's
dynamic bounds and initialization, together with the standard supplied PRM
laws and their independence of the initial vector. All four conclusions and
the identity of the independent limiting paths are proved simultaneously. -/
theorem main_theorem
    (hex : ∀ n, ExchangeableMatching.ExchangeableLaw (P.map (ξ n)))
    (C : ℝ) (hbound : ∀ n, (∫ ω, lyapunov control (ξ n ω) ∂P) ≤ C)
    (hconv : TendstoInMeasure P
      (fun n ω => wasserstein (empiricalLaw κ (Nat.succ_pos n) (ξ n ω)) ν) atTop 0) :
    Conclusions control hActivity ν T hCoupling hMoment M ξ P hM hPoisson hξ hIndependent hΨ := by
  have hv := NonlinearForwardUniqueness.environment_isSolution
    control hActivity ν T T.coe_nonneg hCoupling hMoment
  refine {
    finite_systems := fun n => strong_system control (Nat.succ_pos n) (M n) (ξ n) P
      (hM n) (hPoisson n) (hξ n) (hIndependent n) (hΨ n)
    nonlinear_solution := hv
    nonlinear_continuous := NonlinearForwardUniqueness.continuousOn_solution control ν T T.coe_nonneg v hv
    nonlinear_unique := fun w hw => NonlinearForwardUniqueness.solution_eq_environment
      control hActivity ν T T.coe_nonneg hCoupling hMoment w hw
    nonlinear_envelope := fun t ht => NonlinearForwardUniqueness.solution_envelope
      control hActivity ν T T.coe_nonneg hCoupling hMoment v hv t ht
    empirical_uniform := PrescribedPopulationLimits.measure_runningError_gt_tendsto_zero
      control hActivity ν T T.coe_nonneg hCoupling hMoment M ξ P hM hPoisson hξ hIndependent hΨ
      hex C hbound hconv
    moment_uniform := PrescribedPopulationLimits.measure_runningMomentError_gt_tendsto_zero
      control hActivity ν T T.coe_nonneg hCoupling hMoment M ξ P hM hPoisson hξ hIndependent hΨ
      hex C hbound hconv
    empirical_path_limit := PrescribedPathLimits.empiricalPathLaws_tendsto
      control T M ξ P hM hPoisson hξ hIndependent hΨ hActivity ν hCoupling hMoment hex C hbound hconv
    focal_path_limit := PrescribedPathLimits.focalPathLaws_tendsto
      control T M ξ P hM hPoisson hξ hIndependent hΨ hActivity ν hCoupling hMoment hex C hbound hconv
    independent_limit_paths := NonlinearSkorokhodArray.independent_coordinatePaths
      control hActivity ν T hCoupling hMoment
    limit_path_marginals := NonlinearSkorokhodArray.coordinatePath_map
      control hActivity ν T hCoupling hMoment
    limit_process_initial_law := NonlinearFixedPoint.process_initial_law
      control hActivity ν T T.coe_nonneg hCoupling hMoment
    limit_process_marginal := fun t => (NonlinearFixedPoint.environment_measure_eq_marginal
      control hActivity ν T T.coe_nonneg hCoupling hMoment t).symm
    limit_process_left_limits := NonlinearFixedPoint.ae_preState_eq_leftLim
      control hActivity ν T T.coe_nonneg hCoupling hMoment
    limit_process_counting_equation := NonlinearFixedPoint.ae_counting_identity
      control hActivity ν T T.coe_nonneg hCoupling hMoment }

end CarryingCapacity.MainTheorem
