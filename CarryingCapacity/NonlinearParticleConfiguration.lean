import CarryingCapacity.NonlinearParticleContinuation
import CarryingCapacity.DeterministicEnvironmentConfiguration
import CarryingCapacity.TimeDependentGlobalUniqueness

/-!
# The nonlinear particle array is the actual configuration process

The scalar copies already use the corresponding coordinates of the common
marked noise. Their vector satisfies the configuration counting equations:
only the label selecting a tested particle contributes to that coordinate.
Discrete pathwise uniqueness identifies this vector with the separately
constructed configuration. The initial averaged Lyapunov integrability is
derived from the iid marginal, rather than added as a hypothesis.

The equality holds for the endpoint-held continuation on all nonnegative
times. Nonlinear self-consistency is still restricted to the original horizon.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal Topology BigOperators

namespace CarryingCapacity.NonlinearParticleConfiguration
open CommonInitialNoise ConfigurationLocalization DeterministicEnvironmentLyapunov

variable {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)
  {A : Type*} [MeasurableSpace A] (initial : A → Configuration N D)

/-- The actual vector of scalar nonlinear copies on the original sample. -/
def path (p : Sample A (Label N D)) (t : ℝ) : Configuration N D :=
  fun i => NonlinearParticleArray.process control hActivity ν T hT hCoupling hMoment initial i p t

/-- Its coordinatewise genuine predictable pre-state. -/
def preState (p : Sample A (Label N D)) (t : ℝ) : Configuration N D :=
  fun i => NonlinearParticleArray.preState control hActivity ν T hT hCoupling hMoment initial i p t

/-- The finite coordinate tests separate all configurations, including when
the state dimension is zero. -/
theorem coordinate_separates (x y : Configuration N D)
    (h : ∀ a : Fin N × Fin D, (x a.1 a.2 : ℝ) = (y a.1 a.2 : ℝ)) : x = y := by
  funext i k
  exact Nat.cast_injective (h (i,k))

omit [MeasurableSpace A] in
/-- In a coordinate test, every label belonging to another particle vanishes. -/
theorem coordinate_increment (i : Fin N) (k : Fin D) (j : Label N D)
    (S : ℝ) (p : Sample A (Label N D)) (z : ℝ × ℝ) :
    TimeDependentEquationUniqueness.increment jump
      (DeterministicEnvironmentConfiguration.rate κ q
        (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment) T)
      (preState control hActivity ν T hT hCoupling hMoment initial p)
      (fun x => (x i k : ℝ)) j S z =
    if j.1 = i then NonlinearParticleContinuation.increment control hActivity ν T hT
      hCoupling hMoment initial i (fun x => (x k : ℝ)) j.2 S (p,z) else 0 := by
  rcases j with ⟨l,j⟩
  by_cases h : l = i
  · subst l
    simp [TimeDependentEquationUniqueness.increment,
      DeterministicEnvironmentConfiguration.rate, preState, jump,
      NonlinearParticleContinuation.increment]
  · simp [TimeDependentEquationUniqueness.increment,
      jump, Function.update_of_ne (Ne.symm h), h]

variable (hInitial : Measurable initial) (γ : Measure A) [IsProbabilityMeasure γ]
  (hright : γ.map initial = Measure.pi (fun _ : Fin N => ν.measure))
include hInitial hright hMoment

omit [IsProbabilityMeasure γ] in
/-- The initial coordinate marginal supplies its true Lyapunov integrability. -/
theorem integrable_initial_coordinate (i : Fin N) :
    Integrable (fun a => control.function (initial a i)) γ := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  have hm : Measurable (fun a => initial a i) := (measurable_pi_apply i).comp hInitial
  have he : γ.map (fun a => initial a i) = ν.measure := by
    change γ.map ((fun z : Configuration N D => z i) ∘ initial) = _
    rw [← Measure.map_map (measurable_pi_apply i) hInitial, hright,
      ParticleInputRecords.pi_coordinate_map]
  have hi : Integrable control.function (γ.map (fun a => initial a i)) := by
    rw [he]
    exact hMoment
  exact (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    hm.aemeasurable).mp hi

omit [IsProbabilityMeasure γ] in
/-- No additional averaged-initial-moment premise is required. -/
theorem integrable_initial_lyapunov :
    Integrable (fun a => lyapunov control (initial a)) γ := by
  exact (integrable_finset_sum _ (fun i _ =>
    integrable_initial_coordinate control ν hMoment initial hInitial γ hright i)).const_mul _

/-- The vector starts at the extracted initial configuration on one event. -/
theorem ae_initial : ∀ᵐ p ∂law γ (Label N D),
    path control hActivity ν T hT hCoupling hMoment initial p 0 = initial p.1 := by
  filter_upwards [NonlinearParticleContinuation.ae_initial control hActivity ν T hT
    hCoupling hMoment initial hInitial γ hright] with p hp
  exact funext hp

/-- The actual coordinate pre-states form the vector's positive-time left limit. -/
theorem ae_tendsto_preState : ∀ᵐ p ∂law γ (Label N D), ∀ t : ℝ, 0 < t →
    Tendsto (path control hActivity ν T hT hCoupling hMoment initial p) (𝓝[<] t)
      (𝓝 (preState control hActivity ν T hT hCoupling hMoment initial p t)) := by
  filter_upwards [NonlinearParticleArray.ae_cadlag control hActivity ν T hT hCoupling
    hMoment initial hInitial γ hright,
    NonlinearParticleArray.ae_preState_eq_leftLim control hActivity ν T hT hCoupling
      hMoment initial hInitial γ hright] with p hc hp
  intro t ht
  apply tendsto_pi_nhds.mpr
  intro i
  obtain ⟨y, hy⟩ := (hc i).2 t ht
  have he := leftLim_eq_of_tendsto (neBot_iff.mp inferInstance) hy
  change Tendsto _ _ (𝓝 (NonlinearParticleArray.preState control hActivity ν T hT
    hCoupling hMoment initial i p t))
  rw [hp i t ht, he]
  exact hy

/-- Finite products preserve the actual scalar càdlàg regularity. -/
theorem ae_cadlag : ∀ᵐ p ∂law γ (Label N D),
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt
      (path control hActivity ν T hT hCoupling hMoment initial p) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : Configuration N D, Tendsto
      (path control hActivity ν T hT hCoupling hMoment initial p) (𝓝[<] t) (𝓝 y)) := by
  filter_upwards [NonlinearParticleArray.ae_cadlag control hActivity ν T hT hCoupling
    hMoment initial hInitial γ hright,
    ae_tendsto_preState control hActivity ν T hT hCoupling hMoment initial hInitial γ hright]
    with p hc hp
  exact ⟨fun t ht => continuousWithinAt_pi.mpr (fun i => (hc i).1 t ht),
    fun t ht => ⟨_, hp t ht⟩⟩

/-- All finite separating tests obey the configuration counting equation,
with the original particle-labelled random measures. -/
theorem ae_coordinate_counting_identity : ∀ᵐ p ∂law γ (Label N D),
    ∀ a : Fin N × Fin D, ∀ S : ℝ≥0,
      (path control hActivity ν T hT hCoupling hMoment initial p S a.1 a.2 : ℝ) -
        (initial p.1 a.1 a.2 : ℝ) =
      ∑ j : Label N D, ∫ z,
        TimeDependentEquationUniqueness.increment jump
          (DeterministicEnvironmentConfiguration.rate κ q
            (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment) T)
          (preState control hActivity ν T hT hCoupling hMoment initial p)
          (fun x => (x a.1 a.2 : ℝ)) j S z ∂MarkedNoise.countingMeasure j p.2 := by
  have he := ae_all_iff.mpr (fun k : Fin D =>
    NonlinearParticleContinuation.ae_counting_identity control hActivity ν T hT
      hCoupling hMoment initial hInitial γ hright (fun x => (x k : ℝ)))
  filter_upwards [he] with p hp
  intro a S
  rw [show (path control hActivity ν T hT hCoupling hMoment initial p S a.1 a.2 : ℝ) -
      (initial p.1 a.1 a.2 : ℝ) = _ from hp a.2 a.1 S]
  symm
  simp_rw [coordinate_increment control hActivity ν T hT hCoupling hMoment initial]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a.1]
  · simp only [if_pos rfl, ite_true]
  · intro b _ hb
    simp only [if_neg hb, integral_zero, Finset.sum_const_zero]
  · simp

/-- The scalar array and the independently constructed configuration coincide
on the original sample and original noise, simultaneously at all nonnegative
times. The only initial moment used is the scalar marginal's genuine moment. -/
theorem ae_path_eq_configuration (hN : 0 < N) :
    ∀ᵐ p ∂law γ (Label N D), ∀ s : ℝ, 0 ≤ s →
      path control hActivity ν T hT hCoupling hMoment initial p s =
        DeterministicEnvironmentConfiguration.process control hN hActivity
          (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment) T hT
          (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment).continuousOn
          initial p s := by
  let v := NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment
  have hv : ContinuousOn v (Icc 0 T) :=
    (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment).continuousOn
  let B := manuscriptBound control ν (DeterministicEnvironmentLyapunov.driftConstant control) T
  have hB : 0 ≤ B := manuscriptBound_nonnegative control ν (DeterministicEnvironmentLyapunov.driftConstant control) T
    (DeterministicEnvironmentLyapunov.driftConstant_nonnegative control) hT
  have hEnv : ∀ t ∈ Icc 0 T,
      LyapunovFlowSpace.lyapunovIntegral control.function (v t) ≤ ENNReal.ofReal B :=
    fun t _ => manuscriptExtension_bound control ν (DeterministicEnvironmentLyapunov.driftConstant control) T
      (DeterministicEnvironmentLyapunov.driftConstant_nonnegative control) hT
      (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hMoment) t
  have hV := integrable_initial_lyapunov control ν hMoment initial hInitial γ hright
  filter_upwards [ae_cadlag control hActivity ν T hT hCoupling hMoment initial hInitial γ hright,
    ae_tendsto_preState control hActivity ν T hT hCoupling hMoment initial hInitial γ hright,
    ae_initial control hActivity ν T hT hCoupling hMoment initial hInitial γ hright,
    ae_coordinate_counting_identity control hActivity ν T hT hCoupling hMoment initial hInitial γ hright,
    DeterministicEnvironmentConfiguration.ae_cadlag control hN hActivity v T hT hv initial γ
      hCoupling hInitial B hB hEnv hV,
    DeterministicEnvironmentConfiguration.ae_tendsto_preState control hN hActivity v T hT hv initial γ
      hCoupling hInitial B hB hEnv hV,
    DeterministicEnvironmentConfiguration.ae_initial control hN hActivity v T hT hv initial γ,
    DeterministicEnvironmentConfiguration.ae_coordinate_counting_identity control hN hActivity v T hT hv
      initial γ hCoupling hInitial B hB hEnv hV] with p hc hp hz he gc gp gz ge
  apply TimeDependentEquationUniqueness.eq_of_separating_counting_equations
    (fun (a : Fin N × Fin D) x => (x a.1 a.2 : ℝ)) coordinate_separates jump
    (DeterministicEnvironmentConfiguration.rate κ q v T)
    (fun j => MarkedNoise.countingMeasure j p.2)
    (path control hActivity ν T hT hCoupling hMoment initial p)
    (DeterministicEnvironmentConfiguration.process control hN hActivity v T hT hv initial p)
    (preState control hActivity ν T hT hCoupling hMoment initial p)
    (DeterministicEnvironmentConfiguration.preState control hN hActivity v T hT hv initial p)
    hc.1 gc.1 hp gp (hz.trans gz.symm)
  · intro a s hs
    rw [hz]
    exact he a ⟨s, hs⟩
  · intro a s hs
    rw [gz]
    calc
      _ = ∑ j, ∫ z, DeterministicEnvironmentConfiguration.horizonIncrement
        control hN hActivity v T hT hv initial (fun x => (x a.1 a.2 : ℝ)) j s (p,z)
          ∂MarkedNoise.countingMeasure j p.2 := ge a ⟨s, hs⟩
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => TimeDependentGlobalCounting.horizonIncrement_apply
          (lyapunov control) (finite_sublevel control hN) jump
          (DeterministicEnvironmentConfiguration.rate κ q v T)
          (DeterministicEnvironmentConfiguration.exists_uniform_rate_bounds control hN hActivity v T hT hv)
          initial 0 (fun x => (x a.1 a.2 : ℝ)) j s p z)

/-- The positive-time pre-states also agree on the same sample. Consequently
accepted jump fields can be transported pointwise, including at jump times. -/
theorem ae_preState_eq_configuration (hN : 0 < N) :
    ∀ᵐ p ∂law γ (Label N D), ∀ s : ℝ, 0 < s →
      preState control hActivity ν T hT hCoupling hMoment initial p s =
        DeterministicEnvironmentConfiguration.preState control hN hActivity
          (NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment) T hT
          (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment).continuousOn
          initial p s := by
  let v := NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment
  have hv : ContinuousOn v (Icc 0 T) :=
    (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment).continuousOn
  let B := manuscriptBound control ν (DeterministicEnvironmentLyapunov.driftConstant control) T
  have hB : 0 ≤ B := manuscriptBound_nonnegative control ν
    (DeterministicEnvironmentLyapunov.driftConstant control) T
    (DeterministicEnvironmentLyapunov.driftConstant_nonnegative control) hT
  have hEnv : ∀ t ∈ Icc 0 T,
      LyapunovFlowSpace.lyapunovIntegral control.function (v t) ≤ ENNReal.ofReal B :=
    fun t _ => manuscriptExtension_bound control ν (DeterministicEnvironmentLyapunov.driftConstant control) T
      (DeterministicEnvironmentLyapunov.driftConstant_nonnegative control) hT
      (NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hMoment) t
  have hV := integrable_initial_lyapunov control ν hMoment initial hInitial γ hright
  filter_upwards [ae_path_eq_configuration control hActivity ν T hT hCoupling hMoment
    initial hInitial γ hright hN,
    ae_tendsto_preState control hActivity ν T hT hCoupling hMoment initial hInitial γ hright,
    DeterministicEnvironmentConfiguration.ae_tendsto_preState control hN hActivity v T hT hv initial γ
      hCoupling hInitial B hB hEnv hV] with p he hp gp
  intro t ht
  exact CountingEquationUniqueness.leftLimit_eq_of_strictPast
    (path control hActivity ν T hT hCoupling hMoment initial p)
    (DeterministicEnvironmentConfiguration.process control hN hActivity v T hT hv initial p)
    (preState control hActivity ν T hT hCoupling hMoment initial p)
    (DeterministicEnvironmentConfiguration.preState control hN hActivity v T hT hv initial p)
    hp gp t (fun s hs _ => he s hs) t ⟨ht, le_rfl⟩

end CarryingCapacity.NonlinearParticleConfiguration
