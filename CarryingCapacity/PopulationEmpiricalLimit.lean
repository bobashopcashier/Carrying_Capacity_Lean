import CarryingCapacity.NonlinearEmpiricalUniform
import CarryingCapacity.PopulationSynchronousApproximation

/-!
# Uniform empirical and generalized-moment limits for the canonical population

The manuscript initialization constructs a coupling with the exact original
initial vector law. The established synchronous comparison and uniform iid
empirical theorem give the interacting empirical limit on that coupled space.
Projection to the initial vector and unchanged noise transfers it to the
canonical population with the original initial vector law. The uniform
generalized-moment limit follows from the genuine moment Lipschitz bound.
No claim about an externally supplied path realization or path-space chaos is
made here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.PopulationEmpiricalLimit
open CommonInitialNoise ConfigurationLocalization PopulationCouplingInitialization
open PopulationSynchronousApproximation SynchronousRunningSupremum

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)

local notation "v" => NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment
local notation "hv" => Continuous.continuousOn (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment)

section Projection
variable {N : ℕ} {A : Type*} [MeasurableSpace A]
  (initial : A → Configuration N D)

/-- Retain the extracted initial vector and every original driving clock and mark. -/
def initialProjection (p : Sample A (Label N D)) : Sample (Configuration N D) (Label N D) :=
  (initial p.1, p.2)

theorem measurable_initialProjection (hinit : Measurable initial) :
    Measurable (initialProjection initial) :=
  (hinit.comp measurable_fst).prodMk measurable_snd

/-- Projection gives precisely the canonical original-vector/noise product law. -/
theorem initialProjection_map (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial) :
    (law μ (Label N D)).map (initialProjection initial) = law (μ.map initial) (Label N D) := by
  change (μ.prod (MarkedNoise.law (Label N D))).map (Prod.map initial id) = _
  rw [← Measure.map_prod_map μ (MarkedNoise.law (Label N D)) hinit measurable_id,
    Measure.map_id]
  rfl

omit [MeasurableSpace A] in
/-- The chosen canonical path depends on a record only through its extracted
initial vector, with exact equality on every sample and at every time. -/
theorem process_initialProjection (hN : 0 < N) (p : Sample A (Label N D)) (t : ℝ) :
    ConfigurationTimeDependent.process control hN id (initialProjection initial p) t =
      ConfigurationTimeDependent.process control hN initial p t := rfl

end Projection

section Row
variable {A : Type*} [MeasurableSpace A] (n : ℕ)
  (initial : A → Configuration (n + 1) D)

/-- Actual interacting empirical transport error at one real time. -/
def error (t : ℝ) (p : Sample A (Label (n + 1) D)) : ℝ :=
  wasserstein (empiricalLaw κ (Nat.succ_pos n)
    (ConfigurationTimeDependent.process control (Nat.succ_pos n) initial p t)) (v t)

/-- The supremum over every real time in the construction interval. -/
def runningError (p : Sample A (Label (n + 1) D)) : ℝ≥0∞ :=
  intervalSup (fun t => ENNReal.ofReal (error control hActivity ν T hT hCoupling hMoment n initial t p)) T

/-- Uniform absolute error of the generalized moment of the actual empirical law. -/
def runningMomentError (p : Sample A (Label (n + 1) D)) : ℝ≥0∞ :=
  intervalSup (fun t => ENNReal.ofReal
    |moment (empiricalLaw κ (Nat.succ_pos n)
      (ConfigurationTimeDependent.process control (Nat.succ_pos n) initial p t)) - moment (v t)|) T

omit [MeasurableSpace A] in
/-- The actual generalized moment is controlled pointwise by transport,
before any probabilistic or asymptotic argument. -/
theorem runningMomentError_le_runningError (p : Sample A (Label (n + 1) D)) :
    runningMomentError control hActivity ν T hT hCoupling hMoment n initial p ≤
      runningError control hActivity ν T hT hCoupling hMoment n initial p := by
  apply iSup_le
  intro t
  exact (ENNReal.ofReal_le_ofReal (moment_difference_le_wasserstein _ _)).trans
    (le_iSup_of_le t le_rfl)

private theorem ae_empiricalLaw_rightContinuous (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial)
    (hV : Integrable (fun a => lyapunov control (initial a)) μ) :
    ∀ᵐ p ∂law μ (Label (n + 1) D), ∀ t : ℝ, 0 ≤ t →
      ContinuousWithinAt (fun s => empiricalLaw κ (Nat.succ_pos n)
        (ConfigurationTimeDependent.process control (Nat.succ_pos n) initial p s)) (Ici t) t := by
  have hc := TimeDependentGlobalProcess.ae_process_cadlag (lyapunov control)
    (finite_sublevel control (Nat.succ_pos n)) jump
    (ConfigurationTimeDependent.timeRate κ q (Nat.succ_pos n))
    (ConfigurationTimeDependent.uniform_rate_bounds control (Nat.succ_pos n)) initial 0 μ
    (ConfigurationTimeDependent.ae_exhaustive control (Nat.succ_pos n) initial μ hinit hV)
  filter_upwards [hc] with p hp
  intro t ht
  have he : Continuous (empiricalLaw κ (Nat.succ_pos n) : Configuration (n + 1) D → MomentLaw κ D) :=
    continuous_of_discreteTopology
  exact he.continuousAt.comp_continuousWithinAt ((hp.1) t ht)

private theorem measurable_error_at (hinit : Measurable initial) (t : ℝ) :
    Measurable (error control hActivity ν T hT hCoupling hMoment n initial t) :=
  (measurable_of_countable (fun z : Configuration (n + 1) D =>
    wasserstein (empiricalLaw κ (Nat.succ_pos n) z) (v t))).comp
    ((ConfigurationTimeDependent.measurable_process control (Nat.succ_pos n) initial hinit).of_uncurry_right)

/-- The genuine all-real transport supremum is AE measurable from the
constructed population's right continuity and the continuous nonlinear law. -/
theorem aemeasurable_runningError (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial)
    (hV : Integrable (fun a => lyapunov control (initial a)) μ) :
    AEMeasurable (runningError control hActivity ν T hT hCoupling hMoment n initial)
      (law μ (Label (n + 1) D)) := by
  apply RightContinuousSupremum.aemeasurable_intervalSup_of_rightContinuous _ _ T hT
  · intro t _
    have hm := measurable_error_at control hActivity ν T hT hCoupling hMoment n initial hinit t
    exact hm.ennreal_ofReal.aemeasurable
  · filter_upwards [ae_empiricalLaw_rightContinuous control n initial μ hinit hV] with p hp
    intro t ht
    have hv' : ContinuousWithinAt v (Ici t) t :=
      (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment).continuousAt.continuousWithinAt
    exact ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt ((hp t ht.1).dist hv')

/-- The all-real moment-error supremum is also AE measurable. -/
theorem aemeasurable_runningMomentError (μ : Measure A) [IsProbabilityMeasure μ]
    (hinit : Measurable initial)
    (hV : Integrable (fun a => lyapunov control (initial a)) μ) :
    AEMeasurable (runningMomentError control hActivity ν T hT hCoupling hMoment n initial)
      (law μ (Label (n + 1) D)) := by
  have hmoment : Continuous (fun μ : MomentLaw κ D => moment μ) := moment_lipschitz.continuous
  apply RightContinuousSupremum.aemeasurable_intervalSup_of_rightContinuous _ _ T hT
  · intro t _
    have hm := (measurable_of_countable (fun z : Configuration (n + 1) D =>
      |moment (empiricalLaw κ (Nat.succ_pos n) z) - moment (v t)|)).comp
      ((ConfigurationTimeDependent.measurable_process control (Nat.succ_pos n) initial hinit).of_uncurry_right (y := t))
    exact hm.ennreal_ofReal.aemeasurable
  · filter_upwards [ae_empiricalLaw_rightContinuous control n initial μ hinit hV] with p hp
    intro t ht
    have hv' : ContinuousWithinAt v (Ici t) t :=
      (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment).continuousAt.continuousWithinAt
    exact ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
      (((hmoment.continuousAt.comp_continuousWithinAt (hp t ht.1)).sub
        (hmoment.continuousAt.comp_continuousWithinAt hv')).abs)

end Row

private theorem ae_runningError_le (n : ℕ) (γ : Measure (Record (n + 1) D))
    [IsProbabilityMeasure γ]
    (hright : γ.map right = Measure.pi (fun _ : Fin (n + 1) => ν.measure)) :
    ∀ᵐ p ∂law γ (Label (n + 1) D),
      runningError control hActivity ν T hT hCoupling hMoment n left p ≤
        empiricalPathDiscrepancy control hActivity ν T hT hCoupling hMoment n T p +
        NonlinearEmpiricalSupremum.runningError control hActivity ν T hT hCoupling hMoment n right p := by
  filter_upwards [PopulationNonlinearError.ae_error_eq_array control hActivity ν T hT
    hCoupling hMoment n right measurable_right γ hright] with p hp
  apply iSup_le
  intro t
  let x := ConfigurationTimeDependent.process control (Nat.succ_pos n) left p t
  let y := DeterministicEnvironmentConfiguration.process control (Nat.succ_pos n) hActivity
    v T hT hv right p t
  have he := hp t t.property.1
  have ht := wasserstein_triangle (empiricalLaw κ (Nat.succ_pos n) x)
    (empiricalLaw κ (Nat.succ_pos n) y) (v t)
  have hxy : ENNReal.ofReal (wasserstein (empiricalLaw κ (Nat.succ_pos n) x)
      (empiricalLaw κ (Nat.succ_pos n) y)) ≤
      empiricalPathDiscrepancy control hActivity ν T hT hCoupling hMoment n T p :=
    le_iSup_of_le t le_rfl
  have hy : ENNReal.ofReal (wasserstein (empiricalLaw κ (Nat.succ_pos n) y) (v t)) ≤
      NonlinearEmpiricalSupremum.runningError control hActivity ν T hT hCoupling hMoment n right p := by
    change ENNReal.ofReal (PopulationNonlinearError.error control hActivity ν T hT hCoupling hMoment
      n right p t) ≤ _
    rw [he]
    exact le_iSup_of_le t le_rfl
  exact (ENNReal.ofReal_le_ofReal ht).trans
    ((le_of_eq (ENNReal.ofReal_add (wasserstein_nonneg _ _) (wasserstein_nonneg _ _))).trans
      (add_le_add hxy hy))

private theorem measure_paired_runningError_gt_tendsto_zero
    (γ : ∀ n, Measure (Record (n + 1) D)) [∀ n, IsProbabilityMeasure (γ n)]
    (hright : ∀ n, (γ n).map right = Measure.pi (fun _ : Fin (n + 1) => ν.measure))
    (hpair : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (law (γ n) (Label (n + 1) D)).real
      {p | ENNReal.ofReal ε < empiricalPathDiscrepancy control hActivity ν T hT hCoupling hMoment n T p})
      atTop (𝓝 0)) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (γ n) (Label (n + 1) D))
      {p | ENNReal.ofReal ε < runningError control hActivity ν T hT hCoupling hMoment n left p})
      atTop (𝓝 0) := by
  have hhalf : 0 < ε / 2 := by positivity
  have hpair' : Tendsto (fun n => (law (γ n) (Label (n + 1) D))
      {p | ENNReal.ofReal (ε/2) < empiricalPathDiscrepancy control hActivity ν T hT hCoupling hMoment n T p})
      atTop (𝓝 0) := by
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hpair (ε/2) hhalf)
    apply (show Tendsto (fun n => ENNReal.ofReal ((law (γ n) (Label (n + 1) D)).real
      {p | ENNReal.ofReal (ε/2) < empiricalPathDiscrepancy control hActivity ν T hT hCoupling hMoment n T p}))
      atTop (𝓝 0) by simpa only [ENNReal.ofReal_zero] using hh).congr'
    exact Eventually.of_forall (fun n => ENNReal.ofReal_toReal (measure_ne_top _ _))
  have hind := NonlinearEmpiricalUniform.measure_runningError_gt_tendsto_zero
    control hActivity ν T hT hCoupling hMoment (fun n => right (N := n + 1) (D := D))
    (fun _ => measurable_right) γ hright (ε/2) hhalf
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto _ atTop (𝓝 (0 : ℝ≥0∞)) by simpa only [zero_add] using hpair'.add hind)
    (fun _ => zero_le _)
  intro n
  let E₁ : Set (Sample (Record (n + 1) D) (Label (n + 1) D)) := {p | ENNReal.ofReal (ε/2) < empiricalPathDiscrepancy control hActivity ν T hT hCoupling hMoment n T p}
  let E₂ : Set (Sample (Record (n + 1) D) (Label (n + 1) D)) := {p | ENNReal.ofReal (ε/2) < NonlinearEmpiricalSupremum.runningError control hActivity ν T hT hCoupling hMoment n right p}
  apply (measure_mono_ae (show {p | ENNReal.ofReal ε < runningError control hActivity ν T hT hCoupling hMoment n left p} ≤ᵐ[law (γ n) (Label (n + 1) D)] (E₁ ∪ E₂ : Set _) from ?_)).trans
    (measure_union_le E₁ E₂)
  filter_upwards [ae_runningError_le control hActivity ν T hT hCoupling hMoment n (γ n) (hright n)] with p hp
  intro he
  by_contra hn
  have h₁ : empiricalPathDiscrepancy control hActivity ν T hT hCoupling hMoment n T p ≤ ENNReal.ofReal (ε/2) :=
    le_of_not_gt (fun h => hn (Or.inl h))
  have h₂ : NonlinearEmpiricalSupremum.runningError control hActivity ν T hT hCoupling hMoment n right p ≤ ENNReal.ofReal (ε/2) :=
    le_of_not_gt (fun h => hn (Or.inr h))
  have hh : ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add hhalf.le hhalf.le]
    congr 1
    ring
  exact (not_lt_of_ge ((hp.trans (add_le_add h₁ h₂)).trans_eq hh)) he

section ManuscriptInitialization
variable {Ω : Type*} [MeasurableSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P]
  (z : ∀ n, Ω → Configuration (n + 1) D) (hz : ∀ n, Measurable (z n))
  (hex : ∀ n, ExchangeableMatching.ExchangeableLaw (P.map (z n)))
  (hΨ : ∀ n, Integrable (fun ω => lyapunov control (z n ω)) P)
  (C : ℝ) (hbound : ∀ n, (∫ ω, lyapunov control (z n ω) ∂P) ≤ C)
  (hconv : TendstoInMeasure P
    (fun n ω => wasserstein (empiricalLaw κ (Nat.succ_pos n) (z n ω)) ν) atTop 0)

include hz hex hΨ hbound hconv

/-- Kenny's uniform empirical-law conclusion for the actual canonical
interacting system, initialized with the exact original vector law. The
initialization, synchronous comparison, and uniform iid error are all derived
from the manuscript assumptions. -/
theorem measure_runningError_gt_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (P.map (z n)) (Label (n + 1) D))
      {p | ENNReal.ofReal ε < runningError control hActivity ν T hT hCoupling hMoment n id p})
      atTop (𝓝 0) := by
  obtain ⟨γ, hp, _he, hl, hr, _hstop, _hpath, hpair⟩ :=
    exists_synchronous_approximation control hActivity ν T hT hCoupling hMoment
      P z hz hex hΨ C hbound hconv
  letI : ∀ n, IsProbabilityMeasure (γ n) := hp
  letI : ∀ n, IsProbabilityMeasure (P.map (z n)) :=
    fun n => isProbabilityMeasure_map (hz n).aemeasurable
  have hc := measure_paired_runningError_gt_tendsto_zero
    control hActivity ν T hT hCoupling hMoment γ hr hpair ε hε
  apply hc.congr'
  apply Eventually.of_forall
  intro n
  have hV : Integrable (fun a : Configuration (n + 1) D => lyapunov control a)
      (P.map (z n)) :=
    integrable_initial_of_map control (P.map (z n)) P id (z n)
      measurable_id (hz n) (by simp) (hΨ n)
  have hm := aemeasurable_runningError control hActivity ν T hT hCoupling hMoment
    n id (P.map (z n)) measurable_id hV
  have hmap : (law (γ n) (Label (n + 1) D)).map (initialProjection (left (N := n+1) (D := D))) =
      law (P.map (z n)) (Label (n + 1) D) := by
    rw [initialProjection_map left (γ n) measurable_left, hl n]
  have hs : NullMeasurableSet
      {p | ENNReal.ofReal ε < runningError control hActivity ν T hT hCoupling hMoment n id p}
      ((law (γ n) (Label (n + 1) D)).map (initialProjection (left (N := n+1) (D := D)))) := by
    rw [hmap]
    exact nullMeasurableSet_lt aemeasurable_const hm
  have heq := Measure.map_apply₀
    (measurable_initialProjection left measurable_left).aemeasurable hs
  rw [hmap] at heq
  exact heq.symm

/-- Equivalent real-valued probability formulation of the canonical uniform
empirical transport limit. -/
theorem probability_runningError_gt_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (P.map (z n)) (Label (n + 1) D)).real
      {p | ENNReal.ofReal ε < runningError control hActivity ν T hT hCoupling hMoment n id p})
      atTop (𝓝 0) := by
  exact ENNReal.tendsto_toReal ENNReal.zero_ne_top |>.comp
    (measure_runningError_gt_tendsto_zero control hActivity ν T hT hCoupling hMoment
      P z hz hex hΨ C hbound hconv ε hε)

/-- The generalized empirical moment converges uniformly in time in
probability, directly through the proved transport-moment Lipschitz bound. -/
theorem measure_runningMomentError_gt_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (P.map (z n)) (Label (n + 1) D))
      {p | ENNReal.ofReal ε < runningMomentError control hActivity ν T hT hCoupling hMoment n id p})
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (measure_runningError_gt_tendsto_zero control hActivity ν T hT hCoupling hMoment
      P z hz hex hΨ C hbound hconv ε hε) (fun _ => zero_le _)
  intro n
  exact measure_mono (fun p hp => hp.trans_le
    (runningMomentError_le_runningError control hActivity ν T hT hCoupling hMoment n id p))

/-- Real probability formulation of the uniform generalized-moment limit. -/
theorem probability_runningMomentError_gt_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (P.map (z n)) (Label (n + 1) D)).real
      {p | ENNReal.ofReal ε < runningMomentError control hActivity ν T hT hCoupling hMoment n id p})
      atTop (𝓝 0) := by
  exact ENNReal.tendsto_toReal ENNReal.zero_ne_top |>.comp
    (measure_runningMomentError_gt_tendsto_zero control hActivity ν T hT hCoupling hMoment
      P z hz hex hΨ C hbound hconv ε hε)

end ManuscriptInitialization

end CarryingCapacity.PopulationEmpiricalLimit
