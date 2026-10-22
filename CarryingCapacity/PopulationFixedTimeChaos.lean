import CarryingCapacity.CoupledLawConvergence
import CarryingCapacity.PopulationFocalApproximation
import CarryingCapacity.PopulationEmpiricalLimit

/-!
# Fixed-time chaos for the actual canonical population

The first k coordinates are padded by the zero state when the population has
fewer than k particles. This affects only finitely many rows. At every fixed
time, the genuine focal path approximation forces exact vector agreement with
high probability because unequal states have adapted distance at least one.
The independent comparison vector has exactly the product nonlinear law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators ENNReal Topology

namespace CarryingCapacity.PopulationFixedTimeChaos
open CommonInitialNoise ConfigurationLocalization PopulationCouplingInitialization

/-- The first k coordinates, with zero padding for the finitely many small rows. -/
def first {N D : ℕ} (k : ℕ) (z : Configuration N D) : Fin k → State D :=
  fun i => if h : i.val < N then z ⟨i.val, h⟩ else 0

@[simp] theorem first_cast {N D k : ℕ} (hkn : k ≤ N) (z : Configuration N D) (i : Fin k) :
    first k z i = z (Fin.castLE hkn i) := by
  simp only [first, dif_pos (lt_of_lt_of_le i.isLt hkn)]
  rfl

theorem measurable_first {N D : ℕ} (k : ℕ) : Measurable (first (N := N) (D := D) k) :=
  measurable_of_countable _

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)

local notation "v" => NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment
local notation "hv" => Continuous.continuousOn (NonlinearFixedPoint.continuous_environment control hActivity ν T hT hCoupling hMoment)

/-- The actual interacting first-k vector on an arbitrary initial-record space. -/
def vector {A : Type*} {N : ℕ} (hN : 0 < N) (initial : A → Configuration N D)
    (k : ℕ) (t : ℝ) (p : Sample A (Label N D)) : Fin k → State D :=
  first k (ConfigurationTimeDependent.process control hN initial p t)

theorem measurable_vector {A : Type*} [MeasurableSpace A] {N : ℕ} (hN : 0 < N)
    (initial : A → Configuration N D) (hinit : Measurable initial) (k : ℕ) (t : ℝ) :
    Measurable (vector control hN initial k t) :=
  (measurable_first k).comp
    ((ConfigurationTimeDependent.measurable_process control hN initial hinit).of_uncurry_right)

/-- The first-k vector of the actual independent nonlinear particles. -/
def comparison {A : Type*} {N : ℕ} (initial : A → Configuration N D)
    (k : ℕ) (t : ℝ) (p : Sample A (Label N D)) : Fin k → State D :=
  first k (fun i => NonlinearParticleArray.process control hActivity ν T hT hCoupling hMoment initial i p t)

theorem measurable_comparison {A : Type*} [MeasurableSpace A] {N : ℕ}
    (initial : A → Configuration N D) (hinit : Measurable initial) (k : ℕ) (t : ℝ) :
    Measurable (comparison control hActivity ν T hT hCoupling hMoment initial k t) :=
  (measurable_first k).comp (measurable_pi_lambda _ (fun i =>
    NonlinearParticleArray.measurable_process_at control hActivity ν T hT hCoupling hMoment
      initial hinit i t))

/-- The product of k copies of the actual nonlinear marginal. -/
def productLaw (k : ℕ) (t : Icc (0 : ℝ) T) : ProbabilityMeasure (Fin k → State D) := by
  let μ := ((NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hMoment).val t).measure
  letI : IsProbabilityMeasure μ :=
    ((NonlinearFixedPoint.fixedCurve control hActivity ν T hT hCoupling hMoment).val t).probability
  letI : ∀ _ : Fin k, IsProbabilityMeasure μ := fun _ => inferInstance
  exact ⟨Measure.pi (fun _ : Fin k => μ), ⟨by simp only [Measure.pi_univ, measure_univ, Finset.prod_const_one]⟩⟩

/-- Once N is at least k, the comparison vector has exactly the product law. -/
theorem comparison_map {A : Type*} [MeasurableSpace A] {N : ℕ}
    (initial : A → Configuration N D) (hinit : Measurable initial)
    (γ : Measure A) [IsProbabilityMeasure γ]
    (hright : γ.map initial = Measure.pi (fun _ : Fin N => ν.measure))
    (k : ℕ) (hkn : k ≤ N) (t : Icc (0 : ℝ) T) :
    (law γ (Label N D)).map (comparison control hActivity ν T hT hCoupling hMoment initial k t) =
      (productLaw control hActivity ν T hT hCoupling hMoment k t).toMeasure := by
  have hinj : Function.Injective (Fin.castLE hkn) := Fin.castLE_injective hkn
  have hind := (NonlinearParticleArray.independent_at control hActivity ν T hT hCoupling hMoment
    initial hinit γ hright t).precomp hinj
  have hm (i : Fin k) := NonlinearParticleArray.measurable_process_at control hActivity ν T hT
    hCoupling hMoment initial hinit (Fin.castLE hkn i) t
  have he : comparison control hActivity ν T hT hCoupling hMoment initial k t =
      fun p i => NonlinearParticleArray.process control hActivity ν T hT hCoupling hMoment
        initial (Fin.castLE hkn i) p t := by
    funext p i
    exact first_cast hkn _ i
  rw [he, (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hm i).aemeasurable)).mp hind]
  simp_rw [NonlinearParticleArray.process_marginal control hActivity ν T hT hCoupling hMoment
    initial hinit γ hright]
  rfl

/-- An unequal first-k vector entails a focal discrepancy exceeding one half.
The comparison configuration is identified with the actual independent array
on the proved common probability-one event. -/
theorem ae_mismatch_implies_focal (n k : ℕ) (hkn : k ≤ n + 1)
    (γ : Measure (Record (n + 1) D)) [IsProbabilityMeasure γ]
    (hright : γ.map right = Measure.pi (fun _ : Fin (n + 1) => ν.measure))
    (t : Icc (0 : ℝ) T) :
    ∀ᵐ p ∂law γ (Label (n + 1) D),
      vector control (Nat.succ_pos n) left k t p ≠
          comparison control hActivity ν T hT hCoupling hMoment right k t p →
        ENNReal.ofReal (1 / 2 : ℝ) < PopulationFocalApproximation.focalPathDiscrepancy
          control hActivity ν T hT hCoupling hMoment n k T p := by
  filter_upwards [NonlinearParticleConfiguration.ae_path_eq_configuration control hActivity ν T hT
    hCoupling hMoment right measurable_right γ hright (Nat.succ_pos n)] with p hp
  intro hne
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have he := congrFun (hp t t.property.1) (Fin.castLE hkn i)
  change NonlinearParticleArray.process control hActivity ν T hT hCoupling hMoment right
    (Fin.castLE hkn i) p t = _ at he
  simp only [vector, comparison, first_cast hkn] at hi
  rw [he] at hi
  have hsep := one_le_adaptedDistance_of_ne (κ := κ) _ _ hi
  have hdom : ENNReal.ofReal (adaptedDistance κ
      (ConfigurationTimeDependent.process control (Nat.succ_pos n) left p t (Fin.castLE hkn i))
      (DeterministicEnvironmentConfiguration.process control (Nat.succ_pos n) hActivity
        v T hT hv right p t (Fin.castLE hkn i))) ≤
      PopulationCouplingRemoval.coordinateRunningCost control (Nat.succ_pos n) hActivity
        v T hT hv left right (Fin.castLE hkn i) T p :=
    le_iSup_of_le t le_rfl
  apply (PopulationFocalApproximation.lt_focalPathDiscrepancy_iff control hActivity ν T hT
    hCoupling hMoment n k hkn T p _).mpr
  refine ⟨i, lt_of_lt_of_le ?_ hdom⟩
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr (lt_of_lt_of_le (by norm_num) hsep)


/-- Weak convergence on any genuine coupled initial family, using the proved
focal error as the sole intermediate comparison estimate. -/
theorem coupled_laws_tendsto
    (γ : ∀ n, Measure (Record (n + 1) D)) [∀ n, IsProbabilityMeasure (γ n)]
    (hright : ∀ n, (γ n).map right = Measure.pi (fun _ : Fin (n + 1) => ν.measure))
    (k : ℕ) (t : Icc (0 : ℝ) T)
    (hfocal : Tendsto (fun n => (law (γ n) (Label (n + 1) D)).real
      {p | ENNReal.ofReal (1 / 2 : ℝ) < PopulationFocalApproximation.focalPathDiscrepancy
        control hActivity ν T hT hCoupling hMoment n k T p}) atTop (𝓝 0)) :
    Tendsto (fun n => CoupledLawConvergence.imageLaw (law (γ n) (Label (n + 1) D))
      (vector control (Nat.succ_pos n) left k t)
      (measurable_vector control (Nat.succ_pos n) left measurable_left k t))
      atTop (𝓝 (productLaw control hActivity ν T hT hCoupling hMoment k t)) := by
  apply CoupledLawConvergence.tendsto_imageLaw_of_mismatch _ _
    (fun n => comparison control hActivity ν T hT hCoupling hMoment right k t)
    (fun n => measurable_vector control (Nat.succ_pos n) left measurable_left k t)
    (fun n => measurable_comparison control hActivity ν T hT hCoupling hMoment right measurable_right k t)
  · filter_upwards [eventually_ge_atTop k] with n hn
    exact comparison_map control hActivity ν T hT hCoupling hMoment right measurable_right
      (γ n) (hright n) k (hn.trans (Nat.le_succ n)) t
  · apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hfocal
    filter_upwards [eventually_ge_atTop k] with n hn
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono_ae (ae_mismatch_implies_focal control hActivity ν T hT hCoupling hMoment
        n k (hn.trans (Nat.le_succ n)) (γ n) (hright n) t))

/-- The first-k law on the canonical original-vector/noise probability space. -/
def canonicalLaw (n : ℕ) (α : ProbabilityMeasure (Configuration (n + 1) D))
    (k : ℕ) (t : ℝ) : ProbabilityMeasure (Fin k → State D) :=
  CoupledLawConvergence.imageLaw (law α.toMeasure (Label (n + 1) D))
    (vector control (Nat.succ_pos n) id k t)
    (measurable_vector control (Nat.succ_pos n) id measurable_id k t)

/-- Fixed-time Corollary 6.4 for the actual canonical population. All stochastic
comparison estimates are derived from the original initialization hypotheses.
The padding disappears as soon as the population has at least k particles. -/
theorem canonical_laws_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (z : ∀ n, Ω → Configuration (n + 1) D) (hz : ∀ n, Measurable (z n))
    (hex : ∀ n, ExchangeableMatching.ExchangeableLaw (P.map (z n)))
    (hΨ : ∀ n, Integrable (fun ω => lyapunov control (z n ω)) P)
    (C : ℝ) (hbound : ∀ n, (∫ ω, lyapunov control (z n ω) ∂P) ≤ C)
    (hconv : TendstoInMeasure P
      (fun n ω => wasserstein (empiricalLaw κ (Nat.succ_pos n) (z n ω)) ν) atTop 0)
    (k : ℕ) (t : Icc (0 : ℝ) T) :
    Tendsto (fun n => canonicalLaw control n (CoupledLawConvergence.imageLaw P (z n) (hz n)) k t)
      atTop (𝓝 (productLaw control hActivity ν T hT hCoupling hMoment k t)) := by
  obtain ⟨γ, hp, _he, hl, hr, _hs, _ha, _hm, hf⟩ :=
    PopulationFocalApproximation.exists_full_synchronous_approximation
      control hActivity ν T hT hCoupling hMoment P z hz hex hΨ C hbound hconv
  letI : ∀ n, IsProbabilityMeasure (γ n) := hp
  have hc := coupled_laws_tendsto control hActivity ν T hT hCoupling hMoment γ hr k t
    (hf k (1 / 2) (by norm_num))
  have heq (n : ℕ) :
      CoupledLawConvergence.imageLaw (law (γ n) (Label (n + 1) D))
        (vector control (Nat.succ_pos n) left k t)
        (measurable_vector control (Nat.succ_pos n) left measurable_left k t) =
      canonicalLaw control n (CoupledLawConvergence.imageLaw P (z n) (hz n)) k t := by
    apply Subtype.ext
    change (law (γ n) (Label (n + 1) D)).map (vector control (Nat.succ_pos n) left k t) =
      (law (P.map (z n)) (Label (n + 1) D)).map (vector control (Nat.succ_pos n) id k t)
    rw [← hl n, ← PopulationEmpiricalLimit.initialProjection_map left (γ n) measurable_left,
      Measure.map_map (measurable_vector control (Nat.succ_pos n) id measurable_id k t)
        (PopulationEmpiricalLimit.measurable_initialProjection left measurable_left)]
    rfl
  exact hc.congr' (Eventually.of_forall heq)

end CarryingCapacity.PopulationFixedTimeChaos
