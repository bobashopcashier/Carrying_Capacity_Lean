import CarryingCapacity.PrescribedConfigurationLocalization

/-!
# Strong frozen equations on the supplied Poisson space

The actual frozen path solves the paper's accepted-jump equation with its
genuine left state and the supplied measures. The finite height cap disappears
by the derived active-set bound. Separating coordinate equations give pathwise
uniqueness without an initial moment or a candidate activity hypothesis.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal Topology

namespace CarryingCapacity.PrescribedConfigurationFrozenEquation
open ConfigurationLocalization PrescribedPoissonRealization PrescribedConfigurationLocalization

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N) (initial : A → Configuration N D)
  (M : Label N D → Ω → Measure (ℝ × ℝ)) (ξ : Ω → A)

/-- The actual predictable left state of the reconstructed frozen path. -/
def preState (n : ℕ) (ω : Ω) (t : ℝ) : Configuration N D :=
  InitialFrozenPredictable.preState (active control hN n) jump (rate κ q hN) initial
    (rateBound control hN n) 0 (record (Label N D) M ξ ω) t

/-- The physical freezing indicator, with no artificial height cutoff. -/
def incrementAt (n : ℕ) (pre : ℝ → Configuration N D)
    (f : Configuration N D → ℝ) (j : Label N D) (T : ℝ) (z : ℝ × ℝ) : ℝ :=
  if z.1 ∈ Ioc 0 T ∧ z.2 ≤ rate κ q hN j (pre z.1) ∧
      lyapunov control (pre z.1) < (n : ℝ) + 1
  then f (jump j (pre z.1)) - f (pre z.1) else 0

def increment (n : ℕ) (f : Configuration N D → ℝ) (j : Label N D)
    (T : ℝ) (ω : Ω) (z : ℝ × ℝ) : ℝ :=
  incrementAt control hN n (preState control hN initial M ξ n ω) f j T z

omit [MeasurableSpace Ω] [MeasurableSpace A] in
/-- The cap is redundant because the actual empirical rates are bounded on the active set. -/
theorem increment_eq_horizonIncrement (n : ℕ) (f : Configuration N D → ℝ)
    (j : Label N D) (T : ℝ) (ω : Ω) :
    increment control hN initial M ξ n f j T ω =
      (fun z => InitialFrozenCompensation.horizonIncrement (active control hN n) jump
        (rate κ q hN) initial (rateBound control hN n) 0 f j T
        (record (Label N D) M ξ ω,z)) := by
  funext z
  rw [InitialFrozenCompensation.horizonIncrement_eq_localizedIncrement]
  let x := preState control hN initial M ξ n ω z.1
  change (if z.1 ∈ Ioc 0 T ∧ z.2 ≤ rate κ q hN j x ∧ lyapunov control x < (n : ℝ) + 1
    then f (jump j x) - f x else 0) =
    (if z.1 ∈ Ioc 0 T ∧ x ∈ active control hN n ∧ z.2 ≤ rateBound control hN n ∧
      z.2 ≤ rate κ q hN j x then f (jump j x) - f x else 0)
  have hx : x ∈ active control hN n ↔ lyapunov control x < (n : ℝ) + 1 := mem_active control hN n x
  by_cases ht : z.1 ∈ Ioc 0 T
  · by_cases ha : x ∈ active control hN n
    · have hcap := rate_le_bound control hN n x ha j
      by_cases hr : z.2 ≤ rate κ q hN j x
      · have hu : z.2 ≤ rateBound control hN n := hr.trans hcap
        simp only [ht, ha, (hx.mp ha), hr, hu, and_self, ↓reduceIte]
      · simp only [ht, ha, (hx.mp ha), hr, and_false, false_and, ↓reduceIte]
    · have hv : ¬ lyapunov control x < (n : ℝ) + 1 := mt hx.mpr ha
      simp only [ht, ha, hv, and_false, false_and, ↓reduceIte]
  · simp only [ht, false_and, ↓reduceIte]

/-- An inactive state permits only self-jumps, exactly encoding freezing. -/
def frozenJump (n : ℕ) (j : Label N D) (x : Configuration N D) : Configuration N D :=
  if lyapunov control x < (n : ℝ) + 1 then jump j x else x

omit [MeasurableSpace Ω] [MeasurableSpace A] in
theorem incrementAt_eq_generic (n : ℕ) (pre : ℝ → Configuration N D)
    (f : Configuration N D → ℝ) (j : Label N D) (T : ℝ) :
    incrementAt control hN n pre f j T =
      TimeDependentEquationUniqueness.increment (frozenJump control n)
        (fun j _ => rate κ q hN j) pre f j T := by
  funext z
  by_cases ha : lyapunov control (pre z.1) < (n : ℝ) + 1
  · simp only [incrementAt, TimeDependentEquationUniqueness.increment, frozenJump,
      ha, and_true, ↓reduceIte]
  · simp only [incrementAt, TimeDependentEquationUniqueness.increment, frozenJump,
      ha, and_false, ↓reduceIte, sub_self, ite_self]

variable (P : Measure Ω) [IsProbabilityMeasure P]
  (hM : ∀ j, Measurable (M j)) (hPoisson : PoissonObservationLaw.HasDisjointLaws P (Label N D) M)
  (hξ : Measurable ξ) (hIndependent : IndepFun ξ (fun ω => fun j => M j ω) P)
include hM hPoisson hξ hIndependent
attribute [local irreducible] PrescribedPoissonRealization.record

theorem ae_tendsto_preState (n : ℕ) : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
    Tendsto (path control hN initial M ξ n ω) (𝓝[<] t)
      (𝓝 (preState control hN initial M ξ n ω t)) := by
  have hc := InitialFrozenPredictable.ae_tendsto_preState (active control hN n) jump
    (rate κ q hN) initial (P.map ξ)
  filter_upwards [ae_record (Label N D) M ξ P hM hPoisson hξ hIndependent hc] with ω hω
  exact hω (rateBound control hN n) 0

/-- Every accepted frozen test increment is integrable against each supplied measure. -/
theorem ae_integrable_increment (n : ℕ) : ∀ᵐ ω ∂P, ∀ (T : ℝ)
    (f : Configuration N D → ℝ) (j : Label N D),
    Integrable (increment control hN initial M ξ n f j T ω) (M j ω) := by
  have hc := InitialFrozenCountingIdentity.ae_integrable_horizonIncrement
    (active control hN n) jump (rate κ q hN) initial (P.map ξ)
  filter_upwards [ae_record (Label N D) M ξ P hM hPoisson hξ hIndependent hc,
    ae_countingMeasure_noise (Label N D) M P hM hPoisson] with ω hω hNoise
  intro T f j
  rw [increment_eq_horizonIncrement]
  have hi := hω (rateBound control hN n) 0 T f j
  have he : MarkedNoise.countingMeasure j (record (Label N D) M ξ ω).2 = M j ω := by
    simpa only [record] using hNoise j
  rwa [he] at hi

/-- The frozen path satisfies the original supplied-measure equation on one event for all horizons. -/
theorem ae_counting_identity (n : ℕ) (f : Configuration N D → ℝ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ,
    f (path control hN initial M ξ n ω T) - f (initial (ξ ω)) =
      ∑ j, ∫ z, increment control hN initial M ξ n f j T ω z ∂M j ω := by
  have hc := InitialFrozenCountingIdentity.ae_testFunction_counting_identity
    (active control hN n) jump (rate κ q hN) initial (P.map ξ) f
  filter_upwards [ae_record (Label N D) M ξ P hM hPoisson hξ hIndependent hc,
    ae_countingMeasure_noise (Label N D) M P hM hPoisson,
    PrescribedConfigurationLocalization.ae_initial control hN initial M ξ P hM hPoisson hξ hIndependent n]
    with ω hω hNoise hzero
  intro T
  have he := hω (rateBound control hN n) 0 T
  change f (path control hN initial M ξ n ω T) - f (path control hN initial M ξ n ω 0) = _ at he
  rw [hzero] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro j _
  rw [increment_eq_horizonIncrement]
  congr 1
  simpa only [record] using hNoise j

/-- Coordinate equations give pathwise uniqueness for every frozen level,
without a moment or bounded-activity condition on the candidate. -/
theorem ae_unique_of_coordinate_equations (n : ℕ) (X : Ω → ℝ → Configuration N D)
    (hcadlag : ∀ᵐ ω ∂P,
      (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (X ω) (Ici t) t) ∧
      (∀ t : ℝ, 0 < t → ∃ y : Configuration N D, Tendsto (X ω) (𝓝[<] t) (𝓝 y)))
    (hzero : ∀ᵐ ω ∂P, X ω 0 = initial (ξ ω))
    (heq : ∀ i : Fin N × Fin D, ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      (X ω T i.1 i.2 : ℝ) - (initial (ξ ω) i.1 i.2 : ℝ) =
        ∑ j, ∫ z, incrementAt control hN n (Function.leftLim (X ω))
          (fun x => (x i.1 i.2 : ℝ)) j T z ∂M j ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → X ω t = path control hN initial M ξ n ω t := by
  have hactual := ae_all_iff.mpr (fun i : Fin N × Fin D => ae_counting_identity
    control hN initial M ξ P hM hPoisson hξ hIndependent n
      (fun x => (x i.1 i.2 : ℝ)))
  filter_upwards [hcadlag,hzero,ae_all_iff.mpr heq,hactual,
    PrescribedConfigurationLocalization.ae_cadlag control hN initial M ξ P hM hPoisson hξ hIndependent n,
    PrescribedConfigurationLocalization.ae_initial control hN initial M ξ P hM hPoisson hξ hIndependent n,
    ae_tendsto_preState control hN initial M ξ P hM hPoisson hξ hIndependent n]
    with ω hc hz hEq haEq ha hazero hapre
  have hxpre : ∀ t : ℝ, 0 < t →
      Tendsto (X ω) (𝓝[<] t) (𝓝 (Function.leftLim (X ω) t)) := by
    intro t ht
    obtain ⟨y,hy⟩ := hc.2 t ht
    rw [leftLim_eq_of_tendsto (neBot_iff.mp inferInstance) hy]
    exact hy
  apply TimeDependentEquationUniqueness.eq_of_separating_counting_equations
    (fun i : Fin N × Fin D => fun x : Configuration N D => (x i.1 i.2 : ℝ))
    (fun x y hxy => by
      funext i d
      have h : (x i d : ℝ) = (y i d : ℝ) := hxy (i,d)
      exact_mod_cast h)
    (frozenJump control n) (fun j _ => rate κ q hN j) (fun j => M j ω)
    (X ω) (path control hN initial M ξ n ω)
    (Function.leftLim (X ω)) (preState control hN initial M ξ n ω)
    hc.1 ha.1 hxpre hapre (hz.trans hazero.symm)
  · intro i T hT
    rw [hz]
    simpa only [incrementAt_eq_generic] using hEq i ⟨T,hT⟩
  · intro i T hT
    rw [hazero]
    simpa only [increment, incrementAt_eq_generic] using haEq i T

end CarryingCapacity.PrescribedConfigurationFrozenEquation
