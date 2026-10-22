import CarryingCapacity.Framework
import CarryingCapacity.ModelTransport

/-!
# A verified quadratic-feedback model in the general framework

The actual rates are `birth * x` and `x * a(M₂(μ))`. This file instantiates
`Rates` and proves the manuscript's coupling, activity, and Lyapunov hypotheses
for arbitrary nonnegative globally Lipschitz per-capita mortality. The cubic
Lyapunov function supplies one admissible exponent, rather than the full family
of real exponents greater than two. No stochastic existence or limit theorem
is asserted by this instance.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace CarryingCapacity.QuadraticModel

private instance : IsEmpty {p : Fin 1 × Fin 1 // p.1 ≠ p.2} :=
  ⟨fun p => p.property (Subsingleton.elim _ _)⟩

/-- There are exactly two jumps in the single-type model. -/
theorem sum_jumps (f : Jump 1 → ℝ) :
    ∑ h, f h = f (Jump.birth 0) + f (Jump.death 0) := by
  simp [Jump, Fintype.sum_sum_type, Jump.birth, Jump.death]

/-- Quadratic moment-feedback birth and death rates, with no mutations. -/
def rates (birth : ℝ) (hbirth : 0 ≤ birth) (a : MomentMortality) :
    Rates 1 (MomentLaw MomentScale.quadratic 1) where
  rate h x μ := match h with
    | .inl (.inl i) => birth * (x i : ℝ)
    | .inl (.inr i) => a.rate (moment μ) * (x i : ℝ)
    | .inr p => False.elim (p.property (Subsingleton.elim _ _))
  nonnegative h x μ := by
    rcases h with (i | i) | p
    · exact mul_nonneg hbirth (Nat.cast_nonneg _)
    · exact mul_nonneg (a.nonneg _ (moment_nonneg μ)) (Nat.cast_nonneg _)
    · exact False.elim (p.property (Subsingleton.elim _ _))
  invalid_zero h x μ hi := by
    rcases h with (i | i) | p
    · exact False.elim (hi trivial)
    · simp only [Jump.Admissible, not_lt] at hi
      have hx : x i = 0 := Nat.eq_zero_of_le_zero hi
      simp [hx]
    · exact False.elim (p.property (Subsingleton.elim _ _))

@[simp] theorem advance_birth (x : State 1) :
    Jump.advance (Jump.birth 0) x 0 = x 0 + 1 := by
  simp [Jump.advance, Jump.birth]

@[simp] theorem advance_death (x : State 1) :
    Jump.advance (Jump.death 0) x 0 = x 0 - 1 := by
  by_cases h : 0 < x 0
  · simp [Jump.advance, Jump.death, h]
  · have hx : x 0 = 0 := by omega
    simp [Jump.advance, Jump.death, h, hx]

/-- The finite-sum generator agrees exactly with the boundary-aware scalar one. -/
theorem generator_eq (birth : ℝ) (hbirth : 0 ≤ birth) (a : MomentMortality)
    (μ : MomentLaw MomentScale.quadratic 1) (f : ℕ → ℝ) (x : State 1) :
    (rates birth hbirth a).generator μ (fun y => f (y 0)) x =
      Models.generator birth (a.rate (moment μ)) f (x 0) := by
  rw [Rates.generator, sum_jumps]
  simp [rates, Jump.birth, Jump.death, Models.generator, Jump.advance]
  split_ifs with h
  · simp
  · have hx : x 0 = 0 := by omega
    simp [hx]

/-- The general positive coupling sum contains both the common-jump and excess
rate terms proved in `Models`. -/
theorem couplingActivity_eq (birth : ℝ) (hbirth : 0 ≤ birth) (a : MomentMortality)
    (μ ν : MomentLaw MomentScale.quadratic 1) (x y : State 1) :
    couplingActivity MomentScale.quadratic (rates birth hbirth a) x y μ ν =
      Models.birthCouplingCost birth (x 0) (y 0) +
      Models.deathCouplingCost (a.rate (moment μ)) (a.rate (moment ν)) (x 0) (y 0) := by
  rw [couplingActivity, sum_jumps]
  simp only [quadratic_one_distance, advance_birth, advance_death]
  rfl

/-- Exact agreement of weighted activity with the scalar calculation. -/
theorem weightedActivity_eq (birth : ℝ) (hbirth : 0 ≤ birth) (a : MomentMortality)
    (μ : MomentLaw MomentScale.quadratic 1) (x : State 1) :
    weightedActivity MomentScale.quadratic (rates birth hbirth a) x μ =
      Models.quadraticActivity birth (a.rate (moment μ)) (x 0) := by
  rw [weightedActivity, sum_jumps]
  simp only [quadratic_one_distance, advance_birth, advance_death]
  rfl

/-- Assumption 2.2 holds with the explicit coefficient `3 * birth + 2 * Lip(a)`. -/
theorem couplingBound (birth : ℝ) (hbirth : 0 ≤ birth) (a : MomentMortality) :
    MomentCouplingBound MomentScale.quadratic (rates birth hbirth a) := by
  have hL := a.constant_nonneg
  refine ⟨3 * birth + 2 * a.constant, by positivity, ?_⟩
  intro x y μ ν
  rw [couplingActivity_eq, quadratic_one_distance, quadratic_one_weight,
    quadratic_one_weight]
  exact quadratic_model_coupling_standard birth hbirth a μ ν (x 0) (y 0)

/-- Assumption 2.3 holds with `3 * birth + 2 * a(0) + 2 * Lip(a)`. -/
theorem activityBound (birth : ℝ) (hbirth : 0 ≤ birth) (a : MomentMortality) :
    MomentActivityBound MomentScale.quadratic (rates birth hbirth a) := by
  refine ⟨3 * birth + 2 * a.rate 0 + 2 * a.constant, ?_, ?_⟩
  · have ha := a.nonneg 0 (le_refl 0)
    have hL := a.constant_nonneg
    positivity
  · intro x μ
    rw [weightedActivity_eq, quadratic_one_weight]
    exact quadratic_model_activity birth hbirth a μ (x 0)

/-- Assumption 2.5 is verified by `Ψ(x) = 1 + x³`. -/
def lyapunovControl (birth : ℝ) (hbirth : 0 ≤ birth) (a : MomentMortality) :
    LyapunovControl MomentScale.quadratic (rates birth hbirth a) where
  function x := 1 + (x 0 : ℝ)^3
  dominates x := by
    rw [quadratic_one_weight]
    exact Models.cubic_lyapunov_dominates (x 0)
  superlinear := by
    have h : Tendsto (fun x : State 1 => populationSize x / 2)
        (comap populationSize atTop) atTop :=
      tendsto_comap.atTop_div_const (by norm_num : (0 : ℝ) < 2)
    apply tendsto_atTop_mono _ h
    intro x
    simpa [populationSize, quadratic_one_weight] using Models.cubic_lyapunov_ratio_lower (x 0)
  drift := by
    refine ⟨7 * birth, by positivity, ?_⟩
    intro x μ _
    rw [generator_eq birth hbirth a μ (fun n => 1 + (n : ℝ)^3) x]
    have hi : 0 ≤ ∫ y : State 1, (1 + (y 0 : ℝ)^3) ∂μ.measure := by
      apply integral_nonneg
      intro y
      positivity
    have hh := quadratic_model_lyapunov birth hbirth a μ (x 0)
    nlinarith

end CarryingCapacity.QuadraticModel
