import CarryingCapacity.Transport

/-!
# The two rate frameworks

This file records the ORIGINAL paper's total-variation assumptions separately
from the revised manuscript's moment-adapted assumptions. These structures are
hypotheses, not existence proofs. No field asserts a mean-field limit, a Poisson
construction, or propagation of chaos.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace CarryingCapacity

/-- Births, deaths, and changes between two distinct types. -/
abbrev Jump (D : ℕ) := (Fin D ⊕ Fin D) ⊕ {p : Fin D × Fin D // p.1 ≠ p.2}

namespace Jump

variable {D : ℕ}

def birth (i : Fin D) : Jump D := Sum.inl (Sum.inl i)
def death (i : Fin D) : Jump D := Sum.inl (Sum.inr i)
def mutation (i j : Fin D) (h : i ≠ j) : Jump D := Sum.inr ⟨(i,j),h⟩

def source : Jump D → Fin D
  | .inl (.inl i) => i
  | .inl (.inr i) => i
  | .inr p => p.val.1

def Admissible : Jump D → State D → Prop
  | .inl (.inl _), _ => True
  | .inl (.inr i), x => 0 < x i
  | .inr p, x => 0 < x p.val.1

instance (h : Jump D) (x : State D) : Decidable (Admissible h x) := by
  unfold Admissible
  split <;> infer_instance

/-- Invalid jumps act as the identity, matching the manuscript's T_h. -/
def advance : Jump D → State D → State D
  | .inl (.inl i), x => Function.update x i (x i + 1)
  | .inl (.inr i), x => if 0 < x i then Function.update x i (x i - 1) else x
  | .inr p, x => if 0 < x p.val.1 then
      Function.update (Function.update x p.val.1 (x p.val.1 - 1)) p.val.2
        (x p.val.2 + 1) else x

theorem advance_of_invalid (h : Jump D) (x : State D) (hx : ¬Admissible h x) :
    advance h x = x := by
  rcases h with (i | i) | p
  · exact False.elim (hx trivial)
  · simp only [advance, Admissible] at *
    exact if_neg hx
  · simp only [advance, Admissible] at *
    exact if_neg hx

end Jump

/-- A finite family of nonnegative finite-valued jump rates. -/
structure Rates (D : ℕ) (Law : Type*) where
  rate : Jump D → State D → Law → ℝ
  nonnegative : ∀ h x μ, 0 ≤ rate h x μ
  invalid_zero : ∀ h x μ, ¬Jump.Admissible h x → rate h x μ = 0

namespace Rates

variable {D : ℕ} {Law : Type*} (q : Rates D Law)

def generator (μ : Law) (f : State D → ℝ) (x : State D) : ℝ :=
  ∑ h, q.rate h x μ * (f (Jump.advance h x) - f x)

def totalRate (x : State D) (μ : Law) : ℝ := ∑ h, q.rate h x μ

@[simp] theorem generator_const (μ : Law) (c : ℝ) (x : State D) :
    q.generator μ (fun _ => c) x = 0 := by
  simp [generator]

theorem generator_add (μ : Law) (f g : State D → ℝ) (x : State D) :
    q.generator μ (fun y => f y + g y) x = q.generator μ f x + q.generator μ g x := by
  unfold generator
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  ring

theorem generator_smul (μ : Law) (a : ℝ) (f : State D → ℝ) (x : State D) :
    q.generator μ (fun y => a * f y) x = a * q.generator μ f x := by
  unfold generator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

end Rates

/-- The countable-state total-variation distance in the original paper. -/
def totalVariation {D : ℕ} (μ ν : ProbabilityMeasure (State D)) : ℝ :=
  (1 / 2 : ℝ) * ∑' x, |((μ : Measure (State D)) {x}).toReal -
    ((ν : Measure (State D)) {x}).toReal|

/-- Original Assumption 2.1. The laws here need not have a finite moment. -/
structure OriginalAssumptions {D : ℕ} (q : Rates D (ProbabilityMeasure (State D))) : Prop where
  empty_source : ∀ h x μ, x (Jump.source h) = 0 → q.rate h x μ = 0
  bounds : ∃ L : ℝ, 0 ≤ L ∧
    (∀ h x μ, q.rate h x μ ≤ L * (populationSize x + 1)) ∧
    (∀ h x y μ ν, |q.rate h x μ - q.rate h y ν| ≤
      L * ((∑ i, |(x i : ℝ) - y i|) + totalVariation μ ν))

/-- The positive increments of distance, including shared accepted jumps. -/
def couplingActivity {D : ℕ} (κ : MomentScale) (q : Rates D (MomentLaw κ D))
    (x y : State D) (μ ν : MomentLaw κ D) : ℝ :=
  ∑ h,
    let a := q.rate h x μ
    let b := q.rate h y ν
    let d := adaptedDistance κ x y
    min a b * max (adaptedDistance κ (Jump.advance h x) (Jump.advance h y) - d) 0 +
    max (a - b) 0 * max (adaptedDistance κ (Jump.advance h x) y - d) 0 +
    max (b - a) 0 * max (adaptedDistance κ x (Jump.advance h y) - d) 0

def weightedActivity {D : ℕ} (κ : MomentScale) (q : Rates D (MomentLaw κ D))
    (x : State D) (μ : MomentLaw κ D) : ℝ :=
  ∑ h, q.rate h x μ * adaptedDistance κ (Jump.advance h x) x

/-- Manuscript Assumption 2.2. -/
def MomentCouplingBound {D : ℕ} (κ : MomentScale) (q : Rates D (MomentLaw κ D)) : Prop :=
  ∃ L : ℝ, 0 ≤ L ∧ ∀ x y μ ν,
    couplingActivity κ q x y μ ν ≤ L *
      ((1 + moment μ + moment ν) * adaptedDistance κ x y +
       (1 + momentWeight κ x + momentWeight κ y) * wasserstein μ ν)

/-- Manuscript Assumption 2.3. -/
def MomentActivityBound {D : ℕ} (κ : MomentScale) (q : Rates D (MomentLaw κ D)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x μ,
    weightedActivity κ q x μ ≤ C * (1 + momentWeight κ x) * (1 + moment μ)

/-- Manuscript Assumption 2.5, retaining the supplied drift constant as data
so every quantitative envelope uses that same admissible constant. -/
structure LyapunovControl {D : ℕ} (κ : MomentScale) (q : Rates D (MomentLaw κ D)) where
  function : State D → ℝ
  dominates : ∀ x, 1 + momentWeight κ x ≤ function x
  superlinear : Tendsto (fun x => function x / (1 + momentWeight κ x))
    (Filter.comap populationSize atTop) atTop
  drift : {C : ℝ // 0 ≤ C ∧ ∀ x (μ : MomentLaw κ D),
    Integrable function μ.measure →
    q.generator μ function x ≤ C * (1 + function x + ∫ y, function y ∂μ.measure)}

end CarryingCapacity
