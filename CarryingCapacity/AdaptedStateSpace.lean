import CarryingCapacity.EmpiricalMeasure
import CarryingCapacity.TransportMetric

/-!
# The state space with its adapted metric

This type carries the manuscript's metric `ρ_κ`, while retaining exactly the
underlying countable state space and its measurable sets. Its finite powers
carry the maximum of the adapted coordinate distances. The identity between
this space and the original state space is a uniform equivalence, and the
empirical-law map is one-Lipschitz for the finite-power metric.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace CarryingCapacity

/-- The same states as `State D`, equipped with the manuscript's adapted metric. -/
def AdaptedState (_κ : MomentScale) (D : ℕ) := State D

namespace AdaptedState

variable (κ : MomentScale) (D : ℕ)

def toState (x : AdaptedState κ D) : State D := x

def ofState (x : State D) : AdaptedState κ D := x

instance : MetricSpace (AdaptedState κ D) := adaptedMetric κ

instance : MeasurableSpace (AdaptedState κ D) :=
  inferInstanceAs (MeasurableSpace (State D))

instance : Countable (AdaptedState κ D) := inferInstanceAs (Countable (State D))

instance : MeasurableSingletonClass (AdaptedState κ D) :=
  inferInstanceAs (MeasurableSingletonClass (State D))

@[simp] theorem toState_ofState (x : State D) : toState κ D (ofState κ D x) = x := rfl

@[simp] theorem ofState_toState (x : AdaptedState κ D) :
    ofState κ D (toState κ D x) = x := rfl

@[simp] theorem dist_eq (x y : AdaptedState κ D) :
    dist x y = adaptedDistance κ (toState κ D x) (toState κ D y) := rfl

/-- Distinct states are separated by at least one in the adapted metric. -/
theorem one_le_dist {x y : AdaptedState κ D} (hxy : x ≠ y) : 1 ≤ dist x y := by
  have h : ∃ i, toState κ D x i ≠ toState κ D y i := by
    by_contra! h
    exact hxy (funext h)
  obtain ⟨i, hi⟩ := h
  exact (Nat.pairwise_one_le_dist hi).trans
    ((κ.abs_sub_lower_bound _ _).trans (coordinateDistance_le κ _ _ i))

instance : DiscreteUniformity (AdaptedState κ D) := by
  rw [discreteUniformity_iff_eq_bot, Metric.uniformSpace_eq_bot]
  exact ⟨1, zero_lt_one, fun _ _ h => one_le_dist κ D h⟩

/-- Every function on this uniformly discrete state space is uniformly continuous. -/
theorem uniformContinuous_toState : UniformContinuous (toState κ D) :=
  DiscreteUniformity.uniformContinuous _ _

/-- The ordinary finite-power natural-number metric is also uniformly discrete. -/
theorem uniformContinuous_ofState : UniformContinuous (ofState κ D) := by
  have hsep : Pairwise (fun x y : State D => 1 ≤ dist x y) := by
    intro x y hxy
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra! h
      exact hxy (funext h)
    exact (Nat.pairwise_one_le_dist hi).trans (dist_le_pi_dist x y i)
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  refine ⟨1, zero_lt_one, ?_⟩
  intro x y hxy
  have heq : x = y := by
    by_contra h
    exact (not_le_of_gt hxy) (hsep h)
  subst y
  simpa using hε

/-- Identity on states, uniformly continuous in both directions. -/
def uniformEquiv : AdaptedState κ D ≃ᵤ State D where
  toFun := toState κ D
  invFun := ofState κ D
  left_inv := ofState_toState κ D
  right_inv := toState_ofState κ D
  uniformContinuous_toFun := uniformContinuous_toState κ D
  uniformContinuous_invFun := uniformContinuous_ofState κ D

/-- The adapted metric has exactly the original discrete topology. -/
def homeomorph : AdaptedState κ D ≃ₜ State D := (uniformEquiv κ D).toHomeomorph

theorem measurable_toState : Measurable (toState κ D) := measurable_of_countable _

theorem measurable_ofState : Measurable (ofState κ D) := measurable_of_countable _

/-- The measurable structures agree exactly, independently of the metric choice. -/
def measurableEquiv : AdaptedState κ D ≃ᵐ State D where
  toEquiv := (uniformEquiv κ D).toEquiv
  measurable_toFun := measurable_toState κ D
  measurable_invFun := measurable_ofState κ D

/-- Coordinatewise identity on finite configurations; each side uses its finite
product uniformity and hence its maximum coordinate metric. -/
def piUniformEquiv (N : ℕ) : (Fin N → AdaptedState κ D) ≃ᵤ (Fin N → State D) :=
  UniformEquiv.piCongrRight (fun _ => uniformEquiv κ D)

@[simp] theorem piUniformEquiv_apply (N : ℕ) (z : Fin N → AdaptedState κ D)
    (i : Fin N) : piUniformEquiv κ D N z i = toState κ D (z i) := rfl

def piHomeomorph (N : ℕ) : (Fin N → AdaptedState κ D) ≃ₜ (Fin N → State D) :=
  (piUniformEquiv κ D N).toHomeomorph

def piMeasurableEquiv (N : ℕ) : (Fin N → AdaptedState κ D) ≃ᵐ (Fin N → State D) :=
  MeasurableEquiv.piCongrRight (fun _ => measurableEquiv κ D)

/-- The finite-power metric is precisely the maximum of its adapted coordinate
distances, also covering the empty power. -/
theorem pi_dist_le_iff {N : ℕ} (z w : Fin N → AdaptedState κ D) {r : ℝ}
    (hr : 0 ≤ r) :
    dist z w ≤ r ↔ ∀ i, adaptedDistance κ (toState κ D (z i)) (toState κ D (w i)) ≤ r :=
  dist_pi_le_iff hr

/-- The actual empirical probability law of an adapted configuration. -/
def empiricalLaw {N : ℕ} (hN : 0 < N) (z : Fin N → AdaptedState κ D) : MomentLaw κ D :=
  CarryingCapacity.empiricalLaw κ hN (fun i => toState κ D (z i))

/-- Pairing identical particle labels makes empirical transport one-Lipschitz
for the maximum adapted state distance. -/
theorem lipschitzWith_empiricalLaw {N : ℕ} (hN : 0 < N) :
    LipschitzWith 1 (empiricalLaw κ D hN) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [NNReal.coe_one, one_mul, momentLaw_dist]
  refine (wasserstein_empiricalLaw_le κ hN _ _).trans ?_
  have hsum : (∑ i, adaptedDistance κ (toState κ D (z i)) (toState κ D (w i))) ≤
      (N : ℝ) * dist z w := by
    calc
      _ ≤ ∑ _ : Fin N, dist z w := Finset.sum_le_sum fun i _ => dist_le_pi_dist z w i
      _ = (N : ℝ) * dist z w := by simp
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  calc
    _ ≤ (N : ℝ)⁻¹ * ((N : ℝ) * dist z w) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ = dist z w := by rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem uniformContinuous_empiricalLaw {N : ℕ} (hN : 0 < N) :
    UniformContinuous (empiricalLaw κ D hN) :=
  (lipschitzWith_empiricalLaw κ D hN).uniformContinuous

theorem continuous_empiricalLaw {N : ℕ} (hN : 0 < N) :
    Continuous (empiricalLaw κ D hN) :=
  (uniformContinuous_empiricalLaw κ D hN).continuous

end AdaptedState
end CarryingCapacity
