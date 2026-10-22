import CarryingCapacity.ConfigurationLocalization
import CarryingCapacity.CouplingExpectation
import CarryingCapacity.SynchronousPositiveIncrement

/-!
# Averaged population coupling and the localized split estimate

The actual coordinate costs of a shared-noise configuration pair recover the
single-particle coupling activity exactly. Averaging the manuscript's split
bound averages the random state weights before they multiply the common law
error. The resulting localization constant is independent of particle number.
These are deterministic ingredients of Proposition 5.3, not an assumed
stochastic comparison or convergence theorem.
-/

noncomputable section
open MeasureTheory
open scoped Classical BigOperators

namespace CarryingCapacity.PopulationCouplingAlgebra
open ConfigurationLocalization SynchronousPositiveIncrement DeterministicEnvironmentRates

variable {N D : ℕ} (κ : MomentScale) (q : Rates D (MomentLaw κ D))

/-- The cost of one labelled coordinate of a configuration pair. -/
def coordinateCost (i : Fin N) (z w : Configuration N D) : ℝ :=
  adaptedDistance κ (z i) (w i)

/-- The actual average of the paired particle distances. -/
def meanDistance (z w : Configuration N D) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, adaptedDistance κ (z i) (w i)

/-- The actual average of the single-particle positive coupling activities. -/
def meanActivity (z w : Configuration N D) (μ ν : MomentLaw κ D) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, couplingActivity κ q (z i) (w i) μ ν

theorem meanDistance_nonnegative (z w : Configuration N D) :
    0 ≤ meanDistance κ z w :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))
    (Finset.sum_nonneg (fun i _ => adaptedDistance_nonneg κ (z i) (w i)))

/-- The mean paired distance is controlled by the two genuine empirical moments. -/
theorem meanDistance_le_moments (hN : 0 < N) (z w : Configuration N D) :
    meanDistance κ z w ≤ moment (empiricalLaw κ hN z) + moment (empiricalLaw κ hN w) := by
  simp only [moment_empiricalLaw, FiniteGenerator.empiricalMean, meanDistance, ← mul_add,
    ← Finset.sum_add_distrib]
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i _ => adaptedDistance_le_weights (z i) (w i)))
    (inv_nonneg.mpr (Nat.cast_nonneg N))

theorem meanActivity_nonnegative (z w : Configuration N D) (μ ν : MomentLaw κ D) :
    0 ≤ meanActivity κ q z w μ ν :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))
    (Finset.sum_nonneg (fun i _ => CouplingExpectation.activity_nonnegative κ q (z i) (w i) μ ν))

/-- Proposals of other labels contribute zero to a coordinate cost; its own
labels give precisely the three-region single-particle activity. -/
theorem sum_coordinate_heightActivity (i : Fin N) (z w : Configuration N D)
    (μ ν : MomentLaw κ D) :
    (∑ j : Label N D, heightActivity (coordinateCost κ i) jump j
      (q.rate j.2 (z j.1) μ) (q.rate j.2 (w j.1) ν) z w) =
      couplingActivity κ q (z i) (w i) μ ν := by
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp only [heightActivity, coordinateCost, jump, couplingActivity,
      Function.update_self]
  · intro k _ hki
    apply Finset.sum_eq_zero
    intro h _
    simp [heightActivity, coordinateCost, jump, Function.update_of_ne (Ne.symm hki)]
  · simp

/-- Averaged configuration activity is exactly the averaged scalar activity. -/
theorem mean_coordinate_heightActivity (z w : Configuration N D)
    (μ ν : MomentLaw κ D) :
    (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Label N D,
      heightActivity (coordinateCost κ i) jump j
        (q.rate j.2 (z j.1) μ) (q.rate j.2 (w j.1) ν) z w =
      meanActivity κ q z w μ ν := by
  simp only [sum_coordinate_heightActivity, meanActivity]

/-- The empirical pairing and transport triangle split the error into paired
particle distance and the independent array's empirical error. -/
theorem empirical_error_decomposition (hN : 0 < N) (z w : Configuration N D)
    (ν : MomentLaw κ D) :
    wasserstein (empiricalLaw κ hN z) ν ≤
      meanDistance κ z w + wasserstein (empiricalLaw κ hN w) ν :=
  (wasserstein_triangle _ _ _).trans
    (add_le_add_right (wasserstein_empiricalLaw_le κ hN z w) _)

/-- The genuine empirical moment is bounded by the empirical Lyapunov value. -/
theorem moment_empirical_le_lyapunov (control : LyapunovControl κ q)
    (hN : 0 < N) (z : Configuration N D) :
    moment (empiricalLaw κ hN z) ≤ lyapunov control z := by
  rw [moment_empiricalLaw]
  apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => ?_))
    (inv_nonneg.mpr (Nat.cast_nonneg N))
  exact (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)).trans (control.dominates (z i))

/-- The joint Lyapunov localization controls the two empirical moments. -/
theorem moment_pair_le_of_lyapunov (control : LyapunovControl κ q)
    (hN : 0 < N) (z w : Configuration N D) (R : ℝ)
    (hR : lyapunov control z + lyapunov control w ≤ R) :
    moment (empiricalLaw κ hN z) + moment (empiricalLaw κ hN w) ≤ R :=
  (add_le_add (moment_empirical_le_lyapunov κ q control hN z)
    (moment_empirical_le_lyapunov κ q control hN w)).trans hR

variable (hCoupling : MomentCouplingBound κ q)

/-- Exact averaging preserves the split assumption and averages state weights
before multiplying the common law error. -/
theorem meanActivity_le_split (hN : 0 < N) (z w : Configuration N D)
    (μ ν : MomentLaw κ D) :
    meanActivity κ q z w μ ν ≤ couplingConstant κ q hCoupling *
      ((1 + moment μ + moment ν) * meanDistance κ z w +
        (1 + moment (empiricalLaw κ hN z) + moment (empiricalLaw κ hN w)) *
          wasserstein μ ν) := by
  let a := fun i : Fin N => (z i, w i)
  let P := empiricalMeasure a
  letI : IsProbabilityMeasure P := empiricalMeasure_probability hN a
  have h := CouplingExpectation.integral_activity_le κ q hCoupling P
    Prod.fst Prod.snd measurable_fst measurable_snd
    (integrable_empiricalMeasure hN a (fun p => momentWeight κ p.1))
    (integrable_empiricalMeasure hN a (fun p => momentWeight κ p.2)) μ ν
  simpa only [P, a, integral_empiricalMeasure, moment_empiricalLaw,
    FiniteGenerator.empiricalMean, meanDistance, meanActivity] using h

/-- Before the joint moment exit, the exact split coefficient has no N factor. -/
theorem meanActivity_le_localized_split (hN : 0 < N) (z w : Configuration N D)
    (ν : MomentLaw κ D) (R K d : ℝ)
    (hR : moment (empiricalLaw κ hN z) + moment (empiricalLaw κ hN w) ≤ R)
    (hK : moment ν ≤ K) (hd : meanDistance κ z w ≤ d) :
    meanActivity κ q z w (empiricalLaw κ hN z) ν ≤
      couplingConstant κ q hCoupling * (1 + R + K) * d +
        couplingConstant κ q hCoupling * (1 + R) *
          wasserstein (empiricalLaw κ hN z) ν := by
  have hz := moment_nonneg (empiricalLaw κ hN z)
  have hw := moment_nonneg (empiricalLaw κ hN w)
  have hv := moment_nonneg ν
  have hL := couplingConstant_nonnegative κ q hCoupling
  have ha : 0 ≤ 1 + R + K := by linarith
  have h₁ : (1 + moment (empiricalLaw κ hN z) + moment ν) * meanDistance κ z w ≤
      (1 + R + K) * d :=
    (mul_le_mul_of_nonneg_right (by linarith) (meanDistance_nonnegative κ z w)).trans
      (mul_le_mul_of_nonneg_left hd ha)
  have h₂ := mul_le_mul_of_nonneg_right
    (show 1 + moment (empiricalLaw κ hN z) + moment (empiricalLaw κ hN w) ≤ 1 + R by linarith)
    (wasserstein_nonneg (empiricalLaw κ hN z) ν)
  apply (meanActivity_le_split κ q hCoupling hN z w (empiricalLaw κ hN z) ν).trans
  calc
    _ ≤ couplingConstant κ q hCoupling *
        ((1 + R + K) * d + (1 + R) * wasserstein (empiricalLaw κ hN z) ν) :=
      mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hL
    _ = _ := by ring

/-- The coefficient needed by the localized population Gronwall estimate. -/
def localizedConstant (R K : ℝ) : ℝ := couplingConstant κ q hCoupling * (2 + 2 * R + K)

theorem localizedConstant_nonnegative (R K : ℝ) (hR : 0 ≤ R) (hK : 0 ≤ K) :
    0 ≤ localizedConstant κ q hCoupling R K :=
  mul_nonneg (couplingConstant_nonnegative κ q hCoupling) (by linarith)

/-- Closing the empirical triangle gives the precise deterministic bound used
under the stopped expectation in Proposition 5.3. -/
theorem meanActivity_le_localized (hN : 0 < N) (z w : Configuration N D)
    (ν : MomentLaw κ D) (R K d : ℝ)
    (hR : moment (empiricalLaw κ hN z) + moment (empiricalLaw κ hN w) ≤ R)
    (hK : moment ν ≤ K) (hd : meanDistance κ z w ≤ d) :
    meanActivity κ q z w (empiricalLaw κ hN z) ν ≤
      localizedConstant κ q hCoupling R K *
        (d + wasserstein (empiricalLaw κ hN w) ν) := by
  have hz := moment_nonneg (empiricalLaw κ hN z)
  have hw := moment_nonneg (empiricalLaw κ hN w)
  have hv := moment_nonneg ν
  have hL := couplingConstant_nonnegative κ q hCoupling
  have hR0 : 0 ≤ R := by linarith
  have hK0 : 0 ≤ K := hv.trans hK
  have he := (empirical_error_decomposition κ hN z w ν).trans (add_le_add_right hd _)
  have hcoef : 0 ≤ couplingConstant κ q hCoupling * (1 + R) :=
    mul_nonneg hL (by linarith)
  have hErr := wasserstein_nonneg (empiricalLaw κ hN w) ν
  apply (meanActivity_le_localized_split κ q hCoupling hN z w ν R K d hR hK hd).trans
  calc
    _ ≤ couplingConstant κ q hCoupling * (1 + R + K) * d +
        couplingConstant κ q hCoupling * (1 + R) *
          (d + wasserstein (empiricalLaw κ hN w) ν) :=
      add_le_add_left (mul_le_mul_of_nonneg_left he hcoef) _
    _ ≤ localizedConstant κ q hCoupling R K *
        (d + wasserstein (empiricalLaw κ hN w) ν) := by
      have hp : 0 ≤ couplingConstant κ q hCoupling * (1 + R + K) *
          wasserstein (empiricalLaw κ hN w) ν :=
        mul_nonneg (mul_nonneg hL (by linarith)) hErr
      unfold localizedConstant
      nlinarith

end CarryingCapacity.PopulationCouplingAlgebra
