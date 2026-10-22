import CarryingCapacity.Transport
import CarryingCapacity.Models

/-!
# Transport bounds for actual moment-feedback rates

This file connects the scalar model calculations to probability measures and the
infimum-over-couplings transport cost. Mortality may be any nonnegative globally
Lipschitz function on the nonnegative half-line. Values on negative inputs are
irrelevant. Thus the coefficient comparison is derived from moment transport,
not supplied as a surrogate for the desired estimate.

These are dynamic hypothesis checks for the quadratic model in Proposition 7.7.
The stochastic existence and mean-field conclusions are not asserted here.
-/

noncomputable section

namespace CarryingCapacity

/-- Per-capita mortality on nonnegative moments, represented by a real function
whose required properties are restricted to its actual domain of use. -/
structure MomentMortality where
  rate : ℝ → ℝ
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  nonneg : ∀ m, 0 ≤ m → 0 ≤ rate m
  lipschitz : ∀ m n, 0 ≤ m → 0 ≤ n → |rate m - rate n| ≤ constant * |m - n|

namespace MomentMortality

variable (a : MomentMortality)

theorem growth (m : ℝ) (hm : 0 ≤ m) : a.rate m ≤ a.rate 0 + a.constant * m := by
  have h := a.lipschitz m 0 hm (le_refl 0)
  rw [sub_zero, abs_of_nonneg hm] at h
  have hab := le_abs_self (a.rate m - a.rate 0)
  linarith

theorem difference_le_transport {κ : MomentScale} {D : ℕ} (μ ν : MomentLaw κ D) :
    |a.rate (moment μ) - a.rate (moment ν)| ≤ a.constant * wasserstein μ ν := by
  exact (a.lipschitz _ _ (moment_nonneg μ) (moment_nonneg ν)).trans
    (mul_le_mul_of_nonneg_left (moment_difference_le_wasserstein μ ν) a.constant_nonneg)

/-- Affine crowding is a concrete instance, but the following results use all
nonnegative globally Lipschitz mortality functions. -/
def affine (base slope : ℝ) (hbase : 0 ≤ base) (hslope : 0 ≤ slope) : MomentMortality where
  rate := Models.affineMortality base slope
  constant := slope
  constant_nonneg := hslope
  nonneg m hm := Models.affineMortality_nonneg base slope m hbase hslope hm
  lipschitz m n _ _ := le_of_eq (Models.affineMortality_difference base slope m n hslope)

end MomentMortality

/-- In one dimension the general weight is precisely the square of the state. -/
theorem quadratic_one_weight (x : State 1) :
    momentWeight MomentScale.quadratic x = (x 0 : ℝ)^2 := by
  simp [momentWeight, MomentScale.quadratic]

theorem quadratic_one_distance (x y : State 1) :
    adaptedDistance MomentScale.quadratic x y = Models.quadraticDistance (x 0) (y 0) := by
  simp [adaptedDistance, MomentScale.quadratic, Models.quadraticDistance]

/-- This identifies the actual law functional with the scalar second moment. -/
theorem quadratic_one_moment (μ : MomentLaw MomentScale.quadratic 1) :
    moment μ = ∫ x, (x 0 : ℝ)^2 ∂μ.measure := by
  simp only [moment, quadratic_one_weight]

/-- Proposition 7.7's sharper coupling estimate, using genuine measure transport. -/
theorem quadratic_model_coupling (birth : ℝ) (hbirth : 0 ≤ birth) (a : MomentMortality)
    (μ ν : MomentLaw MomentScale.quadratic 1) (x y : ℕ) :
    Models.birthCouplingCost birth x y +
      Models.deathCouplingCost (a.rate (moment μ)) (a.rate (moment ν)) x y ≤
    3 * birth * Models.quadraticDistance x y +
      2 * a.constant * ((x : ℝ)^2 + (y : ℝ)^2) * wasserstein μ ν := by
  exact Models.quadraticCouplingCost_le_transport birth _ _ a.constant (wasserstein μ ν)
    hbirth (a.nonneg _ (moment_nonneg μ)) (a.nonneg _ (moment_nonneg ν))
    (a.difference_le_transport μ ν) x y

/-- The exact weighted shape required by Assumption 2.2 follows with the
explicit constant `3 * birth + 2 * a.constant`. -/
theorem quadratic_model_coupling_standard (birth : ℝ) (hbirth : 0 ≤ birth)
    (a : MomentMortality) (μ ν : MomentLaw MomentScale.quadratic 1) (x y : ℕ) :
    Models.birthCouplingCost birth x y +
      Models.deathCouplingCost (a.rate (moment μ)) (a.rate (moment ν)) x y ≤
    (3 * birth + 2 * a.constant) *
      ((1 + moment μ + moment ν) * Models.quadraticDistance x y +
       (1 + (x : ℝ)^2 + (y : ℝ)^2) * wasserstein μ ν) := by
  exact Models.quadraticCouplingCost_standard birth _ _ a.constant (wasserstein μ ν)
    (moment μ) (moment ν) hbirth (a.nonneg _ (moment_nonneg μ))
    (a.nonneg _ (moment_nonneg ν)) a.constant_nonneg (wasserstein_nonneg μ ν)
    (moment_nonneg μ) (moment_nonneg ν) (a.difference_le_transport μ ν) x y

/-- Assumption 2.3's weighted activity bound for the law-dependent mortality. -/
theorem quadratic_model_activity (birth : ℝ) (hbirth : 0 ≤ birth) (a : MomentMortality)
    (μ : MomentLaw MomentScale.quadratic 1) (n : ℕ) :
    Models.quadraticActivity birth (a.rate (moment μ)) n ≤
      (3 * birth + 2 * a.rate 0 + 2 * a.constant) *
        (1 + (n : ℝ)^2) * (1 + moment μ) := by
  exact Models.quadraticActivity_growth birth _ (a.rate 0) a.constant (moment μ)
    hbirth (a.nonneg _ (moment_nonneg μ)) (a.nonneg 0 (le_refl 0))
    a.constant_nonneg (moment_nonneg μ) (a.growth _ (moment_nonneg μ)) n

/-- The cubic Lyapunov drift bound is uniform in the population law.
Domination and superlinearity are proved in `Models`, with no mortality cutoff. -/
theorem quadratic_model_lyapunov (birth : ℝ) (hbirth : 0 ≤ birth) (a : MomentMortality)
    (μ : MomentLaw MomentScale.quadratic 1) (n : ℕ) :
    Models.generator birth (a.rate (moment μ)) (fun k => 1 + (k : ℝ)^3) n ≤
      7 * birth * (1 + (n : ℝ)^3) := by
  exact Models.cubic_lyapunov_drift birth _ hbirth (a.nonneg _ (moment_nonneg μ)) n

end CarryingCapacity
