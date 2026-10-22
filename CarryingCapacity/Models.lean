import Mathlib

/-!
# Scalar birth-death calculations

This file proves the boundary-aware generator and weighted-activity calculations
used in the scalar special case of DeWitt--Evans--Hiesmayr--Hummel (2024),
Section 4, and in Kenny Xie's manuscript, Section 7. The argument is algebraic:
`death` denotes the current nonnegative per-capita mortality coefficient,
which may subsequently be evaluated at a first or second population moment.

The results below do not assert existence of a stochastic process, justify an
exchange of expectation and generator, or prove a mean-field limit.
-/

namespace CarryingCapacity.Models

/-- Generator of a scalar lineage with rates `birth * n` and `death * n`.
Natural subtraction implements the boundary, and the death rate vanishes at zero. -/
def generator (birth death : ℝ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  birth * n * (f (n + 1) - f n) + death * n * (f (n - 1) - f n)

@[simp] theorem generator_zero (birth death : ℝ) (f : ℕ → ℝ) :
    generator birth death f 0 = 0 := by
  simp [generator]

@[simp] theorem generator_const (birth death c : ℝ) (n : ℕ) :
    generator birth death (fun _ => c) n = 0 := by
  simp [generator]

theorem generator_add (birth death : ℝ) (f g : ℕ → ℝ) (n : ℕ) :
    generator birth death (fun k => f k + g k) n =
      generator birth death f n + generator birth death g n := by
  unfold generator
  ring

/-- The first-moment drift, before taking any expectations. -/
theorem generator_first_moment (birth death : ℝ) (n : ℕ) :
    generator birth death (fun k => (k : ℝ)) n = (birth - death) * n := by
  cases n with
  | zero => simp
  | succ n => simp [generator, Nat.cast_add, Nat.cast_one]; ring

/-- The exact second-moment drift in the quadratic-feedback example. -/
theorem generator_second_moment (birth death : ℝ) (n : ℕ) :
    generator birth death (fun k => (k : ℝ) ^ 2) n =
      2 * (birth - death) * (n : ℝ) ^ 2 + (birth + death) * n := by
  cases n with
  | zero => simp
  | succ n => simp [generator, Nat.cast_add, Nat.cast_one]; ring

/-- A cubic drift identity; this supplies a Lyapunov function strictly stronger
than the second moment without claiming the whole real-exponent family. -/
theorem generator_third_moment (birth death : ℝ) (n : ℕ) :
    generator birth death (fun k => (k : ℝ) ^ 3) n =
      3 * (birth - death) * (n : ℝ) ^ 3 +
      3 * (birth + death) * (n : ℝ) ^ 2 + (birth - death) * n := by
  cases n with
  | zero => simp
  | succ n => simp [generator, Nat.cast_add, Nat.cast_one]; ring

/-- The adapted distance for the quadratic choice of growth scale. -/
def quadraticDistance (x y : ℕ) : ℝ := |(x : ℝ)^2 - (y : ℝ)^2|

/-- Metric-weighted activity uses the absolute size of each jump, not its signed drift. -/
def quadraticActivity (birth death : ℝ) (n : ℕ) : ℝ :=
  birth * n * quadraticDistance (n + 1) n +
  death * n * quadraticDistance (n - 1) n

theorem quadraticDistance_birth (n : ℕ) :
    quadraticDistance (n + 1) n = 2 * (n : ℝ) + 1 := by
  unfold quadraticDistance
  rw [abs_of_nonneg]
  · push_cast
    ring
  · push_cast
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]

theorem quadraticDistance_death_succ (n : ℕ) :
    quadraticDistance ((n + 1) - 1) (n + 1) = 2 * ((n : ℝ) + 1) - 1 := by
  simp only [Nat.add_sub_cancel, quadraticDistance, Nat.cast_add, Nat.cast_one]
  rw [abs_of_nonpos]
  · ring
  · nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]

/-- The zero state is included: the apparent `2*n-1` factor is multiplied by zero. -/
theorem quadraticActivity_eq (birth death : ℝ) (n : ℕ) :
    quadraticActivity birth death n =
      birth * n * (2 * (n : ℝ) + 1) + death * n * (2 * (n : ℝ) - 1) := by
  cases n with
  | zero => simp [quadraticActivity]
  | succ n =>
    simp only [quadraticActivity, Nat.succ_eq_add_one, quadraticDistance_birth,
      quadraticDistance_death_succ, Nat.cast_add, Nat.cast_one]

/-- The positive common-birth increment can be nonzero, unlike the linear metric. -/
theorem quadratic_common_birth_example :
    quadraticDistance 3 2 - quadraticDistance 2 1 = 2 := by
  norm_num [quadraticDistance]

/-- Ordered birth contribution to the positive-increment coupling calculation.
The first term is shared births; the second term is unmatched births of the
larger lineage. This definition records that exact ordered-case expression. -/
def orderedBirthContribution (birth : ℝ) (x y : ℕ) : ℝ :=
  2 * birth * y * ((x : ℝ) - y) +
    birth * ((x : ℝ) - y) * (2 * (x : ℝ) + 1)

theorem orderedBirthContribution_eq (birth : ℝ) (x y : ℕ) :
    orderedBirthContribution birth x y =
      birth * (2 * ((x : ℝ)^2 - (y : ℝ)^2) + ((x : ℝ) - y)) := by
  unfold orderedBirthContribution
  ring


/-- Integer states, rather than arbitrary positive reals, give this comparison. -/
theorem natCast_le_square (n : ℕ) : (n : ℝ) ≤ (n : ℝ)^2 := by
  cases n with
  | zero => norm_num
  | succ n =>
    simp only [Nat.cast_succ]
    nlinarith [sq_nonneg (n : ℝ), (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]

theorem natCast_square_le_cube (n : ℕ) : (n : ℝ)^2 ≤ (n : ℝ)^3 := by
  have h := mul_le_mul_of_nonneg_left (natCast_le_square n) ((Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)))
  nlinarith

/-- A valid quadratic Lyapunov estimate for linear moment control.
Deaths only improve this upper bound, irrespective of the size of `death`. -/
theorem quadratic_lyapunov_drift (birth death : ℝ)
    (hb : 0 ≤ birth) (hd : 0 ≤ death) (n : ℕ) :
    generator birth death (fun k => 1 + (k : ℝ)^2) n ≤
      3 * birth * (1 + (n : ℝ)^2) := by
  rw [generator_add, generator_const, zero_add, generator_second_moment]
  have hn := natCast_le_square n
  have hdeath : 0 ≤ death * (2 * (n : ℝ)^2 - n) :=
    mul_nonneg hd (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))])
  have hbirth := mul_le_mul_of_nonneg_left hn hb
  nlinarith

/-- A cubic Lyapunov drift estimate usable with second-moment feedback. -/
theorem cubic_lyapunov_drift (birth death : ℝ)
    (hb : 0 ≤ birth) (hd : 0 ≤ death) (n : ℕ) :
    generator birth death (fun k => 1 + (k : ℝ)^3) n ≤
      7 * birth * (1 + (n : ℝ)^3) := by
  rw [generator_add, generator_const, zero_add, generator_third_moment]
  have hn := natCast_le_square n
  have hs := natCast_square_le_cube n
  have hdeath : 0 ≤ death * (3 * (n : ℝ)^3 - 3 * (n : ℝ)^2 + n) :=
    mul_nonneg hd (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))])
  have hbirth1 := mul_le_mul_of_nonneg_left hn hb
  have hbirth2 := mul_le_mul_of_nonneg_left hs hb
  nlinarith

theorem cubic_lyapunov_dominates (n : ℕ) :
    1 + (n : ℝ)^2 ≤ 1 + (n : ℝ)^3 := by
  linarith [natCast_square_le_cube n]

/-- An explicit lower bound on the Lyapunov-to-moment ratio. -/
theorem cubic_lyapunov_ratio_lower (n : ℕ) :
    (n : ℝ) / 2 ≤ (1 + (n : ℝ)^3) / (1 + (n : ℝ)^2) := by
  have hden : 0 < 1 + (n : ℝ)^2 := by positivity
  apply (le_div_iff₀ hden).2
  nlinarith [natCast_le_square n, natCast_square_le_cube n]

/-- Quadratic activity has the required product growth if mortality is bounded
by an affine function of the current population moment. -/
theorem quadraticActivity_growth (birth death base lip moment : ℝ)
    (hb : 0 ≤ birth) (hd : 0 ≤ death) (hbase : 0 ≤ base)
    (hlip : 0 ≤ lip) (hm : 0 ≤ moment) (hdeath : death ≤ base + lip * moment)
    (n : ℕ) :
    quadraticActivity birth death n ≤
      (3 * birth + 2 * base + 2 * lip) * (1 + (n : ℝ)^2) * (1 + moment) := by
  rw [quadraticActivity_eq]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn2 := natCast_le_square n
  have hbirth : birth * n * (2 * (n : ℝ) + 1) ≤ 3 * birth * (n : ℝ)^2 := by
    have h := mul_le_mul_of_nonneg_left hn2 hb
    nlinarith
  have hdeath1 : death * n * (2 * (n : ℝ) - 1) ≤ 2 * death * (n : ℝ)^2 := by
    have h := mul_nonneg hd hn
    nlinarith
  have hdeath2 : 2 * death * (n : ℝ)^2 ≤
      2 * (base + lip * moment) * (n : ℝ)^2 := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdeath (by norm_num))
      (sq_nonneg _)
  have hcoeff : 3 * birth + 2 * (base + lip * moment) ≤
      (3 * birth + 2 * base + 2 * lip) * (1 + moment) := by
    have hbm := mul_nonneg hb hm
    have hbasem := mul_nonneg hbase hm
    nlinarith
  have hcoeff0 : 0 ≤ 3 * birth + 2 * base + 2 * lip := by positivity
  have hmono := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (n : ℝ))
  have hrest : 0 ≤ (3 * birth + 2 * base + 2 * lip) * (1 + moment) := by positivity
  nlinarith

/-- The ordered birth contribution is bounded by three times the adapted distance.
This includes the common-jump term; dropping it would be incorrect. -/
theorem orderedBirthContribution_le (birth : ℝ) (hb : 0 ≤ birth)
    (x y : ℕ) (hxy : y ≤ x) :
    orderedBirthContribution birth x y ≤ 3 * birth * quadraticDistance x y := by
  rw [orderedBirthContribution_eq]
  have hxyR : (y : ℝ) ≤ x := by exact_mod_cast hxy
  have hx : 0 ≤ (x : ℝ) := Nat.cast_nonneg x
  have hy : 0 ≤ (y : ℝ) := Nat.cast_nonneg y
  have hs : 0 ≤ (x : ℝ)^2 - (y : ℝ)^2 := by nlinarith
  have hdiff : (x : ℝ) - y ≤ (x : ℝ)^2 - (y : ℝ)^2 := by
    obtain h | h := eq_or_lt_of_le hxy
    · subst x
      simp
    · have h1 : (y : ℝ) + 1 ≤ x := by exact_mod_cast h
      have hprod := mul_nonneg (sub_nonneg.mpr hxyR) (show 0 ≤ (x : ℝ) + y - 1 by linarith)
      nlinarith
  have hmul := mul_le_mul_of_nonneg_left hdiff hb
  unfold quadraticDistance
  rw [abs_of_nonneg hs]
  nlinarith


/-- Full positive-increment coupling cost for one jump direction.
The three terms are common jumps, first-only jumps, and second-only jumps. -/
def positiveCouplingCost (next : ℕ → ℕ) (a b : ℝ) (x y : ℕ) : ℝ :=
  min a b * max (quadraticDistance (next x) (next y) - quadraticDistance x y) 0 +
  max (a - b) 0 * max (quadraticDistance (next x) y - quadraticDistance x y) 0 +
  max (b - a) 0 * max (quadraticDistance x (next y) - quadraticDistance x y) 0

def birthCouplingCost (birth : ℝ) (x y : ℕ) : ℝ :=
  positiveCouplingCost (fun n => n + 1) (birth * x) (birth * y) x y

def deathCouplingCost (death₁ death₂ : ℝ) (x y : ℕ) : ℝ :=
  positiveCouplingCost (fun n => n - 1) (death₁ * x) (death₂ * y) x y

theorem quadraticDistance_symm (x y : ℕ) :
    quadraticDistance x y = quadraticDistance y x := by
  exact abs_sub_comm _ _

theorem quadraticDistance_of_le {x y : ℕ} (h : y ≤ x) :
    quadraticDistance x y = (x : ℝ)^2 - (y : ℝ)^2 := by
  have hR : (y : ℝ) ≤ x := by exact_mod_cast h
  apply abs_of_nonneg
  nlinarith [(Nat.cast_nonneg x : (0 : ℝ) ≤ (x : ℝ)), (Nat.cast_nonneg y : (0 : ℝ) ≤ (y : ℝ))]

theorem positiveCouplingCost_symm (next : ℕ → ℕ) (a b : ℝ) (x y : ℕ) :
    positiveCouplingCost next a b x y = positiveCouplingCost next b a y x := by
  unfold positiveCouplingCost
  rw [quadraticDistance_symm (next x) (next y),
    quadraticDistance_symm (next x) y, quadraticDistance_symm x (next y),
    quadraticDistance_symm x y, min_comm a b]
  ring

theorem birthCouplingCost_symm (birth : ℝ) (x y : ℕ) :
    birthCouplingCost birth x y = birthCouplingCost birth y x := by
  exact positiveCouplingCost_symm _ _ _ _ _

theorem deathCouplingCost_symm (a b : ℝ) (x y : ℕ) :
    deathCouplingCost a b x y = deathCouplingCost b a y x := by
  exact positiveCouplingCost_symm _ _ _ _ _

theorem quadratic_common_birth_increment {x y : ℕ} (hxy : y ≤ x) :
    quadraticDistance (x + 1) (y + 1) - quadraticDistance x y =
      2 * ((x : ℝ) - y) := by
  rw [quadraticDistance_of_le (Nat.add_le_add_right hxy 1), quadraticDistance_of_le hxy]
  push_cast
  ring

theorem quadratic_larger_birth_increment {x y : ℕ} (hxy : y ≤ x) :
    quadraticDistance (x + 1) y - quadraticDistance x y = 2 * (x : ℝ) + 1 := by
  rw [quadraticDistance_of_le (by omega : y ≤ x + 1), quadraticDistance_of_le hxy]
  push_cast
  ring

/-- The ordered algebra above is the actual three-term Poisson coupling cost. -/
theorem birthCouplingCost_eq_ordered (birth : ℝ) (hb : 0 ≤ birth)
    (x y : ℕ) (hxy : y ≤ x) :
    birthCouplingCost birth x y = orderedBirthContribution birth x y := by
  have hxyR : (y : ℝ) ≤ x := by exact_mod_cast hxy
  have hr : birth * (y : ℝ) ≤ birth * x := mul_le_mul_of_nonneg_left hxyR hb
  unfold birthCouplingCost positiveCouplingCost
  rw [min_eq_right hr, max_eq_left (sub_nonneg.mpr hr),
    max_eq_right (sub_nonpos.mpr hr), zero_mul, add_zero,
    quadratic_common_birth_increment hxy, quadratic_larger_birth_increment hxy,
    max_eq_left (by linarith : 0 ≤ 2 * ((x : ℝ) - y)),
    max_eq_left (by positivity : 0 ≤ 2 * (x : ℝ) + 1)]
  unfold orderedBirthContribution
  ring

/-- Full birth-direction bound in Proposition 7.7, including common births. -/
theorem birthCouplingCost_le (birth : ℝ) (hb : 0 ≤ birth) (x y : ℕ) :
    birthCouplingCost birth x y ≤ 3 * birth * quadraticDistance x y := by
  rcases le_total y x with h | h
  · rw [birthCouplingCost_eq_ordered birth hb x y h]
    exact orderedBirthContribution_le birth hb x y h
  · rw [birthCouplingCost_symm, quadraticDistance_symm]
    rw [birthCouplingCost_eq_ordered birth hb y x h]
    exact orderedBirthContribution_le birth hb y x h


private theorem quadratic_common_death_nonincrease_ordered {x y : ℕ} (hxy : y ≤ x) :
    quadraticDistance (x - 1) (y - 1) ≤ quadraticDistance x y := by
  cases x with
  | zero =>
    have hy : y = 0 := by omega
    subst y
    simp [quadraticDistance]
  | succ x =>
    cases y with
    | zero =>
      norm_num only [Nat.succ_sub_one, Nat.zero_sub, quadraticDistance, Nat.cast_zero,
        zero_pow, sub_zero, Nat.cast_succ]
      rw [abs_of_nonneg (sq_nonneg (x : ℝ)), abs_of_nonneg (sq_nonneg ((x : ℝ) + 1))]
      nlinarith [(Nat.cast_nonneg x : (0 : ℝ) ≤ (x : ℝ))]
    | succ y =>
      have h : y ≤ x := by omega
      rw [quadraticDistance_of_le (Nat.sub_le_sub_right hxy 1), quadraticDistance_of_le hxy]
      simp only [Nat.succ_sub_one, Nat.cast_succ]
      have hR : (y : ℝ) ≤ x := by exact_mod_cast h
      nlinarith

theorem quadratic_common_death_nonincrease (x y : ℕ) :
    quadraticDistance (x - 1) (y - 1) ≤ quadraticDistance x y := by
  rcases le_total y x with h | h
  · exact quadratic_common_death_nonincrease_ordered h
  · rw [quadraticDistance_symm (x - 1) (y - 1), quadraticDistance_symm x y]
    exact quadratic_common_death_nonincrease_ordered h

theorem quadratic_larger_death_nonincrease {x y : ℕ} (hxy : y < x) :
    quadraticDistance (x - 1) y ≤ quadraticDistance x y := by
  cases x with
  | zero => omega
  | succ x =>
    have h : y ≤ x := by omega
    rw [quadraticDistance_of_le (by omega : y ≤ Nat.succ x - 1),
      quadraticDistance_of_le (Nat.le_of_lt hxy)]
    simp only [Nat.succ_sub_one, Nat.cast_succ]
    nlinarith [(Nat.cast_nonneg x : (0 : ℝ) ≤ (x : ℝ))]

theorem quadratic_smaller_death_increment {x y : ℕ} (hxy : y < x) (hy : 0 < y) :
    quadraticDistance x (y - 1) - quadraticDistance x y = 2 * (y : ℝ) - 1 := by
  cases y with
  | zero => omega
  | succ y =>
    rw [quadraticDistance_of_le (by omega : Nat.succ y - 1 ≤ x),
      quadraticDistance_of_le (Nat.le_of_lt hxy)]
    simp only [Nat.succ_sub_one, Nat.cast_succ]
    ring

private theorem deathCouplingCost_ordered_formula (a b : ℝ) (x y : ℕ)
    (hxy : y < x) (hy : 0 < y) :
    deathCouplingCost a b x y = max (b * y - a * x) 0 * (2 * (y : ℝ) - 1) := by
  unfold deathCouplingCost positiveCouplingCost
  rw [max_eq_right (sub_nonpos.mpr (quadratic_common_death_nonincrease x y)),
    max_eq_right (sub_nonpos.mpr (quadratic_larger_death_nonincrease hxy)),
    mul_zero, mul_zero, zero_add, zero_add, quadratic_smaller_death_increment hxy hy]
  have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hy
  rw [max_eq_left (by linarith : 0 ≤ 2 * (y : ℝ) - 1)]

private theorem deathCouplingCost_zero_right (a b : ℝ) (x : ℕ) :
    deathCouplingCost a b x 0 = 0 := by
  cases x with
  | zero => simp [deathCouplingCost, positiveCouplingCost, quadraticDistance]
  | succ x =>
    unfold deathCouplingCost positiveCouplingCost
    rw [max_eq_right (sub_nonpos.mpr (quadratic_common_death_nonincrease _ _))]
    simp

/-- A smaller lineage's excess mortality is controlled by the difference of
per-capita coefficients. The sign of this difference need not be prescribed. -/
theorem smaller_death_excess_le (a b : ℝ) (ha : 0 ≤ a) (x y : ℕ) (hxy : y ≤ x) :
    max (b * y - a * x) 0 ≤ (y : ℝ) * |b - a| := by
  have hxyR : (y : ℝ) ≤ x := by exact_mod_cast hxy
  have hy : 0 ≤ (y : ℝ) := Nat.cast_nonneg y
  have hmul := mul_le_mul_of_nonneg_left hxyR ha
  have hab := le_abs_self (b - a)
  have hmul2 := mul_le_mul_of_nonneg_left hab hy
  apply max_le
  · nlinarith
  · exact mul_nonneg hy (abs_nonneg _)

private theorem deathCouplingCost_strict_le (a b : ℝ) (ha : 0 ≤ a)
    (x y : ℕ) (hxy : y < x) :
    deathCouplingCost a b x y ≤ 2 * (y : ℝ)^2 * |a - b| := by
  by_cases hy : y = 0
  · subst y
    rw [deathCouplingCost_zero_right]
    simp
  · have hypos : 0 < y := Nat.pos_of_ne_zero hy
    rw [deathCouplingCost_ordered_formula a b x y hxy hypos]
    have hyR : (1 : ℝ) ≤ y := by exact_mod_cast hypos
    have hm := mul_le_mul_of_nonneg_right
      (smaller_death_excess_le a b ha x y (Nat.le_of_lt hxy))
      (show 0 ≤ 2 * (y : ℝ) - 1 by linarith)
    have hrem : 0 ≤ (y : ℝ) * |b - a| := mul_nonneg (Nat.cast_nonneg y) (abs_nonneg _)
    rw [abs_sub_comm a b]
    nlinarith


private theorem positive_excess_sum (a b : ℝ) :
    max (a - b) 0 + max (b - a) 0 = |a - b| := by
  rcases le_total a b with h | h
  · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h),
      abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h),
      abs_of_nonneg (sub_nonneg.mpr h)]
    ring

private theorem deathCouplingCost_equal_le (a b : ℝ) (x : ℕ) :
    deathCouplingCost a b x x ≤ 2 * (x : ℝ)^2 * |a - b| := by
  cases x with
  | zero => simp [deathCouplingCost, positiveCouplingCost, quadraticDistance]
  | succ n =>
    have hx : 0 ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hstep : 0 ≤ 2 * ((n + 1 : ℕ) : ℝ) - 1 := by
      push_cast
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    have hdist : quadraticDistance ((n + 1) - 1) (n + 1) =
        2 * ((n + 1 : ℕ) : ℝ) - 1 := by
      simpa using quadraticDistance_death_succ n
    have heq : deathCouplingCost a b (n + 1) (n + 1) =
        (max (a * (n + 1 : ℕ) - b * (n + 1 : ℕ)) 0 +
         max (b * (n + 1 : ℕ) - a * (n + 1 : ℕ)) 0) *
         (2 * ((n + 1 : ℕ) : ℝ) - 1) := by
      unfold deathCouplingCost positiveCouplingCost
      rw [quadraticDistance_symm (n + 1) ((n + 1) - 1), hdist]
      simp only [quadraticDistance, sub_self, abs_zero, sub_zero, max_self,
        mul_zero, zero_add]
      rw [max_eq_left hstep]
      ring
    change deathCouplingCost a b (n + 1) (n + 1) ≤ _
    rw [heq, positive_excess_sum, ← sub_mul, abs_mul, abs_of_nonneg hx]
    have hrem := mul_nonneg hx (abs_nonneg (a - b))
    nlinarith

/-- Full death-direction estimate in Proposition 7.7. Mortality shared by both
chains cannot increase the quadratic distance; only the coefficient mismatch
survives in this bound. -/
theorem deathCouplingCost_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (x y : ℕ) :
    deathCouplingCost a b x y ≤ 2 * ((x : ℝ)^2 + (y : ℝ)^2) * |a - b| := by
  rcases lt_trichotomy y x with h | h | h
  · have hbound := deathCouplingCost_strict_le a b ha x y h
    have hrest := mul_nonneg (sq_nonneg (x : ℝ)) (abs_nonneg (a - b))
    nlinarith
  · subst x
    have hbound := deathCouplingCost_equal_le a b y
    have hrest := mul_nonneg (sq_nonneg (y : ℝ)) (abs_nonneg (a - b))
    nlinarith
  · rw [deathCouplingCost_symm]
    have hbound := deathCouplingCost_strict_le b a hb y x h
    rw [abs_sub_comm b a] at hbound
    have hrest := mul_nonneg (sq_nonneg (y : ℝ)) (abs_nonneg (a - b))
    nlinarith

/-- The combined scalar positive-increment estimate before inserting the
Lipschitz control of mortality by the moment difference. -/
theorem quadraticCouplingCost_le (birth a b : ℝ)
    (hbirth : 0 ≤ birth) (ha : 0 ≤ a) (hb : 0 ≤ b) (x y : ℕ) :
    birthCouplingCost birth x y + deathCouplingCost a b x y ≤
      3 * birth * quadraticDistance x y +
      2 * ((x : ℝ)^2 + (y : ℝ)^2) * |a - b| := by
  exact add_le_add (birthCouplingCost_le birth hbirth x y) (deathCouplingCost_le a b ha hb x y)

/-- Substitution of a verified coefficient comparison into the full coupling
estimate. Here `transport` is a real bound supplied by a separately proved
moment/transport inequality, not an assumed stochastic limit. -/
theorem quadraticCouplingCost_le_transport (birth a b lip transport : ℝ)
    (hbirth : 0 ≤ birth) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcoeff : |a - b| ≤ lip * transport) (x y : ℕ) :
    birthCouplingCost birth x y + deathCouplingCost a b x y ≤
      3 * birth * quadraticDistance x y +
      2 * lip * ((x : ℝ)^2 + (y : ℝ)^2) * transport := by
  have hbound := quadraticCouplingCost_le birth a b hbirth ha hb x y
  have hmul := mul_le_mul_of_nonneg_left hcoeff
    (show 0 ≤ 2 * ((x : ℝ)^2 + (y : ℝ)^2) by positivity)
  nlinarith


/-- The cubic Lyapunov function is superlinear relative to quadratic feedback,
with the asymptotic statement expressed using Lean's filters. -/
theorem cubic_lyapunov_superlinear :
    Filter.Tendsto (fun n : ℕ => (1 + (n : ℝ)^3) / (1 + (n : ℝ)^2))
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono cubic_lyapunov_ratio_lower
  exact Filter.Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2)
    tendsto_natCast_atTop_atTop


/-- Nonnegative affine mortality is a concrete admissible feedback coefficient. -/
def affineMortality (base slope moment : ℝ) : ℝ := base + slope * moment

theorem affineMortality_nonneg (base slope moment : ℝ)
    (hbase : 0 ≤ base) (hslope : 0 ≤ slope) (hmoment : 0 ≤ moment) :
    0 ≤ affineMortality base slope moment := by
  unfold affineMortality
  positivity

theorem affineMortality_difference (base slope moment₁ moment₂ : ℝ) (hslope : 0 ≤ slope) :
    |affineMortality base slope moment₁ - affineMortality base slope moment₂| =
      slope * |moment₁ - moment₂| := by
  have heq : affineMortality base slope moment₁ - affineMortality base slope moment₂ =
      slope * (moment₁ - moment₂) := by unfold affineMortality; ring
  rw [heq, abs_mul, abs_of_nonneg hslope]

/-- Full coupling bound for the explicit untruncated affine second-moment model.
The transport module can replace the moment difference by its Wasserstein bound. -/
theorem affine_quadratic_coupling (birth base slope moment₁ moment₂ : ℝ)
    (hbirth : 0 ≤ birth) (hbase : 0 ≤ base) (hslope : 0 ≤ slope)
    (hm₁ : 0 ≤ moment₁) (hm₂ : 0 ≤ moment₂) (x y : ℕ) :
    birthCouplingCost birth x y +
      deathCouplingCost (affineMortality base slope moment₁)
        (affineMortality base slope moment₂) x y ≤
    3 * birth * quadraticDistance x y +
      2 * slope * ((x : ℝ)^2 + (y : ℝ)^2) * |moment₁ - moment₂| := by
  apply quadraticCouplingCost_le_transport birth _ _ slope |moment₁ - moment₂|
    hbirth (affineMortality_nonneg base slope moment₁ hbase hslope hm₁)
    (affineMortality_nonneg base slope moment₂ hbase hslope hm₂)
  exact le_of_eq (affineMortality_difference base slope moment₁ moment₂ hslope)

theorem affine_quadratic_activity (birth base slope moment : ℝ)
    (hbirth : 0 ≤ birth) (hbase : 0 ≤ base) (hslope : 0 ≤ slope)
    (hmoment : 0 ≤ moment) (n : ℕ) :
    quadraticActivity birth (affineMortality base slope moment) n ≤
      (3 * birth + 2 * base + 2 * slope) * (1 + (n : ℝ)^2) * (1 + moment) := by
  exact quadraticActivity_growth birth _ base slope moment hbirth
    (affineMortality_nonneg base slope moment hbase hslope hmoment)
    hbase hslope hmoment (le_refl _) n

theorem integrable_generator_first_moment (μ : MeasureTheory.Measure ℕ)
    (birth death : ℝ) (hfirst : MeasureTheory.Integrable (fun n : ℕ => (n : ℝ)) μ) :
    MeasureTheory.Integrable (generator birth death (fun k => (k : ℝ))) μ := by
  have heq : generator birth death (fun k => (k : ℝ)) =
      (fun n : ℕ => (birth - death) * n) := by
    funext n
    exact generator_first_moment birth death n
  rw [heq]
  exact hfirst.const_mul (birth - death)

theorem integrable_generator_second_moment (μ : MeasureTheory.Measure ℕ)
    (birth death : ℝ)
    (hfirst : MeasureTheory.Integrable (fun n : ℕ => (n : ℝ)) μ)
    (hsecond : MeasureTheory.Integrable (fun n : ℕ => (n : ℝ)^2) μ) :
    MeasureTheory.Integrable (generator birth death (fun k => (k : ℝ)^2)) μ := by
  have heq : generator birth death (fun k => (k : ℝ)^2) =
      (fun n : ℕ => 2 * (birth - death) * (n : ℝ)^2 + (birth + death) * n) := by
    funext n
    exact generator_second_moment birth death n
  rw [heq]
  exact (hsecond.const_mul (2 * (birth - death))).add (hfirst.const_mul (birth + death))

/-- Integrating the first-moment generator is legitimate under the stated
integrability assumption. This is an identity at a fixed environment, not a
claim that a stochastic process solves a forward equation. -/
theorem integral_generator_first_moment (μ : MeasureTheory.Measure ℕ)
    (birth death : ℝ) (_hfirst : MeasureTheory.Integrable (fun n : ℕ => (n : ℝ)) μ) :
    ∫ n, generator birth death (fun k => (k : ℝ)) n ∂μ =
      (birth - death) * ∫ n, (n : ℝ) ∂μ := by
  simp only [generator_first_moment, MeasureTheory.integral_const_mul]

/-- The two expected polynomial drifts close at order two whenever the
first and second moments are integrable. -/
theorem integral_generator_second_moment (μ : MeasureTheory.Measure ℕ)
    (birth death : ℝ)
    (hfirst : MeasureTheory.Integrable (fun n : ℕ => (n : ℝ)) μ)
    (hsecond : MeasureTheory.Integrable (fun n : ℕ => (n : ℝ)^2) μ) :
    ∫ n, generator birth death (fun k => (k : ℝ)^2) n ∂μ =
      2 * (birth - death) * (∫ n, (n : ℝ)^2 ∂μ) +
      (birth + death) * ∫ n, (n : ℝ) ∂μ := by
  simp only [generator_second_moment]
  rw [MeasureTheory.integral_add (hsecond.const_mul _) (hfirst.const_mul _)]
  simp only [MeasureTheory.integral_const_mul]


/-- The stronger scalar coupling estimate implies the precise weighted shape
of the manuscript's Assumption 2.2, with an explicit constant. -/
theorem quadraticCouplingCost_standard (birth a b lip transport moment₁ moment₂ : ℝ)
    (hbirth : 0 ≤ birth) (ha : 0 ≤ a) (hb : 0 ≤ b) (hlip : 0 ≤ lip)
    (htransport : 0 ≤ transport) (hm₁ : 0 ≤ moment₁) (hm₂ : 0 ≤ moment₂)
    (hcoeff : |a - b| ≤ lip * transport) (x y : ℕ) :
    birthCouplingCost birth x y + deathCouplingCost a b x y ≤
      (3 * birth + 2 * lip) *
        ((1 + moment₁ + moment₂) * quadraticDistance x y +
         (1 + (x : ℝ)^2 + (y : ℝ)^2) * transport) := by
  have hbound := quadraticCouplingCost_le_transport birth a b lip transport
    hbirth ha hb hcoeff x y
  have hd : 0 ≤ quadraticDistance x y := abs_nonneg _
  have hs : 0 ≤ (x : ℝ)^2 + (y : ℝ)^2 := by positivity
  have hC : 0 ≤ 3 * birth + 2 * lip := by positivity
  have hdmono : quadraticDistance x y ≤
      (1 + moment₁ + moment₂) * quadraticDistance x y := by
    have hm₁d := mul_nonneg hm₁ hd
    have hm₂d := mul_nonneg hm₂ hd
    nlinarith
  have hfirst₁ := mul_le_mul_of_nonneg_right
    (show 3 * birth ≤ 3 * birth + 2 * lip by linarith) hd
  have hfirst₂ := mul_le_mul_of_nonneg_left hdmono hC
  have hsecond₁ := mul_le_mul_of_nonneg_right
    (show 2 * lip ≤ 3 * birth + 2 * lip by linarith) hs
  have hsecond₂ : 2 * lip * ((x : ℝ)^2 + (y : ℝ)^2) ≤
      (3 * birth + 2 * lip) * (1 + (x : ℝ)^2 + (y : ℝ)^2) := by
    nlinarith
  have hsecond₃ := mul_le_mul_of_nonneg_right hsecond₂ htransport
  nlinarith

end CarryingCapacity.Models
