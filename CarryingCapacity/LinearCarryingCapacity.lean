import CarryingCapacity.RealPowerLyapunov
import CarryingCapacity.CoordinateMoments
import CarryingCapacity.OriginalParticleSystem

/-!
# Multitype carrying-capacity rates and the full real-power Lyapunov family

The model has per-capita type-dependent births, nonnegative globally l1-Lipschitz
mortality depending on the whole vector of type means, and arbitrary fixed
nonnegative mutation rates. The Lyapunov function is exactly `1 + |x|^p` for
any real `p > 1`. Mutations preserve total population and deaths decrease it.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace CarryingCapacity.LinearCarryingCapacity

/-- The untruncated multitype coefficients from Section 7. Mortality is
represented on real vectors, with assumptions only on the nonnegative orthant. -/
structure Coefficients (D : ℕ) where
  birth : Fin D → ℝ
  birth_nonnegative : ∀ i, 0 ≤ birth i
  mutation : {p : Fin D × Fin D // p.1 ≠ p.2} → ℝ
  mutation_nonnegative : ∀ p, 0 ≤ mutation p
  mortality : Fin D → (Fin D → ℝ) → ℝ
  mortality_nonnegative : ∀ i z, (∀ j, 0 ≤ z j) → 0 ≤ mortality i z
  lipschitzConstant : ℝ
  lipschitzConstant_nonnegative : 0 ≤ lipschitzConstant
  mortality_lipschitz : ∀ i z w, (∀ j, 0 ≤ z j) → (∀ j, 0 ≤ w j) →
    |mortality i z - mortality i w| ≤ lipschitzConstant * ∑ j, |z j - w j|

variable {D : ℕ} (c : Coefficients D)

/-- Actual birth, death and mutation rates using the genuine vector of means. -/
def rates : Rates D (MomentLaw MomentScale.linear D) where
  rate h x μ := match h with
    | .inl (.inl i) => c.birth i * x i
    | .inl (.inr i) => c.mortality i (CoordinateMoments.vector μ) * x i
    | .inr p => c.mutation p * x p.1.1
  nonnegative h x μ := by
    rcases h with (i | i) | p
    · exact mul_nonneg (c.birth_nonnegative i) (Nat.cast_nonneg _)
    · exact mul_nonneg (c.mortality_nonnegative i _ (CoordinateMoments.vector_nonneg μ))
        (Nat.cast_nonneg _)
    · exact mul_nonneg (c.mutation_nonnegative p) (Nat.cast_nonneg _)
  invalid_zero h x μ hi := by
    rcases h with (i | i) | p
    · exact False.elim (hi trivial)
    · have hx : x i = 0 := by simpa only [Jump.Admissible, not_lt, Nat.le_zero] using hi
      simp [hx]
    · have hx : x p.1.1 = 0 := by simpa only [Jump.Admissible, not_lt, Nat.le_zero] using hi
      simp [hx]

/-- Mortality's law dependence is controlled by the actual transport distance. -/
theorem mortality_difference_le (i : Fin D) (μ ν : MomentLaw MomentScale.linear D) :
    |c.mortality i (CoordinateMoments.vector μ) - c.mortality i (CoordinateMoments.vector ν)| ≤
      c.lipschitzConstant * wasserstein μ ν :=
  (c.mortality_lipschitz i _ _ (CoordinateMoments.vector_nonneg μ)
    (CoordinateMoments.vector_nonneg ν)).trans
      (mul_le_mul_of_nonneg_left (CoordinateMoments.l1_difference_le_wasserstein μ ν)
        c.lipschitzConstant_nonnegative)

/-- Global mortality growth follows from its coefficient assumptions. -/
theorem mortality_growth (i : Fin D) (μ : MomentLaw MomentScale.linear D) :
    c.mortality i (CoordinateMoments.vector μ) ≤ c.mortality i 0 +
      c.lipschitzConstant * moment μ := by
  have h := c.mortality_lipschitz i (CoordinateMoments.vector μ) 0
    (CoordinateMoments.vector_nonneg μ) (fun _ => le_rfl)
  simp only [Pi.zero_apply, sub_zero, abs_of_nonneg (CoordinateMoments.vector_nonneg μ _),
    CoordinateMoments.sum_vector] at h
  have hh := (le_abs_self (c.mortality i (CoordinateMoments.vector μ) - c.mortality i 0)).trans h
  linarith

/-- A finite nonnegative birth bound also covers dimension zero. -/
def birthBound : ℝ := ∑ i, c.birth i

theorem birthBound_nonnegative : 0 ≤ birthBound c :=
  Finset.sum_nonneg (fun i _ => c.birth_nonnegative i)

theorem birth_le_bound (i : Fin D) : c.birth i ≤ birthBound c :=
  Finset.single_le_sum (fun j _ => c.birth_nonnegative j) (Finset.mem_univ i)

/-- Total population is the cast of an actual natural number. -/
theorem populationSize_eq_nat (x : State D) : populationSize x = ((∑ i, x i : ℕ) : ℝ) := by
  simp [populationSize]

def lyapunov (p : ℝ) (x : State D) : ℝ := 1 + populationSize x ^ p

theorem lyapunov_nonnegative (p : ℝ) (x : State D) : 0 ≤ lyapunov p x :=
  add_nonneg zero_le_one (Real.rpow_nonneg (OriginalParticleSystem.population_nonnegative x) _)

theorem lyapunov_dominates {p : ℝ} (hp : 1 < p) (x : State D) :
    1 + momentWeight MomentScale.linear x ≤ lyapunov p x := by
  rw [linear_weight, lyapunov, populationSize_eq_nat]
  have h := RealPowerLyapunov.nat_rpow_le (∑ i, x i) (by norm_num : (0 : ℝ) < 1) hp.le
  simpa only [Real.rpow_one] using add_le_add_left h 1

theorem lyapunov_superlinear {p : ℝ} (hp : 1 < p) :
    Tendsto (fun x : State D => lyapunov p x / (1 + momentWeight MomentScale.linear x))
      (comap populationSize atTop) atTop := by
  have h := (RealPowerLyapunov.tendsto_ratio (by norm_num : (0 : ℝ) ≤ 1) hp).comp
    (tendsto_comap : Tendsto (populationSize : State D → ℝ)
      (comap populationSize atTop) atTop)
  simpa only [Function.comp_def, lyapunov, linear_weight, Real.rpow_one] using h

/-- The full untruncated generator has an explicit mortality-independent
real-power drift bound. -/
theorem generator_lyapunov_le {p : ℝ} (hp : 1 < p)
    (μ : MomentLaw MomentScale.linear D) (x : State D) :
    (rates c).generator μ (lyapunov p) x ≤
      (birthBound c * (p * (2 : ℝ) ^ (p - 1))) * lyapunov p x := by
  let delta : ℝ := (populationSize x + 1) ^ p - populationSize x ^ p
  have hpop := OriginalParticleSystem.population_nonnegative x
  have hd : 0 ≤ delta := sub_nonneg.mpr
    (Real.rpow_le_rpow hpop (by linarith) (by linarith : 0 ≤ p))
  have hsum : (rates c).generator μ (lyapunov p) x ≤
      ∑ h : Jump D, match h with
        | .inl (.inl i) => c.birth i * (x i : ℝ) * delta
        | _ => 0 := by
    apply Finset.sum_le_sum
    intro h _
    rcases h with (i | i) | ⟨⟨i, j⟩, hij⟩
    · have hs := OriginalParticleSystem.population_birth_sub x i
      have he : populationSize (Jump.advance (Jump.birth i) x) = populationSize x + 1 := by linarith
      change c.birth i * (x i : ℝ) *
        (lyapunov p (Jump.advance (Jump.birth i) x) - lyapunov p x) ≤ _
      simp only [lyapunov, he]
      dsimp [delta]
      ring_nf
      exact le_rfl
    · apply mul_nonpos_of_nonneg_of_nonpos ((rates c).nonnegative _ _ _)
      change (1 + populationSize (Jump.advance (Jump.death i) x) ^ p) -
        (1 + populationSize x ^ p) ≤ 0
      have hs := OriginalParticleSystem.population_death_sub_nonpos x i
      have hh := Real.rpow_le_rpow
        (OriginalParticleSystem.population_nonnegative (Jump.advance (Jump.death i) x))
        (show populationSize (Jump.advance (Jump.death i) x) ≤ populationSize x by linarith)
        (by linarith : 0 ≤ p)
      linarith
    · have hs := OriginalParticleSystem.population_mutation_sub x i j hij
      have he : populationSize (Jump.advance (Jump.mutation i j hij) x) = populationSize x := by linarith
      change _ * (lyapunov p (Jump.advance (Jump.mutation i j hij) x) - lyapunov p x) ≤ 0
      simp only [lyapunov, he, sub_self, mul_zero, le_refl]
  have hsum' : (rates c).generator μ (lyapunov p) x ≤
      (∑ i, c.birth i * (x i : ℝ)) * delta := by
    simpa only [Fintype.sum_sum_type, Finset.sum_const_zero, add_zero, Finset.sum_mul] using hsum
  have hb : (∑ i, c.birth i * (x i : ℝ)) ≤ birthBound c * populationSize x := by
    rw [populationSize, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
      (birth_le_bound c i) (Nat.cast_nonneg _))
  have hinc : populationSize x * delta ≤
      (p * (2 : ℝ) ^ (p - 1)) * populationSize x ^ p := by
    simpa only [populationSize_eq_nat, delta] using
      (RealPowerLyapunov.birth_increment_le (∑ i, x i) hp.le)
  have hC : 0 ≤ birthBound c * (p * (2 : ℝ) ^ (p - 1)) := by
    have hb0 := birthBound_nonnegative c
    positivity
  calc
    (rates c).generator μ (lyapunov p) x ≤
        (birthBound c * populationSize x) * delta :=
      hsum'.trans (mul_le_mul_of_nonneg_right hb hd)
    _ = birthBound c * (populationSize x * delta) := by ring
    _ ≤ birthBound c * ((p * (2 : ℝ) ^ (p - 1)) * populationSize x ^ p) :=
      mul_le_mul_of_nonneg_left hinc (birthBound_nonnegative c)
    _ ≤ (birthBound c * (p * (2 : ℝ) ^ (p - 1))) * lyapunov p x := by
      dsimp [lyapunov]
      nlinarith

/-- Proposition 7.3(4), for the actual multitype rates and every real `p > 1`. -/
def lyapunovControl (p : ℝ) (hp : 1 < p) :
    LyapunovControl MomentScale.linear (rates c) where
  function := lyapunov p
  dominates := lyapunov_dominates hp
  superlinear := lyapunov_superlinear hp
  drift := by
    refine ⟨birthBound c * (p * (2 : ℝ) ^ (p - 1)), ?_, ?_⟩
    · have hb := birthBound_nonnegative c
      positivity
    · intro x μ _
      have hi : 0 ≤ ∫ x : State D, lyapunov p x ∂μ.measure :=
        integral_nonneg (lyapunov_nonnegative p)
      have hb := birthBound_nonnegative c
      have hC : 0 ≤ birthBound c * (p * (2 : ℝ) ^ (p - 1)) := by positivity
      exact (generator_lyapunov_le c hp μ x).trans
        (mul_le_mul_of_nonneg_left (by linarith) hC)

end CarryingCapacity.LinearCarryingCapacity
