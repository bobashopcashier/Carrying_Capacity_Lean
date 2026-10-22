import CarryingCapacity.PoissonRestart

/-!
# First moments of the constructed Poisson counts

Integrability and expectations are derived from the actual Poisson mass
function, then transferred through the proved laws of counts and increments.
No moment identity is assumed as a property of the clock.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace CarryingCapacity.PoissonMoments
open CountableJumpProcess FrozenProcess PoissonIncrements

theorem poisson_mass_recursion (r : ℝ≥0) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * poissonPMFReal r (n + 1) =
      (r : ℝ) * poissonPMFReal r n := by
  unfold poissonPMFReal
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The weighted Poisson mass series has sum equal to its parameter. -/
theorem hasSum_poisson_firstMoment (r : ℝ≥0) :
    HasSum (fun n : ℕ => (n : ℝ) * poissonPMFReal r n) (r : ℝ) := by
  have hs : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * poissonPMFReal r (n + 1))
      (r : ℝ) := by
    simpa only [poisson_mass_recursion, mul_one] using (poissonPMFRealSum r).mul_left (r : ℝ)
  have h := (hasSum_nat_add_iff
    (f := fun n : ℕ => (n : ℝ) * poissonPMFReal r n) (g := (r : ℝ)) 1).mp hs
  simpa only [Finset.sum_range_one, Nat.cast_zero, zero_mul, add_zero] using h

/-- The extended first moment is finite and equals the Poisson parameter. -/
theorem lintegral_poisson_firstMoment (r : ℝ≥0) :
    (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂poissonMeasure r) = r := by
  rw [lintegral_countable']
  have he (n : ℕ) : (n : ℝ≥0∞) * poissonMeasure r {n} =
      ENNReal.ofReal ((n : ℝ) * poissonPMFReal r n) := by
    rw [poissonMeasure, PMF.toMeasure_apply_singleton _ n (measurableSet_singleton n)]
    change (n : ℝ≥0∞) * ENNReal.ofReal (poissonPMFReal r n) = _
    rw [ENNReal.ofReal_mul (by positivity)]
    simp
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (Nat.cast_nonneg n)
    poissonPMFReal_nonneg) (hasSum_poisson_firstMoment r).summable,
    (hasSum_poisson_firstMoment r).tsum_eq]
  exact ENNReal.ofReal_coe_nnreal

/-- Integrability is established before any real expectation is used. -/
theorem integrable_poisson_firstMoment (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun n : ℕ => Nat.cast_nonneg n))]
  simpa only [ENNReal.ofReal_natCast, lintegral_poisson_firstMoment] using
    (ENNReal.coe_lt_top : (r : ℝ≥0∞) < ⊤)

theorem integral_poisson_firstMoment (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun n : ℕ => Nat.cast_nonneg n))
    (measurable_of_countable _).aestronglyMeasurable]
  simp only [ENNReal.ofReal_natCast, lintegral_poisson_firstMoment, ENNReal.coe_toReal]

theorem integrable_proposalCount (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω => (proposalCount ω t : ℝ)) (waitingTimeLaw r hr) := by
  have h := integrable_poisson_firstMoment ⟨r * t, mul_nonneg hr.le ht⟩
  rw [← proposalCount_map r hr t ht] at h
  exact h.comp_measurable (measurable_proposalCount t)

theorem integral_proposalCount (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : 0 ≤ t) :
    (∫ ω, (proposalCount ω t : ℝ) ∂waitingTimeLaw r hr) = r * t := by
  rw [← integral_map_of_stronglyMeasurable (measurable_proposalCount t)
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).stronglyMeasurable,
    proposalCount_map r hr t ht, integral_poisson_firstMoment]
  rfl

theorem lintegral_proposalCount (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ ω, (proposalCount ω t : ℝ≥0∞) ∂waitingTimeLaw r hr) = ENNReal.ofReal (r * t) := by
  rw [← lintegral_map (measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞)))
    (measurable_proposalCount t), proposalCount_map r hr t ht, lintegral_poisson_firstMoment]
  exact ENNReal.ofReal_coe_nnreal.symm

theorem integrable_increment (r : ℝ) (hr : 0 < r) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Integrable (fun ω => (increment ω s t : ℝ)) (waitingTimeLaw r hr) := by
  have h := integrable_poisson_firstMoment ⟨r * t, mul_nonneg hr.le ht⟩
  rw [← increment_map r hr s t hs ht] at h
  exact h.comp_measurable (measurable_increment s t)

theorem integral_increment (r : ℝ) (hr : 0 < r) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (∫ ω, (increment ω s t : ℝ) ∂waitingTimeLaw r hr) = r * t := by
  rw [← integral_map_of_stronglyMeasurable (measurable_increment s t)
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).stronglyMeasurable,
    increment_map r hr s t hs ht, integral_poisson_firstMoment]
  rfl

end CarryingCapacity.PoissonMoments
