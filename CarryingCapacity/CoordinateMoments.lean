import CarryingCapacity.TransportMetric
import CarryingCapacity.EmpiricalMeasure

/-!
# The vector of coordinate moments

The full vector of coordinate kappa-moments is controlled in the l1 norm by
the adapted transport distance. For the linear scale this is the actual vector
of type means used in the carrying-capacity coefficients and mean equation.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology NNReal

namespace CarryingCapacity.CoordinateMoments
variable {D : ℕ} {κ : MomentScale}

/-- Each component is an actual finite integral. -/
def vector (μ : MomentLaw κ D) (i : Fin D) : ℝ := ∫ x, κ.value (x i) ∂μ.measure

theorem integrable_coordinate (μ : MomentLaw κ D) (i : Fin D) :
    Integrable (fun x => κ.value (x i)) μ.measure := by
  apply μ.integrable_weight.mono' (measurable_of_countable _).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (κ.value_nonneg _)]
    exact Finset.single_le_sum (fun j _ => κ.value_nonneg (x j)) (Finset.mem_univ i))

theorem vector_nonneg (μ : MomentLaw κ D) (i : Fin D) : 0 ≤ vector μ i :=
  integral_nonneg (fun x => κ.value_nonneg (x i))

theorem sum_vector (μ : MomentLaw κ D) : ∑ i, vector μ i = moment μ := by
  change (∑ i, ∫ x, κ.value (x i) ∂μ.measure) = ∫ x, ∑ i, κ.value (x i) ∂μ.measure
  exact (integral_finset_sum _ (fun i _ => integrable_coordinate μ i)).symm

theorem integrable_first {μ ν : MomentLaw κ D} (c : Coupling μ ν) (i : Fin D) :
    Integrable (fun p => κ.value (p.1 i)) c.measure := by
  have h : Integrable (fun x => κ.value (x i)) (c.measure.map Prod.fst) := by
    rw [c.first_marginal]
    exact integrable_coordinate μ i
  exact h.comp_measurable measurable_fst

theorem integrable_second {μ ν : MomentLaw κ D} (c : Coupling μ ν) (i : Fin D) :
    Integrable (fun p => κ.value (p.2 i)) c.measure := by
  have h : Integrable (fun x => κ.value (x i)) (c.measure.map Prod.snd) := by
    rw [c.second_marginal]
    exact integrable_coordinate ν i
  exact h.comp_measurable measurable_snd

theorem integral_first {μ ν : MomentLaw κ D} (c : Coupling μ ν) (i : Fin D) :
    (∫ p, κ.value (p.1 i) ∂c.measure) = vector μ i := by
  rw [← integral_map_of_stronglyMeasurable measurable_fst
    (measurable_of_countable (fun x : State D => κ.value (x i))).stronglyMeasurable,
    c.first_marginal]
  rfl

theorem integral_second {μ ν : MomentLaw κ D} (c : Coupling μ ν) (i : Fin D) :
    (∫ p, κ.value (p.2 i) ∂c.measure) = vector ν i := by
  rw [← integral_map_of_stronglyMeasurable measurable_snd
    (measurable_of_countable (fun x : State D => κ.value (x i))).stronglyMeasurable,
    c.second_marginal]
  rfl

/-- The l1 error of all coordinate moments is bounded by any genuine coupling cost. -/
theorem l1_difference_le_cost {μ ν : MomentLaw κ D} (c : Coupling μ ν) :
    (∑ i, |vector μ i - vector ν i|) ≤ c.cost := by
  calc
    (∑ i, |vector μ i - vector ν i|) ≤
        ∑ i, ∫ p, |κ.value (p.1 i) - κ.value (p.2 i)| ∂c.measure := by
      apply Finset.sum_le_sum
      intro i _
      rw [← integral_first c i, ← integral_second c i,
        ← integral_sub (integrable_first c i) (integrable_second c i)]
      exact abs_integral_le_integral_abs
    _ = c.cost := by
      change (∑ i, ∫ p, |κ.value (p.1 i) - κ.value (p.2 i)| ∂c.measure) =
        ∫ p, ∑ i, |κ.value (p.1 i) - κ.value (p.2 i)| ∂c.measure
      exact (integral_finset_sum _
        (fun i _ => ((integrable_first c i).sub (integrable_second c i)).abs)).symm

/-- Section 2's coordinate-vector version, and Proposition 7.3(1) for linear kappa. -/
theorem l1_difference_le_wasserstein (μ ν : MomentLaw κ D) :
    (∑ i, |vector μ i - vector ν i|) ≤ wasserstein μ ν := by
  apply le_csInf (Set.range_nonempty _)
  rintro r ⟨c, rfl⟩
  exact l1_difference_le_cost c

theorem coordinate_difference_le_wasserstein (μ ν : MomentLaw κ D) (i : Fin D) :
    |vector μ i - vector ν i| ≤ wasserstein μ ν :=
  (Finset.single_le_sum (fun j _ => abs_nonneg (vector μ j - vector ν j))
    (Finset.mem_univ i)).trans (l1_difference_le_wasserstein μ ν)

theorem coordinate_lipschitz (i : Fin D) :
    LipschitzWith 1 (fun μ : MomentLaw κ D => vector μ i) := by
  apply LipschitzWith.of_dist_le_mul
  intro μ ν
  simpa only [Real.dist_eq, momentLaw_dist, NNReal.coe_one, one_mul] using
    coordinate_difference_le_wasserstein μ ν i

theorem continuous_vector : Continuous (vector : MomentLaw κ D → Fin D → ℝ) :=
  continuous_pi (fun i => (coordinate_lipschitz i).continuous)

theorem continuous_l1Difference : Continuous
    (fun p : MomentLaw κ D × MomentLaw κ D => ∑ i, |vector p.1 i - vector p.2 i|) :=
  continuous_finset_sum _ (fun i _ =>
    (((coordinate_lipschitz i).continuous.comp continuous_fst).sub
      ((coordinate_lipschitz i).continuous.comp continuous_snd)).abs)

theorem continuousWithinAt_l1Difference_ofReal
    {X Y : ℝ → MomentLaw κ D} {s : Set ℝ} {t : ℝ}
    (hX : ContinuousWithinAt X s t) (hY : ContinuousWithinAt Y s t) :
    ContinuousWithinAt (fun u => ENNReal.ofReal (∑ i, |vector (X u) i - vector (Y u) i|)) s t := by
  have hxy : ContinuousWithinAt (fun u => (X u, Y u)) s t := hX.prodMk hY
  have hd : ContinuousWithinAt
      (fun u => ∑ i : Fin D, |vector (X u) i - vector (Y u) i|) s t :=
    ContinuousAt.comp_continuousWithinAt (f := fun u => (X u, Y u))
      (g := fun z : MomentLaw κ D × MomentLaw κ D => ∑ i, |vector z.1 i - vector z.2 i|)
      (continuous_l1Difference (κ := κ) (D := D)).continuousAt hxy
  exact ContinuousAt.comp_continuousWithinAt
    (f := fun u => ∑ i : Fin D, |vector (X u) i - vector (Y u) i|) (g := ENNReal.ofReal)
    ENNReal.continuous_ofReal.continuousAt hd

/-- In particular all type means converge whenever the genuine transport distance vanishes. -/
theorem vector_tendsto {I : Type*} {l : Filter I} (μ : I → MomentLaw κ D) (ν : MomentLaw κ D)
    (h : Tendsto (fun i => wasserstein (μ i) ν) l (𝓝 0)) :
    Tendsto (fun i => vector (μ i)) l (𝓝 (vector ν)) := by
  apply tendsto_pi_nhds.mpr
  intro j
  rw [Metric.tendsto_nhds] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with i hi
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (wasserstein_nonneg (μ i) ν)] at hi
  rw [Real.dist_eq]
  exact (coordinate_difference_le_wasserstein (μ i) ν j).trans_lt hi

@[simp] theorem vector_empirical {N : ℕ} (hN : 0 < N) (z : Fin N → State D) (i : Fin D) :
    vector (empiricalLaw κ hN z) i = FiniteGenerator.empiricalMean (fun x => κ.value (x i)) z :=
  integral_empiricalLaw κ hN z _

/-- The linear specialization is exactly the vector of ordinary type means. -/
@[simp] theorem linear_vector (μ : MomentLaw MomentScale.linear D) (i : Fin D) :
    vector μ i = ∫ x, (x i : ℝ) ∂μ.measure := rfl

end CarryingCapacity.CoordinateMoments
