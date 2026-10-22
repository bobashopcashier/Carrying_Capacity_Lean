import CarryingCapacity.EmpiricalLLN
import CarryingCapacity.LyapunovFlowSpace
import CarryingCapacity.LyapunovTails
import CarryingCapacity.FiniteJumpForward

/-!
# Transport continuity from atoms and genuine Lyapunov bounds

Finite truncation preserves each retained nonzero atom. Its zero atom is
determined by the other finitely many atoms and total probability. Thus
atomic convergence gives transport convergence of the actual truncated laws.
Superlinear Lyapunov control makes the truncation costs uniformly small.
The triangle inequality then gives transport convergence without an assumed
total-variation or transport convergence premise.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical ENNReal Topology

namespace CarryingCapacity.AtomicTransportContinuity
open EmpiricalLLN LyapunovFlowSpace

variable {D : ℕ} {κ : MomentScale}

/-- The nonzero states retained by the actual finite truncation. -/
def retained (K : ℕ) : Finset (State D) :=
  (finite_moment_sublevel (D := D) κ (K : ℝ)).toFinset.erase 0

theorem mem_retained (K : ℕ) (x : State D) :
    x ∈ retained (κ := κ) K ↔ x ≠ 0 ∧ momentWeight κ x ≤ K := by
  simp [retained]

theorem preimage_zero (K : ℕ) :
    (truncate κ K) ⁻¹' {0} = (retained (κ := κ) (D := D) K : Set (State D))ᶜ := by
  ext x
  simp only [mem_preimage, mem_singleton_iff, mem_compl_iff, Finset.mem_coe, mem_retained]
  by_cases hx : momentWeight κ x ≤ K <;> simp [truncate, hx]

theorem truncateLaw_atom_zero (μ : MomentLaw κ D) (K : ℕ) :
    (truncateLaw μ K).measure.real {0} =
      1 - ∑ x ∈ retained (κ := κ) K, μ.measure.real {x} := by
  letI : IsProbabilityMeasure μ.measure := μ.probability
  change ((μ.measure.map (truncate κ K)) {0}).toReal = _
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _), preimage_zero]
  change μ.measure.real (retained (κ := κ) (D := D) K : Set (State D))ᶜ = _
  rw [measureReal_compl (retained (κ := κ) (D := D) K).measurableSet, measureReal_univ_eq_one,
    sum_measureReal_singleton]

theorem truncateLaw_atom_of_ne_zero (μ : MomentLaw κ D) (K : ℕ) (x : State D) (hx : x ≠ 0) :
    (truncateLaw μ K).measure.real {x} =
      if momentWeight κ x ≤ K then μ.measure.real {x} else 0 := by
  have hpre : (truncate κ K) ⁻¹' {x} = if momentWeight κ x ≤ K then {x} else ∅ := by
    ext y
    by_cases hy : momentWeight κ y ≤ K
    · by_cases he : y = x
      · subst y
        simp [truncate, hy]
      · simp [truncate, hy, he]
    · by_cases hxx : momentWeight κ x ≤ K
      · have hne : y ≠ x := by intro he; exact hy (he ▸ hxx)
        simp [truncate, hy, hx.symm, hxx, hne]
      · simp [truncate, hy, hx.symm, hxx]
  change ((μ.measure.map (truncate κ K)) {x}).toReal = _
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _), hpre]
  split_ifs <;> simp [measureReal_def]

/-- Truncated atom convergence includes the collapsed atom at zero. -/
theorem tendsto_truncated_atom {I : Type*} {l : Filter I}
    (μ : I → MomentLaw κ D) (ν : MomentLaw κ D)
    (h : ∀ x, Tendsto (fun i => (μ i).measure.real {x}) l (𝓝 (ν.measure.real {x})))
    (K : ℕ) (x : State D) :
    Tendsto (fun i => (truncateLaw (μ i) K).measure.real {x}) l
      (𝓝 ((truncateLaw ν K).measure.real {x})) := by
  by_cases hx : x = 0
  · subst x
    simp_rw [truncateLaw_atom_zero]
    exact tendsto_const_nhds.sub (tendsto_finset_sum _ (fun x _ => h x))
  · simp_rw [truncateLaw_atom_of_ne_zero _ K x hx]
    split_ifs
    · exact h x
    · exact tendsto_const_nhds

theorem tendsto_truncated_wasserstein {I : Type*} {l : Filter I}
    (μ : I → MomentLaw κ D) (ν : MomentLaw κ D)
    (h : ∀ x, Tendsto (fun i => (μ i).measure.real {x}) l (𝓝 (ν.measure.real {x})))
    (K : ℕ) :
    Tendsto (fun i => wasserstein (truncateLaw (μ i) K) (truncateLaw ν K)) l (𝓝 0) := by
  let S := (finite_range_truncate (κ := κ) (D := D) K).toFinset
  have hm (η : MomentLaw κ D) : (truncateLaw η K).measure S = 1 := by
    simpa only [S, Set.Finite.coe_toFinset] using truncateLaw_range_mass η K
  exact FiniteTransport.wasserstein_tendsto_of_finite_support _ _ S
    (fun i => hm (μ i)) (hm ν) (fun x _ => tendsto_truncated_atom μ ν h K x)

/-- Genuine uniform Lyapunov moments imply uniformly small actual
truncation-coupling costs, including the cost of the target law. -/
theorem uniform_truncation_tails {I : Type*}
    (Ψ : State D → ℝ) (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (μ : I → MomentLaw κ D) (hΨ : ∀ i, Integrable Ψ (μ i).measure)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ i, (∫ x, Ψ x ∂(μ i).measure) ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ i, (∫ x, tailWeight κ K x ∂(μ i).measure) < ε := by
  have hδ : 0 < ε / (B + 1) := div_pos hε (by linarith)
  obtain ⟨R, _hR, hr⟩ := LyapunovTails.exists_weight_cutoff hsuper hδ
  refine ⟨Nat.ceil R, ?_⟩
  intro i
  have hp (x : State D) : tailWeight κ (Nat.ceil R) x ≤ ε / (B + 1) * Ψ x := by
    by_cases hx : momentWeight κ x ≤ Nat.ceil R
    · simp only [tailWeight, if_pos hx]
      exact mul_nonneg hδ.le (by linarith [hdom x, momentWeight_nonneg κ x])
    · have hh := hr x (by have hc := Nat.le_ceil R; linarith [lt_of_not_ge hx])
      simp only [tailWeight, if_neg hx]
      linarith
  calc
    _ ≤ ∫ x, ε / (B + 1) * Ψ x ∂(μ i).measure :=
      integral_mono (integrable_tailWeight (μ i) _) ((hΨ i).const_mul _) hp
    _ = ε / (B + 1) * ∫ x, Ψ x ∂(μ i).measure := integral_const_mul _ _
    _ ≤ ε / (B + 1) * B := mul_le_mul_of_nonneg_left (hbound i) hδ.le
    _ < ε := by
      rw [div_mul_eq_mul_div]
      exact (div_lt_iff₀ (by linarith : 0 < B + 1)).mpr (by nlinarith)

/-- Atomic convergence and a genuine common superlinear moment bound give
convergence in the actual adapted transport metric. -/
theorem wasserstein_tendsto_of_atoms {I : Type*} {l : Filter I}
    (Ψ : State D → ℝ) (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (μ : I → MomentLaw κ D) (ν : MomentLaw κ D)
    (hΨ : ∀ i, Integrable Ψ (μ i).measure) (hν : Integrable Ψ ν.measure)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ i, (∫ x, Ψ x ∂(μ i).measure) ≤ B)
    (hνbound : (∫ x, Ψ x ∂ν.measure) ≤ B)
    (h : ∀ x, Tendsto (fun i => (μ i).measure.real {x}) l (𝓝 (ν.measure.real {x}))) :
    Tendsto (fun i => wasserstein (μ i) ν) l (𝓝 0) := by
  let family : Option I → MomentLaw κ D := fun i => i.elim ν μ
  have hi : ∀ i, Integrable Ψ (family i).measure := by intro i; cases i <;> simp_all [family]
  have hb : ∀ i, (∫ x, Ψ x ∂(family i).measure) ≤ B := by intro i; cases i <;> simp_all [family]
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun i => ha.trans_le (wasserstein_nonneg _ _))
  · intro ε hε
    obtain ⟨K, hK⟩ := uniform_truncation_tails Ψ hdom hsuper family hi B hB hb
      (ε := ε / 3) (by linarith)
    have he := (tendsto_truncated_wasserstein μ ν h K).eventually
      (gt_mem_nhds (show (0 : ℝ) < ε / 3 by linarith))
    filter_upwards [he] with i hi
    have h₁ := wasserstein_triangle (μ i) (truncateLaw (μ i) K) ν
    have h₂ := wasserstein_triangle (truncateLaw (μ i) K) (truncateLaw ν K) ν
    have h₃ := wasserstein_truncateLaw_le (μ i) K
    have h₄ := wasserstein_truncateLaw_le ν K
    have hμtail := hK (some i)
    have hνtail := hK none
    dsimp only [family, Option.elim] at hμtail hνtail
    rw [wasserstein_symm (truncateLaw ν K) ν] at h₂
    linarith

/-- Continuity of atom probabilities upgrades to transport continuity
under a genuine uniform superlinear moment bound. -/
theorem continuous_of_atoms {I : Type*} [TopologicalSpace I]
    (Ψ : State D → ℝ) (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (μ : I → MomentLaw κ D) (hΨ : ∀ i, Integrable Ψ (μ i).measure)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ i, (∫ x, Ψ x ∂(μ i).measure) ≤ B)
    (h : ∀ x, Continuous (fun i => (μ i).measure.real {x})) : Continuous μ := by
  apply continuous_iff_continuousAt.mpr
  intro i
  apply tendsto_iff_dist_tendsto_zero.mpr
  change Tendsto (fun j => wasserstein (μ j) (μ i)) (𝓝 i) (𝓝 0)
  exact wasserstein_tendsto_of_atoms Ψ hdom hsuper μ (μ i) hΨ (hΨ i) B hB hbound (hbound i)
    (fun x => (h x).continuousAt)

/-- A moment-bounded nonlinear weak forward solution is automatically
transport-continuous. Candidate continuity is not an assumption. -/
theorem continuousOn_of_isSolution
    (Ψ : State D → ℝ) (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (q : Rates D (MomentLaw κ D)) (ν : MomentLaw κ D) (v : ℝ → MomentLaw κ D)
    (T : ℝ) (hT : 0 ≤ T) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Icc 0 T, lyapunovIntegral Ψ (v t) ≤ ENNReal.ofReal B)
    (hv : FiniteJumpForward.IsSolution Jump.advance (fun j s x => q.rate j x (v s))
      ν.measure (fun s => (v s).measure) T) : ContinuousOn v (Icc 0 T) := by
  have hpos (x : State D) : 0 ≤ Ψ x := by linarith [hdom x, momentWeight_nonneg κ x]
  have hb (s : Icc (0 : ℝ) T) :=
    (lyapunovIntegral_le_iff hpos (v s) hB).mp (hbound s s.property)
  apply continuousOn_iff_continuous_restrict.mpr
  exact continuous_of_atoms Ψ hdom hsuper (fun s : Icc (0 : ℝ) T => v s)
    (fun s => (hb s).1) B hB (fun s => (hb s).2)
    (fun x => continuousOn_iff_continuous_restrict.mp
      (FiniteJumpForward.continuousOn_atom Jump.advance (fun j s x => q.rate j x (v s))
        ν.measure (fun s => (v s).measure) T hT hv x))

end CarryingCapacity.AtomicTransportContinuity
