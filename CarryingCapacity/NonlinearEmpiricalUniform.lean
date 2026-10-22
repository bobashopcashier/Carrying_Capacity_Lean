import CarryingCapacity.NonlinearEmpiricalSupremum
import CarryingCapacity.EmpiricalTimeGrid
import CarryingCapacity.IndependentArrayLLN
import CarryingCapacity.NonlinearVariationBounds

/-!
# Uniform empirical convergence of the actual independent nonlinear paths

The finite grid argument combines fixed-time empirical convergence with a
scalar law of large numbers for each cell's actual accepted-jump variation.
The supremum is taken over every real time in the construction interval.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace CarryingCapacity.NonlinearEmpiricalUniform
open CommonInitialNoise NonlinearParticleEmpirical

/-- A finite union of vanishing event probabilities still vanishes, allowing
the sample spaces and probability measures to change with the row size. -/
theorem measure_finite_union_tendsto_zero {ι : Type*} [Fintype ι]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (S : ∀ n, ι → Set (Ω n))
    (hS : ∀ i, Tendsto (fun n => P n (S n i)) atTop (𝓝 0)) :
    Tendsto (fun n => P n (⋃ i, S n i)) atTop (𝓝 0) := by
  classical
  have hu : ∀ n, P n (⋃ i, S n i) ≤ ∑ i, P n (S n i) := by
    intro n
    simpa using measure_biUnion_finset_le (μ := P n) Finset.univ (S n)
  have hl : Tendsto (fun n => ∑ i, P n (S n i)) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum Finset.univ (fun i _ => hS i)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
    (fun _ => zero_le _) hu

/-- The actual all-real supremum event is controlled by two finite unions:
grid errors and centered coordinate-variation averages. Only the coordinate
displacement estimate is allowed an exceptional null set. -/
theorem measure_sup_error_le_grid_events {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {N D m : ℕ} (κ : MomentScale) (hN : 0 < N)
    (u : Fin (m + 1) → ℝ) (hu : Monotone u)
    (T : ℝ) (hu0 : u 0 = 0) (huT : u (Fin.last m) = T)
    (z : Ω → ℝ → Fin N → State D) (v : ℝ → MomentLaw κ D)
    (V : Fin m → Ω → Fin N → ℝ) (b : Fin m → ℝ)
    (G A L ε : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L) (hε : G + A + 2 * L ≤ ε)
    (hdisp : ∀ᵐ p ∂P, ∀ (j : Fin m) (t : ℝ), t ∈ Ioc (u j.castSucc) (u j.succ) →
      ∀ i, adaptedDistance κ (z p t i) (z p (u j.castSucc) i) ≤ V j p i)
    (hmean : ∀ j, b j ≤ L)
    (hmod : ∀ (j : Fin m) (t : ℝ), t ∈ Ioc (u j.castSucc) (u j.succ) →
      wasserstein (v (u j.castSucc)) (v t) ≤ L) :
    P {p | ENNReal.ofReal ε < ⨆ t : Icc (0 : ℝ) T,
      ENNReal.ofReal (wasserstein (empiricalLaw κ hN (z p t)) (v t))} ≤
      P (⋃ j, {p | G < wasserstein (empiricalLaw κ hN (z p (u j))) (v (u j))}) +
      P (⋃ j, {p | A < |EmpiricalTimeGrid.meanVariation (V j p) - b j|}) := by
  have hs : ∀ᵐ p ∂P, ENNReal.ofReal ε < (⨆ t : Icc (0 : ℝ) T,
      ENNReal.ofReal (wasserstein (empiricalLaw κ hN (z p t)) (v t))) →
      p ∈ (⋃ j, {p | G < wasserstein (empiricalLaw κ hN (z p (u j))) (v (u j))}) ∪
      (⋃ j, {p | A < |EmpiricalTimeGrid.meanVariation (V j p) - b j|}) := by
    filter_upwards [hdisp] with p hp
    intro hbad
    by_contra hout
    have hg : ∀ j, wasserstein (empiricalLaw κ hN (z p (u j))) (v (u j)) ≤ G := by
      intro j
      by_contra hj
      exact hout (Or.inl (mem_iUnion.mpr ⟨j, not_le.mp hj⟩))
    have ha : ∀ j, |EmpiricalTimeGrid.meanVariation (V j p) - b j| ≤ A := by
      intro j
      by_contra hj
      exact hout (Or.inr (mem_iUnion.mpr ⟨j, not_le.mp hj⟩))
    exact not_lt_of_ge ((EmpiricalTimeGrid.supremum_error_le_of_grid κ hN u hu T hu0 huT
      (z p) v (fun j => V j p) b G A L hA hL hg hp hmean hmod ha).trans
        (ENNReal.ofReal_le_ofReal hε)) hbad
  exact (measure_mono_ae hs).trans (measure_union_le _ _)

/-- For a fixed finite grid, convergence of its finitely many error and
variation events implies the asserted supremum-tail convergence. The final
nonlinear-process theorem below supplies all these premises from actual laws. -/
theorem measure_sup_error_gt_tendsto_zero_of_grid
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    {D m : ℕ} (κ : MomentScale) (u : Fin (m + 1) → ℝ) (hu : Monotone u)
    (T : ℝ) (hu0 : u 0 = 0) (huT : u (Fin.last m) = T)
    (z : ∀ n, Ω n → ℝ → Fin (n + 1) → State D) (v : ℝ → MomentLaw κ D)
    (V : ∀ n, Fin m → Ω n → Fin (n + 1) → ℝ) (b : Fin m → ℝ)
    (G A L ε : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L) (hε : G + A + 2 * L ≤ ε)
    (hdisp : ∀ n, ∀ᵐ p ∂P n, ∀ (j : Fin m) (t : ℝ),
      t ∈ Ioc (u j.castSucc) (u j.succ) →
      ∀ i, adaptedDistance κ (z n p t i) (z n p (u j.castSucc) i) ≤ V n j p i)
    (hmean : ∀ j, b j ≤ L)
    (hmod : ∀ (j : Fin m) (t : ℝ), t ∈ Ioc (u j.castSucc) (u j.succ) →
      wasserstein (v (u j.castSucc)) (v t) ≤ L)
    (hgrid : ∀ j, Tendsto (fun n => P n
      {p | G < wasserstein (empiricalLaw κ (Nat.succ_pos n) (z n p (u j))) (v (u j))})
      atTop (𝓝 0))
    (hcenter : ∀ j, Tendsto (fun n => P n
      {p | A < |EmpiricalTimeGrid.meanVariation (V n j p) - b j|}) atTop (𝓝 0)) :
    Tendsto (fun n => P n {p | ENNReal.ofReal ε < ⨆ t : Icc (0 : ℝ) T,
      ENNReal.ofReal (wasserstein (empiricalLaw κ (Nat.succ_pos n) (z n p t)) (v t))})
      atTop (𝓝 0) := by
  have hg := measure_finite_union_tendsto_zero P
    (fun n j => {p | G < wasserstein (empiricalLaw κ (Nat.succ_pos n) (z n p (u j))) (v (u j))}) hgrid
  have hc := measure_finite_union_tendsto_zero P
    (fun n j => {p | A < |EmpiricalTimeGrid.meanVariation (V n j p) - b j|}) hcenter
  have hl := hg.add hc
  rw [zero_add] at hl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
    (fun _ => zero_le _) (fun n => measure_sup_error_le_grid_events (P n) κ
      (Nat.succ_pos n) u hu T hu0 huT (z n) v (V n) b G A L ε hA hL hε
      (hdisp n) hmean hmod)

variable {D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hActivity : MomentActivityBound κ q)
  (ν : MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hCoupling : MomentCouplingBound κ q)
  (hMoment : Integrable control.function ν.measure)
  {A : ℕ → Type*} [∀ n, MeasurableSpace (A n)]
  (initial : ∀ n, A n → Fin (n + 1) → State D) (hInitial : ∀ n, Measurable (initial n))
  (γ : ∀ n, Measure (A n)) [∀ n, IsProbabilityMeasure (γ n)]
  (hright : ∀ n, (γ n).map (initial n) = Measure.pi (fun _ : Fin (n + 1) => ν.measure))
include hInitial hright

/-- Fixed-time actual empirical-error tails vanish, using the proved genuine
first-moment convergence and Markov's inequality. -/
theorem measure_error_gt_tendsto_zero (t : Icc (0 : ℝ) T) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (γ n) (Fin (n + 1) × Jump D))
      {p | ε < error control hActivity ν T hT hCoupling hMoment n (initial n) t p})
      atTop (𝓝 0) := by
  have hbound : ∀ n, (law (γ n) (Fin (n + 1) × Jump D))
      {p | ε < error control hActivity ν T hT hCoupling hMoment n (initial n) t p} ≤
      ENNReal.ofReal (beta control hActivity ν T hT hCoupling hMoment n (initial n) (γ n) t) /
        ENNReal.ofReal ε := by
    intro n
    have hi := integrable_error control hActivity ν T hT hCoupling hMoment n
      (initial n) (γ n) (hInitial n) (hright n) t
    have hm := meas_ge_le_lintegral_div hi.aemeasurable.ennreal_ofReal
      (ne_of_gt (ENNReal.ofReal_pos.mpr hε)) ENNReal.ofReal_ne_top
    have hs : {p | ε < error control hActivity ν T hT hCoupling hMoment n (initial n) t p} ⊆
        {p | ENNReal.ofReal ε ≤ ENNReal.ofReal
          (error control hActivity ν T hT hCoupling hMoment n (initial n) t p)} := by
      intro p hp
      exact ENNReal.ofReal_le_ofReal hp.le
    apply (measure_mono hs).trans
    simpa only [beta, ← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall (error_nonnegative control hActivity ν T hT hCoupling hMoment n
        (initial n) t))] using hm
  have hb : Tendsto (fun n => ENNReal.ofReal
      (beta control hActivity ν T hT hCoupling hMoment n (initial n) (γ n) t)) atTop (𝓝 0) := by
    simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (beta_tendsto_zero control hActivity ν T hT hCoupling hMoment initial hInitial γ hright t)
  have hl : Tendsto (fun n => ENNReal.ofReal
      (beta control hActivity ν T hT hCoupling hMoment n (initial n) (γ n) t) /
        ENNReal.ofReal ε) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, zero_mul] using
      ENNReal.Tendsto.mul_const hb
        (Or.inr (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hε))))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
    (fun _ => zero_le _) hbound

/-- A cell variation observable satisfies the scalar law of large numbers
on the actual projected input records. Its only premise is genuine
single-record integrability; independence is derived from the record law. -/
theorem measure_record_average_gt_tendsto_zero
    (f : Sample (State D) (Jump D) → ℝ)
    (hf : Integrable f (law ν.measure (Jump D))) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (γ n) (Fin (n + 1) × Jump D))
      {p | ε < |EmpiricalTimeGrid.meanVariation
        (fun i => f (ParticleInputRecords.record (initial n) i p)) -
          ∫ x, f x ∂law ν.measure (Jump D)|}) atTop (𝓝 0) := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  have h := IndependentArrayLLN.measure_centered_mean_gt_tendsto_zero
    (law ν.measure (Jump D)) f hf
    (fun n => law (γ n) (Fin (n + 1) × Jump D))
    (fun n p i => ParticleInputRecords.record (initial n) i p)
    (fun n => (measurable_pi_lambda _
      (ParticleInputRecords.measurable_record (initial n) (hInitial n))).aemeasurable)
    (fun n => ParticleInputRecords.array_map (γ n) ν.measure (initial n) (hInitial n) (hright n)) ε hε
  simpa only [EmpiricalTimeGrid.meanVariation, FiniteGenerator.empiricalMean] using h

set_option maxHeartbeats 800000 in
/-- Proposition 6.2: the genuine independent empirical error converges
uniformly in probability over the whole construction interval. All variation
and marginal-modulus estimates are consequences of the actual nonlinear
process; no uniform convergence or stochastic comparison estimate is assumed. -/
theorem measure_runningError_gt_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (law (γ n) (Fin (n + 1) × Jump D))
      {p | ENNReal.ofReal ε < NonlinearEmpiricalSupremum.runningError
        control hActivity ν T hT hCoupling hMoment n (initial n) p}) atTop (𝓝 0) := by
  let C := NonlinearActivityBound.variationConstant hActivity control ν T
  have hC : 0 ≤ C := NonlinearActivityBound.variationConstant_nonnegative hActivity control ν T
  have hmesh : Tendsto (fun m : ℕ => 2 * (C * T / m)) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (C * T)).const_mul 2
  obtain ⟨m, hm, hsmall⟩ := ((eventually_gt_atTop 0).and
    (hmesh.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith)))).exists
  let u := EmpiricalTimeGrid.uniformGrid T m
  have hu : Monotone u := EmpiricalTimeGrid.uniformGrid_monotone T hT m
  have hu0 : u 0 = 0 := EmpiricalTimeGrid.uniformGrid_zero T m
  have huT : u (Fin.last m) = T := EmpiricalTimeGrid.uniformGrid_last T m hm
  have humem (j : Fin (m + 1)) : u j ∈ Icc (0 : ℝ) T := by
    constructor
    · simpa only [hu0] using hu (Fin.zero_le j)
    · simpa only [huT] using hu (Fin.le_last j)
  have hucell (j : Fin m) : u j.castSucc ≤ u j.succ := hu (by
    change j.val ≤ j.val + 1
    omega)
  let f : Fin m → Sample (State D) (Jump D) → ℝ := fun j p =>
    (NonlinearPathVariation.variation control hActivity ν T hT hCoupling hMoment
      (u j.castSucc) (u j.succ) p).toReal
  let b : Fin m → ℝ := fun j => ∫ p, f j p ∂law ν.measure (Jump D)
  let V : ∀ n, Fin m → Sample (A n) (Fin (n + 1) × Jump D) → Fin (n + 1) → ℝ :=
    fun n j p i => f j (ParticleInputRecords.record (initial n) i p)
  let z : ∀ n, Sample (A n) (Fin (n + 1) × Jump D) → ℝ → Fin (n + 1) → State D :=
    fun n p t i => NonlinearParticleArray.process control hActivity ν T hT hCoupling hMoment
      (initial n) i p t
  let v := NonlinearFixedPoint.environment control hActivity ν T hT hCoupling hMoment
  have hf (j : Fin m) : Integrable (f j) (law ν.measure (Jump D)) :=
    NonlinearVariationBounds.integrable_variationReal control hActivity ν T hT hCoupling hMoment
      (u j.castSucc) (u j.succ) (humem j.castSucc).1 (hucell j) (humem j.succ).2
  have hmean (j : Fin m) : b j ≤ C * T / m := by
    have hb := NonlinearVariationBounds.integral_variationReal_le control hActivity ν T hT
      hCoupling hMoment (u j.castSucc) (u j.succ) (humem j.castSucc).1 (hucell j) (humem j.succ).2
    simpa only [b, f, NonlinearVariationBounds.variationReal, C, u,
      EmpiricalTimeGrid.uniformGrid_mesh, mul_div_assoc] using hb
  have hmod (j : Fin m) (t : ℝ) (ht : t ∈ Ioc (u j.castSucc) (u j.succ)) :
      wasserstein (v (u j.castSucc)) (v t) ≤ C * T / m := by
    have hb := NonlinearVariationBounds.wasserstein_environment_le control hActivity ν T hT
      hCoupling hMoment (u j.castSucc) t (humem j.castSucc).1 ht.1.le (ht.2.trans (humem j.succ).2)
    apply hb.trans
    calc
      C * (t - u j.castSucc) ≤ C * (u j.succ - u j.castSucc) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 _) hC
      _ = _ := by dsimp only [u]; rw [EmpiricalTimeGrid.uniformGrid_mesh]; ring
  have hdisp (n : ℕ) : ∀ᵐ p ∂law (γ n) (Fin (n + 1) × Jump D),
      ∀ (j : Fin m) (t : ℝ), t ∈ Ioc (u j.castSucc) (u j.succ) →
        ∀ i, adaptedDistance κ (z n p t i) (z n p (u j.castSucc) i) ≤ V n j p i := by
    have hd (j : Fin m) (i : Fin (n + 1)) :=
      (NonlinearParticleArray.record_preserving ν (initial n) (hInitial n) (γ n) (hright n) i).quasiMeasurePreserving.ae
          (NonlinearVariationBounds.ae_distance_le_variationReal control hActivity ν T hT
            hCoupling hMoment (u j.castSucc) (u j.succ) (humem j.castSucc).1 (humem j.succ).2)
    filter_upwards [ae_all_iff.mpr (fun j => ae_all_iff.mpr (hd j))] with p hp
    intro j t ht i
    exact hp j i t ⟨ht.1.le, ht.2⟩
  have hg (j : Fin (m + 1)) := measure_error_gt_tendsto_zero control hActivity ν T hT hCoupling
    hMoment initial hInitial γ hright ⟨u j, humem j⟩ (ε / 4) (by linarith)
  have hc (j : Fin m) := measure_record_average_gt_tendsto_zero ν initial hInitial γ hright
    (f j) (hf j) (ε / 4) (by linarith)
  have h := measure_sup_error_gt_tendsto_zero_of_grid
    (fun n => law (γ n) (Fin (n + 1) × Jump D)) κ u hu T hu0 huT z v V b
    (ε / 4) (ε / 4) (C * T / m) ε (by linarith) (by positivity) (by linarith)
    hdisp hmean hmod hg hc
  exact h

/-- The same actual uniform convergence stated for real probabilities. -/
theorem probability_runningError_gt_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => ((law (γ n) (Fin (n + 1) × Jump D))
      {p | ENNReal.ofReal ε < NonlinearEmpiricalSupremum.runningError
        control hActivity ν T hT hCoupling hMoment n (initial n) p}).toReal) atTop (𝓝 0) := by
  exact ENNReal.tendsto_toReal ENNReal.zero_ne_top |>.comp
    (measure_runningError_gt_tendsto_zero control hActivity ν T hT hCoupling hMoment
      initial hInitial γ hright ε hε)

end CarryingCapacity.NonlinearEmpiricalUniform
