import CarryingCapacity.PopulationCouplingRemoval
import CarryingCapacity.PopulationStoppedExchangeability
import CarryingCapacity.PopulationCouplingProbability

/-!
# Actual finite-coordinate comparison events

A fixed collection of coordinates shares a single common exit event. Outside
that event all actual coordinate running costs equal their stopped versions.
A finite union bound and the proved stopped-cost measurability give the focal
Markov estimate before applying exchangeability.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal NNReal

namespace CarryingCapacity.PopulationFocalProbability
open CommonInitialNoise ConfigurationLocalization PopulationStoppedCoupling PopulationCouplingRemoval

/-- The first k particles that exist in the finite configuration. This
convention defines the statistic even before the population reaches k. -/
def focalIndices (N k : ℕ) : Finset (Fin N) := Finset.univ.filter (fun i => i.val < k)

theorem mem_focalIndices {N k : ℕ} (i : Fin N) : i ∈ focalIndices N k ↔ i.val < k := by
  simp [focalIndices]

/-- The number of selected coordinates never exceeds the fixed focal size. -/
theorem card_focalIndices_le (N k : ℕ) : (focalIndices N k).card ≤ k := by
  have hsub : (focalIndices N k).image Fin.val ⊆ Finset.range k := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr ((mem_focalIndices i).mp hi)
  calc
    (focalIndices N k).card = ((focalIndices N k).image Fin.val).card :=
      (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (Finset.range k).card := Finset.card_le_card hsub
    _ = k := Finset.card_range k

variable {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N) (hActivity : MomentActivityBound κ q)
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))
  {A : Type*} [MeasurableSpace A] (initialX initialY : A → Configuration N D)

/-- Maximum of the actual coordinate running costs for the selected particles;
the maximum over an empty set is zero. -/
def focalRunningCost (F : Finset (Fin N)) (S : ℝ) (p : Sample A (Label N D)) : ℝ≥0∞ :=
  F.sup (fun i => coordinateRunningCost control hN hActivity v T hT hv initialX initialY i S p)

omit [MeasurableSpace A] in
/-- Exceeding a threshold means that an actual selected coordinate exceeds it. -/
theorem lt_focalRunningCost_iff (F : Finset (Fin N)) (S : ℝ) (p : Sample A (Label N D))
    (ε : ℝ≥0∞) :
    ε < focalRunningCost control hN hActivity v T hT hv initialX initialY F S p ↔
      ∃ i ∈ F, ε < coordinateRunningCost control hN hActivity v T hT hv initialX initialY i S p :=
  Finset.lt_sup_iff

omit [MeasurableSpace A] in
/-- The same exit event is used for the entire finite collection. -/
theorem focal_event_subset (F : Finset (Fin N)) (R S : ℝ) (ε : ℝ≥0∞) :
    {p | ε < focalRunningCost control hN hActivity v T hT hv initialX initialY F S p} ⊆
      {p | pairExit control hN hActivity v T hT hv initialX initialY R p ≤ ENNReal.ofReal S} ∪
        ⋃ i ∈ F, {p | ε ≤ coordinateStoppedCost control hN hActivity v T hT hv initialX initialY R i S p} := by
  intro p hp
  by_cases he : pairExit control hN hActivity v T hT hv initialX initialY R p ≤ ENNReal.ofReal S
  · exact Or.inl he
  · apply Or.inr
    obtain ⟨i,hi,hc⟩ := (lt_focalRunningCost_iff control hN hActivity v T hT hv initialX initialY F S p ε).mp hp
    refine mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,?_⟩⟩
    change ε ≤ coordinateStoppedCost control hN hActivity v T hT hv initialX initialY R i S p
    rw [← coordinateRunningCost_eq_stopped_of_le control hN hActivity v T hT hv initialX initialY
      R i S p (lt_of_not_ge he).le]
    exact hc.le

variable (μ : Measure A) [IsProbabilityMeasure μ]
  (hCoupling : MomentCouplingBound κ q) (hinitX : Measurable initialX) (hinitY : Measurable initialY)
  (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ s ∈ Icc 0 T,
    LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
  (hInitialX : Integrable (fun a => lyapunov control (initialX a)) μ)
  (hInitialY : Integrable (fun a => lyapunov control (initialY a)) μ)
include hCoupling hinitX hinitY hB hEnv hInitialX hInitialY

/-- The actual finite maximum is AE measurable. -/
theorem aemeasurable_focalRunningCost (F : Finset (Fin N)) (S : ℝ≥0) :
    AEMeasurable (focalRunningCost control hN hActivity v T hT hv initialX initialY F S)
      (law μ (Label N D)) := by
  change AEMeasurable (fun p => F.sup (fun i =>
    coordinateRunningCost control hN hActivity v T hT hv initialX initialY i S p)) _
  induction F using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty] using (aemeasurable_const (b := (0 : ℝ≥0∞)))
  | @insert i F hi ih =>
    simpa only [Finset.sup_insert] using
      (aemeasurable_coordinateRunningCost control hN hActivity v T hT hv initialX initialY μ
        hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY i S).sup ih

/-- A union bound followed by genuine extended Markov estimates. Coordinate
expectations are not assumed equal; that is established separately by relabeling. -/
theorem probability_focal_le_exit_sum (F : Finset (Fin N)) (R : ℝ) (S : ℝ≥0)
    (ε : ℝ) (hε : 0 < ε) :
    (law μ (Label N D))
      {p | ENNReal.ofReal ε < focalRunningCost control hN hActivity v T hT hv initialX initialY F S p} ≤
      (law μ (Label N D))
        {p | pairExit control hN hActivity v T hT hv initialX initialY R p ≤ (S : ℝ≥0∞)} +
      (ENNReal.ofReal ε)⁻¹ * ∑ i ∈ F,
        ∫⁻ p, coordinateStoppedCost control hN hActivity v T hT hv initialX initialY R i S p
          ∂law μ (Label N D) := by
  have hu := (measure_mono (μ := law μ (Label N D))
    (focal_event_subset control hN hActivity v T hT hv initialX initialY F R S (ENNReal.ofReal ε))).trans
    (measure_union_le _ _)
  have hf := measure_biUnion_finset_le (μ := law μ (Label N D)) F
    (fun i => {p | ENNReal.ofReal ε ≤
      coordinateStoppedCost control hN hActivity v T hT hv initialX initialY R i S p})
  apply (hu.trans (add_le_add_left hf _)).trans
  simp only [ENNReal.ofReal_coe_nnreal]
  apply add_le_add_left
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi := meas_ge_le_lintegral_div
    (aemeasurable_coordinateStoppedCost control hN hActivity v T hT hv initialX initialY μ
      hCoupling hinitX hinitY B hB hEnv hInitialX hInitialY R i S)
    (ne_of_gt (ENNReal.ofReal_pos.mpr hε)) ENNReal.ofReal_ne_top
  simpa only [ENNReal.div_eq_inv_mul] using hi

end CarryingCapacity.PopulationFocalProbability

namespace CarryingCapacity.PopulationFocalProbability
open CommonInitialNoise ConfigurationLocalization PopulationCouplingInitialization
open PopulationStoppedCoupling PopulationCouplingTime PopulationCouplingExit
open PopulationStoppedExchangeability

variable {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q) (hN : 0 < N) (hActivity : MomentActivityBound κ q)
  (v : ℝ → MomentLaw κ D) (T : ℝ) (hT : 0 ≤ T) (hv : ContinuousOn v (Icc 0 T))
  (γ : Measure (Record N D)) [IsProbabilityMeasure γ]
  (hex : ExchangeableMatching.ExchangeableLaw γ)
  (hCoupling : MomentCouplingBound κ q) (B : ℝ) (hB : 0 ≤ B)
  (hEnv : ∀ s ∈ Icc 0 T,
    LyapunovFlowSpace.lyapunovIntegral control.function (v s) ≤ ENNReal.ofReal B)
  (hInitialX : Integrable (fun a => lyapunov control (left a)) γ)
  (hInitialY : Integrable (fun a => lyapunov control (right a)) γ)
include hex hCoupling hB hEnv hInitialX hInitialY

/-- The genuine fixed-particle probability estimate. The full paired-input
symmetry proves equality of stopped coordinate expectations; the common exit
tail is counted once. All real conversions use an already finite expectation.
For populations smaller than k, the statistic selects all existing particles. -/
theorem probability_focalRunningCost_le (M : ℝ)
    (hMX : (∫ a, lyapunov control (left a) ∂γ) ≤ M)
    (hMY : (∫ a, lyapunov control (right a) ∂γ) ≤ M)
    (R : ℝ) (hR : 0 < R) (S : ℝ≥0) (hST : (S : ℝ) ≤ T)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (law γ (Label N D)).real
      {p | ENNReal.ofReal ε < focalRunningCost control hN hActivity v T hT hv
        left right (focalIndices N k) S p} ≤
    exitConstant control B M S / R +
      (k : ℝ) * expectedCost control hN hActivity v T hT hv left right γ R S / ε := by
  have hm := probability_focal_le_exit_sum control hN hActivity v T hT hv left right γ
    hCoupling measurable_left measurable_right B hB hEnv hInitialX hInitialY
    (focalIndices N k) R S ε hε
  have hcoord (i : Fin N) := lintegral_coordinateStoppedCost_eq_expectedStoppedCost
    control hN hActivity v T hT hv γ hex hCoupling B hB hEnv hInitialX hInitialY R i S
  simp_rw [hcoord] at hm
  simp only [Finset.sum_const, nsmul_eq_mul] at hm
  have hcard : ((focalIndices N k).card : ℝ≥0∞) ≤ (k : ℝ≥0∞) := by
    exact_mod_cast card_focalIndices_le N k
  have he := pairExit_probability_le_uniform control hN hActivity v T hT hv left right γ
    hCoupling measurable_left measurable_right B hB hEnv hInitialX hInitialY
    M hMX hMY R S hR S.coe_nonneg
  simp only [ENNReal.ofReal_coe_nnreal] at he
  have hb := hm.trans (add_le_add he (mul_le_mul_left' (mul_le_mul_right' hcard _) _))
  have hf := expectedStoppedCost_eq_ofReal control hN hActivity v T hT hv left right γ
    hCoupling measurable_left measurable_right B hB hEnv hInitialX hInitialY
    R hR.le S ⟨S.coe_nonneg, hST⟩
  rw [hf] at hb
  have hε' : ENNReal.ofReal ε ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hε)
  have hi : (ENNReal.ofReal ε)⁻¹ ≠ ⊤ := by simp [hε']
  have hku : (k : ℝ≥0∞) *
      ENNReal.ofReal (expectedCost control hN hActivity v T hT hv left right γ R S) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top k) ENNReal.ofReal_ne_top
  have hp : (ENNReal.ofReal ε)⁻¹ * ((k : ℝ≥0∞) *
      ENNReal.ofReal (expectedCost control hN hActivity v T hT hv left right γ R S)) ≠ ⊤ :=
    ENNReal.mul_ne_top hi hku
  have hfinite : ENNReal.ofReal (exitConstant control B M S / R) +
      (ENNReal.ofReal ε)⁻¹ * ((k : ℝ≥0∞) *
        ENNReal.ofReal (expectedCost control hN hActivity v T hT hv left right γ R S)) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hp⟩
  have hM : 0 ≤ M := (integral_nonneg (fun a => lyapunov_nonnegative control (left a))).trans hMX
  have htail := div_nonneg (PopulationCouplingProbability.exitConstant_nonnegative control B M S hM) hR.le
  have hcost := expectedCost_nonnegative control hN hActivity v T hT hv left right γ R (S : ℝ)
  have hr := ENNReal.toReal_mono hfinite hb
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hp, ENNReal.toReal_ofReal htail,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal hε.le, ENNReal.toReal_ofReal hcost] at hr
  simpa only [Measure.real, div_eq_mul_inv, mul_comm ε⁻¹] using hr

end CarryingCapacity.PopulationFocalProbability
