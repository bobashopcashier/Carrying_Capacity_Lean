import CarryingCapacity.MarkedStripCounts
import CarryingCapacity.PoissonFiniteDimensional

/-!
# Actual marked counts on deterministic finite time grids

Each category count on a time window is the sum of its mark indicators over
the corresponding consecutive block of proposal indices. The blocks are
pairwise disjoint on the proved full-measure locally finite clock event, and
their cardinalities are the actual clock increments. These are deterministic
identifications and measurability results, without an assumed marked-count law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

namespace CarryingCapacity.MarkedTimeCounts
open CountableJumpProcess FrozenProcess MarkedNoise MarkedStripCounts

local instance : (P : Prop) → Decidable P := Classical.propDecidable

/-- Number of category marks in a fixed half-open interval of indices. -/
def indexCount (B : Set ℝ) (a b : ℕ) (marks : ℕ → ℝ) : ℕ :=
  ∑ n ∈ Finset.Ico a b, if marks n ∈ B then 1 else 0

theorem measurable_indexCount (B : Set ℝ) (hB : MeasurableSet B) (a b : ℕ) :
    Measurable (indexCount B a b) :=
  Finset.measurable_sum _ (fun n _ =>
    Measurable.ite (hB.preimage (measurable_pi_apply n)) measurable_const measurable_const)

theorem measurable_indexCount_joint (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable (fun p : (ℕ × ℕ) × (ℕ → ℝ) => indexCount B p.1.1 p.1.2 p.2) := by
  have h : Measurable (fun p : (ℕ → ℝ) × (ℕ × ℕ) =>
      indexCount B p.2.1 p.2.2 p.1) :=
    measurable_from_prod_countable (fun n => measurable_indexCount B hB n.1 n.2)
  exact h.comp measurable_swap

/-- Prefix-count subtraction is an actual finite block count when endpoints are ordered. -/
theorem prefixCount_sub_eq_indexCount (B : Set ℝ) {a b : ℕ} (hab : a ≤ b)
    (marks : ℕ → ℝ) :
    prefixCount B b marks - prefixCount B a marks = indexCount B a b marks := by
  have h := Finset.sum_range_add_sum_Ico (fun n => if marks n ∈ B then 1 else 0) hab
  change prefixCount B a marks + indexCount B a b marks = prefixCount B b marks at h
  omega

/-- Multiplication of one category's mark factors over an index block gives
the corresponding power, including empty blocks and zero complex arguments. -/
theorem indexProduct_indicator_eq_pow (B : Set ℝ) (z : ℂ) (a b : ℕ) (marks : ℕ → ℝ) :
    (∏ n ∈ Finset.Ico a b, if marks n ∈ B then z else 1) =
      z ^ indexCount B a b marks := by
  rw [indexCount, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro n _
  by_cases hn : marks n ∈ B <;> simp [hn]

variable {q : ℕ} {ι : Type*}

/-- Proposal indices belonging to the interval `(u_a,u_{a+1}]`. -/
def indexBlock (u : Fin (q + 1) → ℝ) (ω : ClockSpace) (a : Fin q) : Finset ℕ :=
  Finset.Ico (proposalCount ω (u a.castSucc)) (proposalCount ω (u a.succ))

/-- Category counts on each consecutive time window of the actual marked strip. -/
def gridCounts (B : Fin q → ι → Set ℝ) (u : Fin (q + 1) → ℝ) (ω : StripSample)
    (a : Fin q) (i : ι) : ℕ :=
  windowCount (B a i) (u a.castSucc) (u a.succ) ω

/-- The same array computed directly from the actual consecutive mark blocks. -/
def blockCounts (B : Fin q → ι → Set ℝ) (u : Fin (q + 1) → ℝ) (ω : StripSample)
    (a : Fin q) (i : ι) : ℕ :=
  ∑ n ∈ indexBlock u ω.1 a, if ω.2 n ∈ B a i then 1 else 0

theorem measurable_gridCounts (B : Fin q → ι → Set ℝ) (hB : ∀ a i, MeasurableSet (B a i))
    (u : Fin (q + 1) → ℝ) : Measurable (gridCounts B u) :=
  measurable_pi_lambda _ (fun a => measurable_pi_lambda _ (fun i =>
    measurable_windowCount (B a i) (hB a i) (u a.castSucc) (u a.succ)))

theorem measurable_blockCounts (B : Fin q → ι → Set ℝ) (hB : ∀ a i, MeasurableSet (B a i))
    (u : Fin (q + 1) → ℝ) : Measurable (blockCounts B u) := by
  apply measurable_pi_lambda
  intro a
  apply measurable_pi_lambda
  intro i
  exact (measurable_indexCount_joint (B a i) (hB a i)).comp
    ((((measurable_proposalCount (u a.castSucc)).comp measurable_fst).prodMk
      ((measurable_proposalCount (u a.succ)).comp measurable_fst)).prodMk measurable_snd)

/-- A product-indexed vector convenient for finite-dimensional distribution laws. -/
def gridVector (B : Fin q → ι → Set ℝ) (u : Fin (q + 1) → ℝ) (ω : StripSample)
    (p : Fin q × ι) : ℕ := gridCounts B u ω p.1 p.2

theorem measurable_gridVector (B : Fin q → ι → Set ℝ) (hB : ∀ a i, MeasurableSet (B a i))
    (u : Fin (q + 1) → ℝ) : Measurable (gridVector B u) :=
  measurable_pi_lambda _ (fun p => measurable_windowCount (B p.1 p.2) (hB p.1 p.2)
    (u p.1.castSucc) (u p.1.succ))

/-- The block length is exactly the natural-valued difference of proposal counts. -/
theorem card_indexBlock (u : Fin (q + 1) → ℝ) (ω : ClockSpace) (a : Fin q) :
    (indexBlock u ω a).card =
      proposalCount ω (u a.succ) - proposalCount ω (u a.castSucc) := by
  simp [indexBlock]

/-- Direct identification with the existing actual-clock grid-increment API. -/
theorem card_indexBlock_eq_gridIncrement (u : Fin (q + 1) → ℝ) (ω : ClockSpace)
    (a : Fin q) : (indexBlock u ω a).card =
      PoissonFiniteDimensional.gridIncrements
        (fun i : Fin q => u i.succ - u i.castSucc) (u 0) ω a := by
  rw [PoissonFiniteDimensional.gridIncrements_at_times, card_indexBlock]

/-- On any locally finite clock, ordered times give the precise mark-index block. -/
theorem gridCounts_eq_blockCounts (B : Fin q → ι → Set ℝ) (u : Fin (q + 1) → ℝ)
    (hu : Monotone u) (ω : StripSample)
    (hfin : ∀ T : ℝ, {n : ℕ | arrival ω.1 n ≤ T}.Finite) :
    gridCounts B u ω = blockCounts B u ω := by
  funext a i
  exact prefixCount_sub_eq_indexCount (B a i)
    (proposalCount_mono hfin (hu (Fin.castSucc_le_succ a))) ω.2

theorem disjoint_indexBlock_of_lt (u : Fin (q + 1) → ℝ) (hu : Monotone u)
    (ω : ClockSpace) (hfin : ∀ T : ℝ, {n : ℕ | arrival ω n ≤ T}.Finite)
    {a b : Fin q} (hab : a < b) : Disjoint (indexBlock u ω a) (indexBlock u ω b) := by
  have hab' : a.succ ≤ b.castSucc := by
    apply Fin.le_iff_val_le_val.mpr
    change a.val + 1 ≤ b.val
    exact Nat.succ_le_of_lt (Fin.lt_iff_val_lt_val.mp hab)
  have hc := proposalCount_mono hfin (hu hab')
  apply Finset.disjoint_left.mpr
  intro n hn hm
  simp only [indexBlock, Finset.mem_Ico] at hn hm
  omega

/-- Distinct time windows use disjoint actual mark indices. -/
theorem pairwise_disjoint_indexBlock (u : Fin (q + 1) → ℝ) (hu : Monotone u)
    (ω : ClockSpace) (hfin : ∀ T : ℝ, {n : ℕ | arrival ω n ≤ T}.Finite) :
    Pairwise (fun a b => Disjoint (indexBlock u ω a) (indexBlock u ω b)) := by
  intro a b hab
  rcases lt_or_gt_of_ne hab with h | h
  · exact disjoint_indexBlock_of_lt u hu ω hfin h
  · exact (disjoint_indexBlock_of_lt u hu ω hfin h).symm

/-- One full-measure clock event identifies every grid's category blocks.
No positivity of the first grid time is needed for this deterministic identity. -/
theorem ae_gridCounts_eq_blockCounts (B : Fin q → ι → Set ℝ) : ∀ᵐ ω ∂stripLaw,
    ∀ u : Fin (q + 1) → ℝ, Monotone u →
      gridCounts B u ω = blockCounts B u ω := by
  filter_upwards [strip_ae_good] with ω hω
  exact fun u hu => gridCounts_eq_blockCounts B u hu ω hω.1.2

theorem ae_pairwise_disjoint_indexBlock : ∀ᵐ ω ∂stripLaw,
    ∀ u : Fin (q + 1) → ℝ, Monotone u →
      Pairwise (fun a b => Disjoint (indexBlock u ω.1 a) (indexBlock u ω.1 b)) := by
  filter_upwards [strip_ae_good] with ω hω
  exact fun u hu => pairwise_disjoint_indexBlock u hu ω.1 hω.1.2

/-- At nonnegative ordered grid times, the same counts are masses of the actual
translated strip counting measure on the corresponding time rectangles. -/
theorem ae_stripMeasure_gridCounts (B : Fin q → ι → Set ℝ)
    (hB : ∀ a i, MeasurableSet (B a i))
    (u : Fin (q + 1) → ℝ) (hu : Monotone u) (hu0 : 0 ≤ u 0) :
    ∀ᵐ ω ∂stripLaw, ∀ n : ℕ, ∀ a : Fin q, ∀ i : ι,
      stripMeasure n ω (Ioc (u a.castSucc) (u a.succ) ×ˢ B a i) =
        (gridCounts (fun a i => (fun x : ℝ => (n : ℝ) + x) ⁻¹' B a i) u ω a i : ℝ≥0∞) := by
  filter_upwards [ae_stripMeasure_window_rectangle] with ω hω
  intro n a i
  exact hω n (u a.castSucc) (u a.succ) (hu0.trans (hu (Fin.zero_le _)))
    (hu (Fin.castSucc_le_succ a)) (B a i) (hB a i)

end CarryingCapacity.MarkedTimeCounts
