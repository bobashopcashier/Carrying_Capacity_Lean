import CarryingCapacity.PredictableSets
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Strict-past deterministic approximations

On positive times, the grid value `(ceil ((n+1)*t)-1)/(n+1)` is strictly
smaller than `t`, converges to `t`, and is constant on each right-closed grid
cell. Adapted samples at these grid values are therefore measurable in the
actual positive-time predictable sigma algebra. Values at nonpositive times
are assigned a fixed default, as required by that sigma algebra.
-/

noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology

namespace CarryingCapacity.PredictableStepApproximation
open PredictableSets

/-- Left endpoint of the right-closed grid cell containing a positive time. -/
def leftGrid (n : ℕ) (t : ℝ) : ℝ :=
  ((⌈t * (n + 1)⌉₊ - 1 : ℕ) : ℝ) / (n + 1)

theorem leftGrid_nonneg (n : ℕ) (t : ℝ) : 0 ≤ leftGrid n t := by
  unfold leftGrid
  positivity

theorem leftGrid_cell (n : ℕ) (t : ℝ) (ht : 0 < t) :
    t ∈ Ioc (leftGrid n t) (leftGrid n t + 1 / (n + 1)) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hc : 1 ≤ ⌈t * (n + 1)⌉₊ := Nat.one_le_ceil_iff.mpr (mul_pos ht hn)
  have he := (Nat.ceil_eq_iff (Nat.ne_zero_of_lt hc)).mp rfl
  constructor
  · exact (div_lt_iff₀ hn).mpr he.1
  · unfold leftGrid
    rw [Nat.cast_sub hc, Nat.cast_one]
    have heq : ((⌈t * (n + 1)⌉₊ : ℝ) - 1) / (n + 1) + 1 / (n + 1) =
        (⌈t * (n + 1)⌉₊ : ℝ) / (n + 1) := by ring
    rw [heq]
    exact (le_div_iff₀ hn).mpr he.2

theorem leftGrid_lt (n : ℕ) (t : ℝ) (ht : 0 < t) : leftGrid n t < t :=
  (leftGrid_cell n t ht).1

theorem leftGrid_eq_of_mem_cell (n k : ℕ) (t : ℝ)
    (ht : t ∈ Ioc ((k : ℝ) / (n + 1)) ((k + 1 : ℕ) / (n + 1))) :
    leftGrid n t = (k : ℝ) / (n + 1) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have he : ⌈t * (n + 1)⌉₊ = k + 1 := by
    apply (Nat.ceil_eq_iff (Nat.succ_ne_zero k)).mpr
    simpa only [Nat.add_sub_cancel] using
      And.intro ((div_lt_iff₀ hn).mp ht.1) ((le_div_iff₀ hn).mp ht.2)
  simp [leftGrid, he]

theorem tendsto_leftGrid (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => leftGrid n t) atTop (𝓝 t) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hc := (tendsto_nat_ceil_mul_div_atTop ht.le).comp hn
  have hi := tendsto_inv_atTop_zero.comp hn
  have hlim := hc.sub hi
  simp only [sub_zero] at hlim
  apply hlim.congr
  intro n
  have hp : 1 ≤ ⌈t * (n + 1)⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
  simp only [Function.comp_apply, leftGrid, Nat.cast_sub hp, Nat.cast_one,
    sub_div, one_div]

theorem tendsto_leftGrid_nhdsLT (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => leftGrid n t) atTop (𝓝[<] t) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_leftGrid t ht)
    (Eventually.of_forall (fun n => leftGrid_lt n t ht))

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]

/-- A strictly past adapted sample, with a fixed value on nonpositive times. -/
def pastStep (X : ℝ → Ω → E) (e : E) (n : ℕ) (p : Ω × (ℝ × ℝ)) : E :=
  if 0 < p.2.1 then X (leftGrid n p.2.1) p.1 else e

theorem measurableSet_positive (F : Filtration ℝ mΩ) :
    MeasurableSet[predictable F] {p : Ω × (ℝ × ℝ) | 0 < p.2.1} := by
  have he : {p : Ω × (ℝ × ℝ) | 0 < p.2.1} =
      ⋃ k : ℕ, rectangle univ 0 k univ := by
    ext p
    simp only [mem_setOf_eq, mem_iUnion, rectangle, mem_prod, mem_univ,
      true_and, and_true, mem_Ioc]
    constructor
    · intro hp
      obtain ⟨k, hk⟩ := exists_nat_gt p.2.1
      exact ⟨k, hp, hk.le⟩
    · rintro ⟨k, hk, _⟩
      exact hk
  rw [he]
  exact MeasurableSet.iUnion (fun k => measurableSet_predictable_rectangle
    F 0 k le_rfl univ MeasurableSet.univ univ MeasurableSet.univ)

/-- Grid-step measurability uses only adaptedness at nonnegative times. -/
theorem measurable_pastStep (F : Filtration ℝ mΩ) (X : ℝ → Ω → E)
    (hX : ∀ s, 0 ≤ s → Measurable[F s] (X s)) (e : E) (n : ℕ) :
    Measurable[predictable F] (pastStep X e n) := by
  classical
  letI : MeasurableSpace (Ω × (ℝ × ℝ)) := predictable F
  intro A hA
  have he : (pastStep X e n) ⁻¹' A =
      (⋃ k : ℕ, rectangle ((X ((k : ℝ) / (n + 1))) ⁻¹' A)
        ((k : ℝ) / (n + 1)) ((k + 1 : ℕ) / (n + 1)) univ) ∪
      (if e ∈ A then {p : Ω × (ℝ × ℝ) | 0 < p.2.1}ᶜ else ∅) := by
    ext p
    by_cases hp : 0 < p.2.1
    · have hbad : p ∉ (if e ∈ A then {p : Ω × (ℝ × ℝ) | 0 < p.2.1}ᶜ else ∅) := by
        split_ifs <;> simp [hp]
      simp only [mem_preimage, pastStep, hp, ↓reduceIte, mem_union, mem_iUnion,
        rectangle, mem_prod, mem_univ, and_true, mem_compl_iff, mem_setOf_eq,
        not_true_eq_false, ite_self, mem_empty_iff_false, hbad, or_false]
      constructor
      · intro h
        refine ⟨⌈p.2.1 * (n + 1)⌉₊ - 1, h, ?_⟩
        have hc := leftGrid_cell n p.2.1 hp
        simpa only [leftGrid, Nat.cast_add, Nat.cast_one, add_div] using hc
      · rintro ⟨k, hk, ht⟩
        rwa [leftGrid_eq_of_mem_cell n k p.2.1 ht]
    · simp only [mem_preimage, pastStep, hp, ↓reduceIte, mem_union, mem_iUnion,
        rectangle, mem_prod, mem_univ, and_true, mem_compl_iff, mem_setOf_eq,
        not_false_eq_true]
      have hz : ¬ ∃ k : ℕ, X ((k : ℝ) / (n + 1)) p.1 ∈ A ∧
          p.2.1 ∈ Ioc ((k : ℝ) / (n + 1)) ((k + 1 : ℕ) / (n + 1)) := by
        rintro ⟨k, _, ht⟩
        exact hp ((by positivity : (0 : ℝ) ≤ k / (n + 1)).trans_lt ht.1)
      simp only [hz, false_or]
      split_ifs <;> simp_all
  rw [he]
  apply MeasurableSet.union
  · exact MeasurableSet.iUnion (fun k => measurableSet_predictable_rectangle
      F _ _ (by positivity) _ (hX _ (by positivity) hA) _ MeasurableSet.univ)
  · split_ifs
    · exact (measurableSet_positive F).compl
    · exact MeasurableSet.empty

section Limits
variable [TopologicalSpace E] [PseudoMetrizableSpace E] [BorelSpace E]

/-- A pathwise left-limit target of adapted processes is predictable on
positive times. Neither adaptedness nor measurability of the target is assumed. -/
theorem measurable_leftLimit (F : Filtration ℝ mΩ) (X L : ℝ → Ω → E)
    (hX : ∀ s, 0 ≤ s → Measurable[F s] (X s)) (e : E)
    (hL : ∀ ω t, 0 < t → Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 (L t ω))) :
    Measurable[predictable F]
      (fun p : Ω × (ℝ × ℝ) => if 0 < p.2.1 then L p.2.1 p.1 else e) := by
  letI : MeasurableSpace (Ω × (ℝ × ℝ)) := predictable F
  apply measurable_of_tendsto_metrizable (fun n => measurable_pastStep F X hX e n)
  apply tendsto_pi_nhds.mpr
  intro p
  by_cases hp : 0 < p.2.1
  · simpa only [pastStep, hp, ↓reduceIte] using
      (hL p.1 p.2.1 hp).comp (tendsto_leftGrid_nhdsLT p.2.1 hp)
  · simp only [pastStep, hp, ↓reduceIte]
    exact tendsto_const_nhds

/-- Every left-continuous adapted process is predictable on positive times. -/
theorem measurable_of_leftContinuous (F : Filtration ℝ mΩ) (X : ℝ → Ω → E)
    (hX : ∀ s, 0 ≤ s → Measurable[F s] (X s)) (e : E)
    (hleft : ∀ ω t, 0 < t → ContinuousWithinAt (fun s => X s ω) (Iio t) t) :
    Measurable[predictable F]
      (fun p : Ω × (ℝ × ℝ) => if 0 < p.2.1 then X p.2.1 p.1 else e) :=
  measurable_leftLimit F X X hX e hleft

end Limits

section PredictableVersion
variable [TopologicalSpace E] [PolishSpace E] [BorelSpace E]

/-- A predictable candidate for the left limit, defined also on paths on
which the approximating sequence fails to converge. -/
def pastLimit (X : ℝ → Ω → E) (e : E) (ω : Ω) (t : ℝ) : E :=
  letI : Nonempty E := ⟨e⟩
  limUnder atTop (fun n : ℕ => if 0 < t then X (leftGrid n t) ω else e)

theorem measurable_pastLimit (F : Filtration ℝ mΩ) (X : ℝ → Ω → E)
    (hX : ∀ s, 0 ≤ s → Measurable[F s] (X s)) (e : E) :
    Measurable[predictable F]
      (fun p : Ω × (ℝ × ℝ) => pastLimit X e p.1 p.2.1) := by
  letI : MeasurableSpace (Ω × (ℝ × ℝ)) := predictable F
  letI : Nonempty E := ⟨e⟩
  exact (StronglyMeasurable.limUnder (l := atTop)
    (fun n => (measurable_pastStep F X hX e n).stronglyMeasurable)).measurable

omit mΩ [MeasurableSpace E] [BorelSpace E] in
theorem pastLimit_eq_of_tendsto (X : ℝ → Ω → E) (e : E) (ω : Ω)
    (t : ℝ) (ht : 0 < t) (y : E)
    (hy : Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 y)) :
    pastLimit X e ω t = y := by
  unfold pastLimit
  simp only [ht, ↓reduceIte]
  exact (hy.comp (tendsto_leftGrid_nhdsLT t ht)).limUnder_eq

omit mΩ [MeasurableSpace E] [BorelSpace E] in
/-- A locally constant left interval suffices to identify the predictable
version. This applies directly to finite-jump paths, without a limit axiom. -/
theorem pastLimit_eq_of_left_constant (X : ℝ → Ω → E) (e : E) (ω : Ω)
    (t : ℝ) (ht : 0 < t) (b : ℝ) (hb : b < t) (y : E)
    (hy : ∀ s ∈ Ico b t, X s ω = y) : pastLimit X e ω t = y := by
  apply pastLimit_eq_of_tendsto X e ω t ht y
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hb)] with s hs hbs
  exact (hy s ⟨hbs.le, hs⟩).symm

omit mΩ [MeasurableSpace E] [BorelSpace E] in
theorem pastLimit_nonpositive (X : ℝ → Ω → E) (e : E) (ω : Ω)
    (t : ℝ) (ht : t ≤ 0) : pastLimit X e ω t = e := by
  unfold pastLimit
  simp only [not_lt.mpr ht, ↓reduceIte]
  exact tendsto_const_nhds.limUnder_eq

end PredictableVersion

/-- The mark coordinate is observable in the predictable sigma algebra at
positive times; its value elsewhere is fixed. -/
def positiveHeight (p : Ω × (ℝ × ℝ)) : ℝ := if 0 < p.2.1 then p.2.2 else 0

theorem measurable_positiveHeight (F : Filtration ℝ mΩ) :
    Measurable[predictable F] (positiveHeight (Ω := Ω)) := by
  classical
  letI : MeasurableSpace (Ω × (ℝ × ℝ)) := predictable F
  intro B hB
  have he : positiveHeight ⁻¹' B =
      (⋃ k : ℕ, rectangle (univ : Set Ω) 0 k B) ∪
      (if 0 ∈ B then {p : Ω × (ℝ × ℝ) | 0 < p.2.1}ᶜ else ∅) := by
    ext p
    by_cases hp : 0 < p.2.1
    · have hbad : p ∉ (if 0 ∈ B then {p : Ω × (ℝ × ℝ) | 0 < p.2.1}ᶜ else ∅) := by
        split_ifs <;> simp [hp]
      simp only [mem_preimage, positiveHeight, hp, ↓reduceIte, mem_union, mem_iUnion,
        rectangle, mem_prod, mem_univ, true_and, hbad, or_false]
      constructor
      · intro h
        obtain ⟨k, hk⟩ := exists_nat_gt p.2.1
        exact ⟨k, ⟨hp, hk.le⟩, h⟩
      · rintro ⟨k, _, h⟩
        exact h
    · have hempty : ¬ ∃ k : ℕ, p.2.1 ∈ Ioc 0 (k : ℝ) ∧ p.2.2 ∈ B := by
        rintro ⟨k, ht, _⟩
        exact hp ht.1
      simp only [mem_preimage, positiveHeight, hp, ↓reduceIte, mem_union, mem_iUnion,
        rectangle, mem_prod, mem_univ, true_and, hempty, false_or]
      split_ifs <;> simp_all
  rw [he]
  apply MeasurableSet.union
  · exact MeasurableSet.iUnion (fun k => measurableSet_predictable_rectangle
      F 0 k le_rfl univ MeasurableSet.univ B hB)
  · split_ifs
    · exact (measurableSet_positive F).compl
    · exact MeasurableSet.empty

end CarryingCapacity.PredictableStepApproximation
