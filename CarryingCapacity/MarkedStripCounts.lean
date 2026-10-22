import CarryingCapacity.MarkedProducts

/-!
# Finite mark counts and the actual strip counting measure

The category count uses exactly the marks attached to arrivals before the
horizon. On the probability-one event of increasing, divergent clock arrivals,
it equals the category mass of the constructed sum of Dirac point measures.
This also identifies indicator products with powers of the actual count.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace CarryingCapacity.MarkedStripCounts
open CountableJumpProcess FrozenProcess PoissonIncrements MarkedNoise MarkedProducts
local instance : (P : Prop) → Decidable P := Classical.propDecidable

def prefixCount (B : Set ℝ) (n : ℕ) (u : ℕ → ℝ) : ℕ :=
  ∑ k ∈ Finset.range n, if u k ∈ B then 1 else 0

def clockCount (B : Set ℝ) (T : ℝ) (ω : StripSample) : ℕ :=
  prefixCount B (proposalCount ω.1 T) ω.2

theorem measurable_prefixCount (B : Set ℝ) (hB : MeasurableSet B) (n : ℕ) :
    Measurable (prefixCount B n) := by
  classical
  exact Finset.measurable_sum _ (fun k _ =>
    Measurable.ite (hB.preimage (measurable_pi_apply k)) measurable_const measurable_const)

theorem measurable_prefixCount_joint (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable (fun p : ℕ × (ℕ → ℝ) => prefixCount B p.1 p.2) := by
  have h : Measurable (fun p : (ℕ → ℝ) × ℕ => prefixCount B p.2 p.1) :=
    measurable_from_prod_countable (fun n => measurable_prefixCount B hB n)
  exact h.comp measurable_swap

theorem measurable_clockCount (B : Set ℝ) (hB : MeasurableSet B) (T : ℝ) :
    Measurable (clockCount B T) :=
  (measurable_prefixCount_joint B hB).comp
    (((measurable_proposalCount T).comp measurable_fst).prodMk measurable_snd)

theorem measurable_clockCount_joint (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable (fun p : StripSample × ℝ => clockCount B p.2 p.1) :=
  (measurable_prefixCount_joint B hB).comp
    ((measurable_joint_proposalCount.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
      measurable_fst.snd)

theorem prefixProduct_indicator_eq_pow (B : Set ℝ) (z : ℂ) (n : ℕ) (u : ℕ → ℝ) :
    prefixProduct (fun x => if x ∈ B then z else 1) n u = z ^ prefixCount B n u := by
  classical
  induction n with
  | zero => simp [prefixProduct, prefixCount]
  | succ n ih =>
    simp only [prefixProduct, prefixCount, Finset.prod_range_succ, Finset.sum_range_succ] at *
    by_cases h : u n ∈ B
    · simp [h, ih, pow_succ]
    · simp [h, ih]

theorem clockProduct_indicator_eq_pow (B : Set ℝ) (z : ℂ) (T : ℝ) (ω : StripSample) :
    clockProduct (fun x => if x ∈ B then z else 1) T ω = z ^ clockCount B T ω :=
  prefixProduct_indicator_eq_pow B z _ _

theorem prefixCount_union (A B : Set ℝ) (hAB : Disjoint A B) (n : ℕ) (u : ℕ → ℝ) :
    prefixCount (A ∪ B) n u = prefixCount A n u + prefixCount B n u := by
  simp only [prefixCount, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hnot : ¬(u k ∈ A ∧ u k ∈ B) := fun h => Set.disjoint_left.mp hAB h.1 h.2
  by_cases hA : u k ∈ A <;> by_cases hB : u k ∈ B <;> simp_all

/-- A finite disjoint partition adds exactly at the level of natural counts. -/
theorem prefixCount_finset_iUnion {I : Type*} (B : I → Set ℝ) (s : Finset I)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (B i) (B j))
    (n : ℕ) (u : ℕ → ℝ) :
    prefixCount (⋃ i ∈ s, B i) n u = ∑ i ∈ s, prefixCount (B i) n u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [prefixCount]
  | @insert a s ha ih =>
    have had : Disjoint (B a) (⋃ i ∈ s, B i) := by
      apply Set.disjoint_iUnion_right.mpr
      intro i
      apply Set.disjoint_iUnion_right.mpr
      intro hi
      exact hdis a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))
    have hs : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (B i) (B j) :=
      fun i hi j hj hij => hdis i (Finset.mem_insert_of_mem hi)
        j (Finset.mem_insert_of_mem hj) hij
    simpa only [Finset.set_biUnion_insert, Finset.sum_insert ha,
      prefixCount_union _ _ had] using congrArg (prefixCount (B a) n u + ·) (ih hs)

theorem clockCount_finset_iUnion {I : Type*} (B : I → Set ℝ) (s : Finset I)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (B i) (B j))
    (T : ℝ) (ω : StripSample) :
    clockCount (⋃ i ∈ s, B i) T ω = ∑ i ∈ s, clockCount (B i) T ω :=
  prefixCount_finset_iUnion B s hdis _ _

def windowCount (B : Set ℝ) (S T : ℝ) (ω : StripSample) : ℕ :=
  clockCount B T ω - clockCount B S ω

theorem measurable_windowCount (B : Set ℝ) (hB : MeasurableSet B) (S T : ℝ) :
    Measurable (windowCount B S T) :=
  (measurable_clockCount B hB T).sub (measurable_clockCount B hB S)

/-- A strip's genuine random point measure, with its actual vertical translation. -/
def stripMeasure (n : ℕ) (ω : StripSample) : Measure (ℝ × ℝ) :=
  Measure.sum (fun k : ℕ =>
    Measure.dirac (arrival ω.1 (k + 1), (n : ℝ) + ω.2 k))

theorem measurable_stripMeasure (n : ℕ) : Measurable (stripMeasure n) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [stripMeasure, Measure.sum_apply _ hs]
  apply Measurable.ennreal_tsum
  intro k
  exact (Measure.measurable_coe hs).comp (Measure.measurable_dirac.comp
    (((measurable_arrival (k + 1)).comp measurable_fst).prodMk
      (measurable_const.add ((measurable_pi_apply k).comp measurable_snd))))

theorem arrival_le_iff_lt_proposalCount {ω : ClockSpace}
    (hmono : StrictMono (arrival ω)) (hdiv : Tendsto (arrival ω) atTop atTop)
    (T : ℝ) (hT : 0 ≤ T) (k : ℕ) :
    arrival ω (k + 1) ≤ T ↔ k < proposalCount ω T := by
  have hb := (proposalCount_eq_iff hmono hdiv T hT (proposalCount ω T)).mp rfl
  constructor
  · intro hk
    by_contra h
    have hh := hmono.monotone (Nat.add_le_add_right (Nat.le_of_not_gt h) 1)
    exact (not_le_of_gt hb.2) (hh.trans hk)
  · intro hk
    exact (hmono.monotone (by omega)).trans hb.1

/-- Pathwise identification, valid for every measurable category on a good clock. -/
theorem stripMeasure_rectangle {ω : StripSample}
    (hmono : StrictMono (arrival ω.1)) (hdiv : Tendsto (arrival ω.1) atTop atTop)
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T) (B : Set ℝ) (hB : MeasurableSet B) :
    stripMeasure n ω (Iic T ×ˢ B) =
      (clockCount ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B) T ω : ℝ≥0∞) := by
  classical
  rw [stripMeasure, Measure.sum_apply _ (measurableSet_Iic.prod hB)]
  simp only [Measure.dirac_apply' _ (measurableSet_Iic.prod hB), Set.indicator_apply,
    Set.mem_prod, Set.mem_Iic, Pi.one_apply,
    arrival_le_iff_lt_proposalCount hmono hdiv T hT]
  rw [tsum_eq_sum (s := Finset.range (proposalCount ω.1 T)) (fun k hk => by
    simp only [Finset.mem_range] at hk
    simp [hk])]
  simp only [clockCount, prefixCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [Finset.mem_range.mp hk]

/-- Time-window counts are differences of finite prefix counts on the same clock. -/
theorem stripMeasure_window_rectangle {ω : StripSample}
    (hmono : StrictMono (arrival ω.1)) (hdiv : Tendsto (arrival ω.1) atTop atTop)
    (n : ℕ) (S T : ℝ) (hS : 0 ≤ S) (hST : S ≤ T)
    (B : Set ℝ) (hB : MeasurableSet B) :
    stripMeasure n ω (Ioc S T ×ˢ B) =
      (windowCount ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B) S T ω : ℝ≥0∞) := by
  have heq : Ioc S T ×ˢ B = (Iic T ×ˢ B) \ (Iic S ×ˢ B) := by
    ext p
    simp only [Set.mem_prod, Set.mem_Ioc, Set.mem_diff, Set.mem_Iic]
    constructor
    · rintro ⟨⟨h1, h2⟩, hB⟩
      exact ⟨⟨h2, hB⟩, fun h => (not_le_of_gt h1) h.1⟩
    · rintro ⟨⟨h2, hB⟩, h⟩
      exact ⟨⟨lt_of_not_ge (fun h1 => h ⟨h1, hB⟩), h2⟩, hB⟩
  have hsub : Iic S ×ˢ B ⊆ Iic T ×ˢ B :=
    fun _ h => ⟨h.1.trans hST, h.2⟩
  have hfin : stripMeasure n ω (Iic S ×ˢ B) ≠ ∞ := by
    rw [stripMeasure_rectangle hmono hdiv n S hS B hB]
    exact ENNReal.natCast_ne_top _
  rw [heq, measure_diff hsub (measurableSet_Iic.prod hB).nullMeasurableSet hfin,
    stripMeasure_rectangle hmono hdiv n T (hS.trans hST) B hB,
    stripMeasure_rectangle hmono hdiv n S hS B hB, windowCount, ENNReal.natCast_sub]

theorem strip_ae_increasing_divergent : ∀ᵐ ω ∂stripLaw,
    StrictMono (arrival ω.1) ∧ Tendsto (arrival ω.1) atTop atTop := by
  have hd := ae_arrival_tendsto 1 (by norm_num)
  rw [← strip_clock_map] at hd
  filter_upwards [strip_ae_good, ae_of_ae_map measurable_fst.aemeasurable hd] with ω hg hd
  exact ⟨hg.1.1, hd⟩

/-- One null set suffices simultaneously for all horizons and categories. -/
theorem ae_stripMeasure_rectangle : ∀ᵐ ω ∂stripLaw,
    ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T → ∀ B : Set ℝ, MeasurableSet B →
      stripMeasure n ω (Iic T ×ˢ B) =
        (clockCount ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B) T ω : ℝ≥0∞) := by
  filter_upwards [strip_ae_increasing_divergent] with ω hω
  intro n T hT B hB
  exact stripMeasure_rectangle hω.1 hω.2 n T hT B hB

theorem ae_stripMeasure_window_rectangle : ∀ᵐ ω ∂stripLaw,
    ∀ n : ℕ, ∀ S T : ℝ, 0 ≤ S → S ≤ T → ∀ B : Set ℝ, MeasurableSet B →
      stripMeasure n ω (Ioc S T ×ˢ B) =
        (windowCount ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B) S T ω : ℝ≥0∞) := by
  filter_upwards [strip_ae_increasing_divergent] with ω hω
  intro n S T hS hST B hB
  exact stripMeasure_window_rectangle hω.1 hω.2 n S T hS hST B hB

theorem countingMeasure_eq_sum_strips {J : Type*} (j : J) (ω : MarkedNoise.Sample J) :
    countingMeasure j ω = Measure.sum (fun n => stripMeasure n (ω (j, n))) := by
  symm
  exact Measure.sum_sum _

/-- Each actual strip coordinate has the same finite-count identification. -/
theorem ae_coordinate_stripMeasure_rectangle {J : Type*} (j : J) (n : ℕ) :
    ∀ᵐ ω ∂law J, ∀ T : ℝ, 0 ≤ T → ∀ B : Set ℝ, MeasurableSet B →
      stripMeasure n (ω (j, n)) (Iic T ×ˢ B) =
        (clockCount ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B) T (ω (j, n)) : ℝ≥0∞) := by
  have h := ae_stripMeasure_rectangle
  rw [← strip_map J (j, n)] at h
  filter_upwards [ae_of_ae_map (measurable_pi_apply (j, n)).aemeasurable h] with ω hω
  exact hω n

/-- The original common counting measure is the sum of the identified strip counts. -/
theorem ae_countingMeasure_rectangle {J : Type*} (j : J) :
    ∀ᵐ ω ∂law J, ∀ T : ℝ, 0 ≤ T → ∀ B : Set ℝ, MeasurableSet B →
      countingMeasure j ω (Iic T ×ˢ B) =
        ∑' n : ℕ, (clockCount ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B)
          T (ω (j, n)) : ℝ≥0∞) := by
  have h := ae_all_iff.mpr (fun n : ℕ => ae_coordinate_stripMeasure_rectangle j n)
  filter_upwards [h] with ω hω
  intro T hT B hB
  rw [countingMeasure_eq_sum_strips, Measure.sum_apply _ (measurableSet_Iic.prod hB)]
  exact tsum_congr (fun n => hω n T hT B hB)

end CarryingCapacity.MarkedStripCounts
