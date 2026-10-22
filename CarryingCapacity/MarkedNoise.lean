import CarryingCapacity.FrozenProcess
import CarryingCapacity.PoissonIncrements

/-!
# A common marked noise for all finite rate cutoffs

For each jump label and each unit vertical strip we construct an independent
unit-rate exponential clock with independent uniform marks. These define one
random counting measure on time and height for each label, on a single sample
space. Every bounded time-height rectangle contains only finitely many points
almost surely, simultaneously for all labels and real cutoffs. No compatibility
of separately chosen finite-rate clocks is assumed.

The Poisson increment law and compensation are separate proof obligations.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace CarryingCapacity.MarkedNoise
open CountableJumpProcess

abbrev StripSample := ClockSpace × (ℕ → ℝ)

def unitMarksLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => FrozenProcess.uniformUnit)

instance unitMarksLaw_probability : IsProbabilityMeasure unitMarksLaw := by
  unfold unitMarksLaw
  infer_instance

/-- A unit strip uses one unit-rate clock and an independent iid uniform sequence. -/
def stripLaw : Measure StripSample :=
  (waitingTimeLaw 1 (by norm_num)).prod unitMarksLaw

instance stripLaw_probability : IsProbabilityMeasure stripLaw := by
  unfold stripLaw
  infer_instance

theorem strip_clock_map : Measure.map Prod.fst stripLaw = waitingTimeLaw 1 (by norm_num) := by
  simp [stripLaw, Measure.map_fst_prod]

theorem strip_marks_map : Measure.map Prod.snd stripLaw = unitMarksLaw := by
  simp [stripLaw, Measure.map_snd_prod]

theorem unitMarks_coordinate_map (k : ℕ) :
    Measure.map (fun u : ℕ → ℝ => u k) unitMarksLaw = FrozenProcess.uniformUnit := by
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply k) hs]
  exact coordinate_event _ k s hs

theorem unitMarks_ae_range : ∀ᵐ u ∂unitMarksLaw, ∀ k, 0 ≤ u k ∧ u k ≤ 1 := by
  rw [ae_all_iff]
  intro k
  have h : ∀ᵐ x ∂FrozenProcess.uniformUnit, x ∈ Icc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Icc
  rw [← unitMarks_coordinate_map k] at h
  exact ae_of_ae_map (measurable_pi_apply k).aemeasurable h

/-- Clock local finiteness and mark bounds hold together under the constructed strip law. -/
theorem strip_ae_good : ∀ᵐ ω ∂stripLaw,
    (StrictMono (arrival ω.1) ∧ ∀ T : ℝ, {k : ℕ | arrival ω.1 k ≤ T}.Finite) ∧
      (∀ k, 0 ≤ ω.2 k ∧ ω.2 k ≤ 1) := by
  have hc := ae_locally_finite 1 (by norm_num)
  rw [← strip_clock_map] at hc
  have hm := unitMarks_ae_range
  rw [← strip_marks_map] at hm
  exact (ae_of_ae_map measurable_fst.aemeasurable hc).and
    (ae_of_ae_map measurable_snd.aemeasurable hm)

variable (J : Type*) [Countable J]

abbrev Sample := J × ℕ → StripSample

/-- One fixed probability law for all labels and all vertical strips. -/
def law : Measure (Sample J) := Measure.infinitePi (fun _ : J × ℕ => stripLaw)

instance law_probability : IsProbabilityMeasure (law J) := by
  unfold law
  infer_instance

omit [Countable J] in
theorem strip_map (i : J × ℕ) : Measure.map (fun ω : Sample J => ω i) (law J) = stripLaw := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  have heq : (fun ω : Sample J => ω i) ⁻¹' s = Set.pi ({i} : Finset (J × ℕ)) (fun _ => s) := by
    ext ω
    simp
  rw [heq, law, Measure.infinitePi_pi _ (fun _ _ => hs)]
  simp

omit [Countable J] in
/-- Independence of the full strip samples, including clocks and all marks. -/
theorem independent_strips : iIndepFun (fun i (ω : Sample J) => ω i) (law J) := by
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro I sets hs
  have heq : (⋂ i ∈ I, (fun ω : Sample J => ω i) ⁻¹' sets i) = Set.pi I sets := by
    ext ω
    simp
  rw [heq, law, Measure.infinitePi_pi _ hs]
  apply Finset.prod_congr rfl
  intro i hi
  calc
    stripLaw (sets i) = (Measure.map (fun ω : Sample J => ω i) (law J)) (sets i) :=
      congrArg (fun μ : Measure StripSample => μ (sets i)) (strip_map J i).symm
    _ = _ := Measure.map_apply (measurable_pi_apply i) (hs i hi)

/-- A single probability-one event controls every label and strip. -/
theorem ae_good : ∀ᵐ ω ∂law J, ∀ i : J × ℕ,
    (StrictMono (arrival (ω i).1) ∧ ∀ T : ℝ, {k : ℕ | arrival (ω i).1 k ≤ T}.Finite) ∧
      (∀ k, 0 ≤ (ω i).2 k ∧ (ω i).2 k ≤ 1) := by
  rw [ae_all_iff]
  intro i
  have h := strip_ae_good
  rw [← strip_map J i] at h
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h

variable {J}

/-- The k-th point in strip n has its actual arrival time and height n+U_k. -/
def point (j : J) (ω : Sample J) (p : ℕ × ℕ) : ℝ × ℝ :=
  (arrival (ω (j, p.1)).1 (p.2 + 1), (p.1 : ℝ) + (ω (j, p.1)).2 p.2)

omit [Countable J] in
theorem measurable_point (j : J) (p : ℕ × ℕ) : Measurable (fun ω : Sample J => point j ω p) :=
  ((measurable_arrival (p.2 + 1)).comp ((measurable_pi_apply (j, p.1)).fst)).prodMk
    (measurable_const.add ((measurable_pi_apply p.2).comp (measurable_pi_apply (j, p.1)).snd))

/-- One common random time-height counting measure for each jump label. -/
def countingMeasure (j : J) (ω : Sample J) : Measure (ℝ × ℝ) :=
  Measure.sum (fun p : ℕ × ℕ => Measure.dirac (point j ω p))

omit [Countable J] in
theorem measurable_countingMeasure (j : J) : Measurable (countingMeasure j : Sample J → _) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [countingMeasure, Measure.sum_apply _ hs]
  apply Measurable.ennreal_tsum
  intro p
  exact (Measure.measurable_coe hs).comp
    (Measure.measurable_dirac.comp (measurable_point j p))

omit [Countable J] in
theorem countingMeasure_eq_map (j : J) (ω : Sample J) :
    countingMeasure j ω = Measure.map (point j ω) Measure.count := by
  rw [Measure.count, Measure.map_sum (measurable_of_countable _).aemeasurable]
  simp only [Measure.map_dirac (measurable_of_countable _)]
  rfl

omit [Countable J] in
/-- Finite vertical cutoff uses only finitely many strips, and each strip
contains finitely many arrivals before any bounded horizon. -/
theorem finite_points_in_box (j : J) (ω : Sample J)
    (hclock : ∀ n, ∀ T : ℝ, {k : ℕ | arrival (ω (j, n)).1 k ≤ T}.Finite)
    (hmark : ∀ n k, 0 ≤ (ω (j, n)).2 k) (T C : ℝ) :
    {p : ℕ × ℕ | point j ω p ∈ Iic T ×ˢ Iic C}.Finite := by
  have hf (n : ℕ) : {k : ℕ | arrival (ω (j, n)).1 (k + 1) ≤ T}.Finite :=
    Set.Finite.preimage (f := fun k : ℕ => k + 1)
      (fun _ _ _ _ h => Nat.succ_injective h) (hclock n T)
  have hset : {p : ℕ × ℕ | point j ω p ∈ Iic T ×ˢ Iic C} ⊆
      ⋃ n ∈ Iic (Nat.ceil C), (fun k : ℕ => (n, k)) ''
        {k : ℕ | arrival (ω (j, n)).1 (k + 1) ≤ T} := by
    rintro ⟨n, k⟩ hp
    have hn : (n : ℝ) ≤ C := by
      have hm := hmark n k
      have hh := hp.2
      change (n : ℝ) + (ω (j, n)).2 k ≤ C at hh
      linarith
    have hnc : n ≤ Nat.ceil C := by exact_mod_cast hn.trans (Nat.le_ceil C)
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hnc, mem_image_of_mem _ hp.1⟩⟩
  exact ((Set.finite_Iic (Nat.ceil C)).biUnion (fun n _ => (hf n).image _)).subset hset

/-- The same noise is locally finite for all real time and height cutoffs. -/
theorem ae_locally_finite_boxes : ∀ᵐ ω ∂law J, ∀ j : J, ∀ T C : ℝ,
    countingMeasure j ω (Iic T ×ˢ Iic C) < ∞ := by
  filter_upwards [ae_good J] with ω hω
  intro j T C
  rw [countingMeasure_eq_map,
    Measure.map_apply (measurable_of_countable _) (measurableSet_Iic.prod measurableSet_Iic),
    Measure.count_apply_lt_top]
  exact finite_points_in_box j ω (fun n => (hω (j, n)).1.2)
    (fun n k => ((hω (j, n)).2 k).1) T C

/-- With finitely many jump labels, the total proposal set in a bounded box
is finite as well. This is the event list needed by a finite system. -/
theorem ae_finite_total_points [Finite J] : ∀ᵐ ω ∂law J, ∀ T C : ℝ,
    {e : J × (ℕ × ℕ) | point e.1 ω e.2 ∈ Iic T ×ˢ Iic C}.Finite := by
  filter_upwards [ae_good J] with ω hω
  intro T C
  have hf (j : J) := finite_points_in_box j ω (fun n => (hω (j, n)).1.2)
    (fun n k => ((hω (j, n)).2 k).1) T C
  have heq : {e : J × (ℕ × ℕ) | point e.1 ω e.2 ∈ Iic T ×ˢ Iic C} =
      ⋃ j : J, (fun p : ℕ × ℕ => (j, p)) '' {p | point j ω p ∈ Iic T ×ˢ Iic C} := by
    ext e
    constructor
    · intro he
      exact mem_iUnion.mpr ⟨e.1, mem_image_of_mem _ he⟩
    · intro he
      obtain ⟨j, p, hp, heq⟩ := mem_iUnion.mp he
      rcases heq with rfl
      exact hp
  rw [heq]
  exact Set.finite_iUnion (fun j => (hf j).image _)

/-- Every atom lies at positive time and nonnegative height. -/
theorem ae_positive_points : ∀ᵐ ω ∂law J, ∀ j : J, ∀ p : ℕ × ℕ,
    0 < (point j ω p).1 ∧ 0 ≤ (point j ω p).2 := by
  filter_upwards [ae_good J] with ω hω
  intro j p
  constructor
  · have h := (hω (j, p.1)).1.1 (Nat.succ_pos p.2)
    simpa [point, arrival_zero] using h
  · exact add_nonneg (Nat.cast_nonneg _) (((hω (j, p.1)).2 p.2).1)

omit [Countable J] in
theorem arrival_map (i : J × ℕ) (k : ℕ) :
    Measure.map (fun ω : Sample J => arrival (ω i).1 (k + 1)) (law J) =
      Measure.map (fun w : ClockSpace => arrival w (k + 1)) (waitingTimeLaw 1 (by norm_num)) := by
  calc
    _ = Measure.map (fun w : ClockSpace => arrival w (k + 1))
        (Measure.map Prod.fst (Measure.map (fun ω : Sample J => ω i) (law J))) := by
      rw [Measure.map_map measurable_fst (measurable_pi_apply i),
        Measure.map_map (measurable_arrival (k + 1)) (measurable_fst.comp (measurable_pi_apply i))]
      rfl
    _ = _ := by rw [strip_map, strip_clock_map]

omit [Countable J] in
/-- Independent strips have no coincident arrivals at any two fixed indices. -/
theorem ae_arrivals_ne (i j : J × ℕ) (hij : i ≠ j) (k l : ℕ) :
    ∀ᵐ ω ∂law J, arrival (ω i).1 (k + 1) ≠ arrival (ω j).1 (l + 1) := by
  let f : Sample J → ℝ := fun ω => arrival (ω i).1 (k + 1)
  let g : Sample J → ℝ := fun ω => arrival (ω j).1 (l + 1)
  have hf : Measurable f := (measurable_arrival _).comp (measurable_pi_apply i).fst
  have hg : Measurable g := (measurable_arrival _).comp (measurable_pi_apply j).fst
  have hind : IndepFun f g (law J) :=
    ((independent_strips J).indepFun hij).comp
      ((measurable_arrival _).comp measurable_fst) ((measurable_arrival _).comp measurable_fst)
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).mp hind
  letI : NoAtoms (Measure.map g (law J)) := by
    change NoAtoms (Measure.map (fun ω : Sample J => arrival (ω j).1 (l + 1)) (law J))
    rw [arrival_map]
    exact PoissonIncrements.arrival_noAtoms 1 (by norm_num) l
  have hs : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hz : ((Measure.map f (law J)).prod (Measure.map g (law J)))
      {p : ℝ × ℝ | p.1 = p.2} = 0 := by
    apply Measure.measure_prod_null_of_ae_null hs
    apply Filter.Eventually.of_forall
    intro a
    have heq : Prod.mk a ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {a} := by
      ext b
      simp [eq_comm]
    change (Measure.map g (law J)) (Prod.mk a ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 0
    rw [heq]
    exact measure_singleton a
  rw [ae_iff]
  change law J {ω | ¬f ω ≠ g ω} = 0
  simp only [not_not]
  change law J ((fun ω => (f ω, g ω)) ⁻¹' {p : ℝ × ℝ | p.1 = p.2}) = 0
  rw [← Measure.map_apply (hf.prodMk hg) hs, hmap]
  exact hz

/-- The full countable event family has no simultaneous arrivals almost surely. -/
theorem ae_distinct_event_times : ∀ᵐ ω ∂law J, Function.Injective
    (fun e : J × (ℕ × ℕ) => (point e.1 ω e.2).1) := by
  have hsep : ∀ᵐ ω ∂law J, ∀ i j : J × ℕ, ∀ k l : ℕ,
      i ≠ j → arrival (ω i).1 (k + 1) ≠ arrival (ω j).1 (l + 1) := by
    simp only [ae_all_iff]
    intro i j k l hij
    exact ae_arrivals_ne i j hij k l
  filter_upwards [ae_good J, hsep] with ω hω hsep
  rintro ⟨j, n, k⟩ ⟨j', n', k'⟩ heq
  change arrival (ω (j, n)).1 (k + 1) = arrival (ω (j', n')).1 (k' + 1) at heq
  have hp : (j, n) = (j', n') := by
    by_cases h : (j, n) = (j', n')
    · exact h
    · exact False.elim (hsep (j, n) (j', n') k k' h heq)
  have hj := congrArg Prod.fst hp
  have hn := congrArg Prod.snd hp
  dsimp at hj hn
  subst j'
  subst n'
  have hk := (hω (j, n)).1.1.injective heq
  have hkk : k = k' := Nat.succ_injective hk
  subst k'
  rfl

end CarryingCapacity.MarkedNoise
