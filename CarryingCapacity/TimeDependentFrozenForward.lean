import CarryingCapacity.TimeDependentExpectation

/-!
# The actual finite active-state forward system

Singleton expectations of the constructed frozen process satisfy a finite
linear system. Its rows retain the full outgoing rate, including jumps leaving
the active set. Self-jumps cancel in the matrix definition. No forward equation
or continuity of the actual masses is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace CarryingCapacity.TimeDependentFrozenForward
open CommonInitialNoise TimeDependentInitial TimeDependentGeneratorIntegral

variable {E J : Type*} [DecidableEq E]

/-- Real singleton indicator, bounded between zero and one. -/
def atomTest (x y : E) : ℝ := if y = x then 1 else 0

theorem atomTest_nonneg (x y : E) : 0 ≤ atomTest x y := by
  unfold atomTest
  split_ifs <;> norm_num

theorem atomTest_le_one (x y : E) : atomTest x y ≤ 1 := by
  unfold atomTest
  split_ifs <;> norm_num

theorem sum_atomTest (G : Finset E) (y : E) :
    ∑ x ∈ G, atomTest x y = if y ∈ G then 1 else 0 := by
  simp [atomTest, Finset.sum_ite_eq']

/-- Source-to-target coefficient, with self-jump cancellation built in. -/
def matrixEntry [Fintype J] (jump : J → E → E) (rate : J → ℝ → E → ℝ)
    (t : ℝ) (y x : E) : ℝ :=
  ∑ j, rate j t y * (atomTest x (jump j y) - atomTest x y)

theorem matrixEntry_nonneg_of_ne [Fintype J] (jump : J → E → E)
    (rate : J → ℝ → E → ℝ) (t : ℝ) (y x : E) (hne : y ≠ x)
    (hq : ∀ j, 0 ≤ rate j t y) : 0 ≤ matrixEntry jump rate t y x := by
  apply Finset.sum_nonneg
  intro j _
  simpa only [atomTest, if_neg hne, sub_zero] using
    mul_nonneg (hq j) (atomTest_nonneg x (jump j y))

/-- Loss from the active system is exactly the rate of jumps leaving it. -/
theorem sum_matrixEntry [Fintype J] (G : Finset E) (jump : J → E → E)
    (rate : J → ℝ → E → ℝ) (t : ℝ) (y : E) (hy : y ∈ G) :
    ∑ x ∈ G, matrixEntry jump rate t y x =
      -∑ j, if jump j y ∈ G then 0 else rate j t y := by
  unfold matrixEntry
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_atomTest, if_pos hy]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

/-- The active rows are sub-conservative, including exits from the active set. -/
theorem sum_matrixEntry_nonpos [Fintype J] (G : Finset E) (jump : J → E → E)
    (rate : J → ℝ → E → ℝ) (t : ℝ) (y : E) (hy : y ∈ G)
    (hq : ∀ j, 0 ≤ rate j t y) : ∑ x ∈ G, matrixEntry jump rate t y x ≤ 0 := by
  rw [sum_matrixEntry G jump rate t y hy]
  apply neg_nonpos.mpr
  exact Finset.sum_nonneg (fun j _ => by
    split_ifs
    · exact le_rfl
    · exact hq j)

/-- A uniform finite-rate cap bounds every matrix entry, including the diagonal. -/
theorem norm_matrixEntry_le [Fintype J] (jump : J → E → E)
    (rate : J → ℝ → E → ℝ) (C t : ℝ) (y x : E)
    (hq : ∀ j, 0 ≤ rate j t y) (hb : ∀ j, rate j t y ≤ C) :
    ‖matrixEntry jump rate t y x‖ ≤ Fintype.card J * C := by
  calc
    _ ≤ ∑ j, ‖rate j t y * (atomTest x (jump j y) - atomTest x y)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : J, C := by
      apply Finset.sum_le_sum
      intro j _
      have hdiff : ‖atomTest x (jump j y) - atomTest x y‖ ≤ 1 := by
        unfold atomTest
        split_ifs <;> norm_num
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hq j)]
      exact (mul_le_mul_of_nonneg_left hdiff (hq j)).trans (by simpa using hb j)
    _ = _ := by simp

/-- Finite active-state expansion holds at every state, including frozen exits. -/
theorem generator_atom_eq_sum [Fintype J] (G : Finset E) (jump : J → E → E)
    (rate : J → ℝ → E → ℝ) (t : ℝ) (x z : E) :
    frozenGenerator G jump rate (atomTest x) t z =
      ∑ y ∈ G, atomTest y z * matrixEntry jump rate t y x := by
  simp only [frozenGenerator, FrozenProcess.frozenGenerator, matrixEntry]
  by_cases hz : z ∈ G <;> simp [atomTest, hz, Finset.sum_ite_eq']

section Probability
variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  [MeasurableSingletonClass E] (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The real expectation is exactly the genuine event probability. -/
theorem integral_atomTest_eq_measureReal (Z : Ω → E) (hZ : Measurable Z) (x : E) :
    (∫ ω, atomTest x (Z ω) ∂μ) = μ.real (Z ⁻¹' {x}) := by
  have hf : (fun ω => atomTest x (Z ω)) = (Z ⁻¹' {x}).indicator 1 := by
    funext ω
    simp [atomTest, Set.indicator_apply]
  rw [hf, integral_indicator_one (hZ (measurableSet_singleton x))]

theorem integrable_atomTest (Z : Ω → E) (hZ : Measurable Z) (x : E) :
    Integrable (fun ω => atomTest x (Z ω)) μ := by
  have hm : Measurable (fun ω => atomTest x (Z ω)) :=
    measurable_const.ite (hZ (measurableSet_singleton x)) measurable_const
  exact ⟨hm.aestronglyMeasurable, hasFiniteIntegral_of_bounded
    (Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (atomTest_nonneg x (Z ω))]
      exact atomTest_le_one x (Z ω)))⟩

omit [MeasurableSpace E] [MeasurableSingletonClass E] [IsProbabilityMeasure μ] in
theorem integral_atomTest_nonneg (Z : Ω → E) (x : E) :
    0 ≤ ∫ ω, atomTest x (Z ω) ∂μ :=
  integral_nonneg (fun ω => atomTest_nonneg x (Z ω))

theorem integral_atomTest_le_one (Z : Ω → E) (hZ : Measurable Z) (x : E) :
    (∫ ω, atomTest x (Z ω) ∂μ) ≤ 1 := by
  calc
    _ ≤ ∫ _ : Ω, (1 : ℝ) ∂μ :=
      integral_mono (integrable_atomTest μ Z hZ x) (integrable_const 1)
        (fun ω => atomTest_le_one x (Z ω))
    _ = 1 := by simp

/-- Integrating the finite expansion produces actual mass-weighted coefficients. -/
theorem integral_generator_atom [Fintype J] (G : Finset E) (jump : J → E → E)
    (rate : J → ℝ → E → ℝ) (Z : Ω → E) (hZ : Measurable Z) (t : ℝ) (x : E) :
    (∫ ω, frozenGenerator G jump rate (atomTest x) t (Z ω) ∂μ) =
      ∑ y ∈ G, (∫ ω, atomTest y (Z ω) ∂μ) * matrixEntry jump rate t y x := by
  simp_rw [generator_atom_eq_sum]
  rw [integral_finset_sum _ (fun y _ =>
    (integrable_atomTest μ Z hZ y).mul_const (matrixEntry jump rate t y x))]
  simp_rw [integral_mul_const]

end Probability

section Process
variable {A : Type*} [MeasurableSpace A] [Fintype J]
  [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  (active : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)
  (initial : A → E) (μ : Measure A) [IsProbabilityMeasure μ]

/-- Singleton probability of the actual frozen path, expressed as a real expectation. -/
def mass (C t : ℝ) (x : E) : ℝ :=
  ∫ p, atomTest x (process active jump rate initial C p t) ∂law μ J

omit [Fintype J] [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [IsProbabilityMeasure μ] in
theorem mass_nonneg (C t : ℝ) (x : E) :
    0 ≤ mass active jump rate initial μ C t x :=
  integral_atomTest_nonneg (law μ J) _ x

theorem mass_le_one (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C t : ℝ) (x : E) :
    mass active jump rate initial μ C t x ≤ 1 :=
  integral_atomTest_le_one (law μ J) _
    ((measurable_process active jump rate initial hRate hinit C).comp
      (measurable_id.prodMk measurable_const)) x

omit [IsProbabilityMeasure μ] in
/-- The constructed singleton mass is the probability of its actual state event. -/
theorem mass_eq_measureReal (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C t : ℝ) (x : E) :
    mass active jump rate initial μ C t x =
      (law μ J).real {p | process active jump rate initial C p t = x} :=
  integral_atomTest_eq_measureReal (law μ J) _
    ((measurable_process active jump rate initial hRate hinit C).comp
      (measurable_id.prodMk measurable_const)) x

/-- Any finite collection of distinct singleton masses has total at most one. -/
theorem sum_mass_le_one (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C t : ℝ) (G : Finset E) :
    ∑ x ∈ G, mass active jump rate initial μ C t x ≤ 1 := by
  have hm := (measurable_process active jump rate initial hRate hinit C).comp
    (measurable_id.prodMk (measurable_const (a := t)))
  have hi (x : E) := integrable_atomTest (law μ J)
    (fun p => process active jump rate initial C p t) hm x
  unfold mass
  rw [← integral_finset_sum G (fun x _ => hi x)]
  calc
    _ ≤ ∫ _p : Sample A J, (1 : ℝ) ∂law μ J := by
      apply integral_mono (integrable_finset_sum G (fun x _ => hi x)) (integrable_const 1)
      intro p
      change (∑ x ∈ G, atomTest x (process active jump rate initial C p t)) ≤ 1
      rw [sum_atomTest]
      split_ifs <;> norm_num
    _ = 1 := by simp

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E] in
theorem mass_zero (C : ℝ) (x : E) :
    mass active jump rate initial μ C 0 x = ∫ a, atomTest x (initial a) ∂μ := by
  unfold mass
  calc
    _ = ∫ p : Sample A J, atomTest x (initial p.1) ∂law μ J := by
      apply integral_congr_ae
      filter_upwards [ae_process_zero active jump rate initial μ] with p hp
      rw [hp C]
    _ = _ := by
      simpa only [measureReal_univ_eq_one, one_smul] using
        (integral_fun_fst (μ := μ) (ν := MarkedNoise.law J) (fun a => atomTest x (initial a)))

theorem expectedGenerator_eq_sum (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C t : ℝ) (x : E) :
    TimeDependentExpectation.expectedGenerator active jump rate initial μ C (atomTest x) t =
      ∑ y ∈ active, mass active jump rate initial μ C t y * matrixEntry jump rate t y x :=
  integral_generator_atom (law μ J) active jump rate _
    ((measurable_process active jump rate initial hRate hinit C).comp
      (measurable_id.prodMk measurable_const)) t x

variable [TopologicalSpace E] [PolishSpace E] [BorelSpace E]

/-- The finite system is derived from actual Dynkin and Fubini, not postulated. -/
theorem mass_forward (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e x : E) (t : ℝ)
    (hq : ∀ y ∈ active, ∀ j s, 0 ≤ s → 0 ≤ rate j s y)
    (hbound : ∀ y ∈ active, ∀ j s, 0 ≤ s → rate j s y ≤ C) :
    mass active jump rate initial μ C t x = (∫ a, atomTest x (initial a) ∂μ) +
      ∫ s in Ioc 0 t, ∑ y ∈ active,
        mass active jump rate initial μ C s y * matrixEntry jump rate s y x := by
  have h := TimeDependentExpectation.expectation_eq_initial_add_integral
    active jump rate initial μ hRate hinit C e (atomTest x) t hq hbound
      (integrable_atomTest μ initial hinit x)
  simpa only [expectedGenerator_eq_sum active jump rate initial μ hRate hinit C] using h

/-- The actual frozen masses are Lipschitz, hence continuous, on nonnegative times. -/
theorem continuousOn_mass (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (e x : E)
    (hq : ∀ y ∈ active, ∀ j s, 0 ≤ s → 0 ≤ rate j s y)
    (hbound : ∀ y ∈ active, ∀ j s, 0 ≤ s → rate j s y ≤ C) :
    ContinuousOn (fun t => mass active jump rate initial μ C t x) (Ici 0) :=
  TimeDependentExpectation.continuousOn_expectation active jump rate initial μ hRate hinit
    C e (atomTest x) hq hbound (integrable_atomTest μ initial hinit x)

omit [TopologicalSpace E] [PolishSpace E] [BorelSpace E] in
/-- The finite-system right side is genuinely integrable on bounded intervals. -/
theorem intervalIntegrable_mass_system (hRate : ∀ j x, Measurable (fun t => rate j t x))
    (hinit : Measurable initial) (C : ℝ) (x : E)
    (hq : ∀ y ∈ active, ∀ j s, 0 ≤ s → 0 ≤ rate j s y)
    (hbound : ∀ y ∈ active, ∀ j s, 0 ≤ s → rate j s y ≤ C)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun s => ∑ y ∈ active,
      mass active jump rate initial μ C s y * matrixEntry jump rate s y x) volume a b := by
  have he := funext (fun s => expectedGenerator_eq_sum active jump rate initial μ hRate hinit C s x)
  rw [← he]
  exact TimeDependentExpectation.intervalIntegrable_expectedGenerator active jump rate initial μ
    hRate hinit C (atomTest x) hq hbound a b ha hb

end Process
end CarryingCapacity.TimeDependentFrozenForward
