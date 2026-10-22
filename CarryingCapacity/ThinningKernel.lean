import CarryingCapacity.FrozenProcess

/-!
# Exact thinning probabilities and generator normalization

A uniform proposal label and an independent uniform mark accept jump `j`
with probability `q_j / (card J * C)` when `C > 0` and `0 ≤ q_j ≤ C`.
The expected one-proposal increment
therefore equals the frozen generator divided by that clock rate. These are
identities for the actual mark law; a continuous-time compensator theorem is
still needed to identify the generator of the constructed process.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Classical

namespace CarryingCapacity.FrozenProcess

theorem uniformUnit_Iic {u : ℝ} (hu1 : u ≤ 1) :
    uniformUnit (Iic u) = ENNReal.ofReal u := by
  rw [uniformUnit, Measure.restrict_apply measurableSet_Iic]
  have heq : Iic u ∩ Icc (0 : ℝ) 1 = Icc 0 u := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨hxu, hx0, _⟩
      exact ⟨hx0, hxu⟩
    · rintro ⟨hx0, hxu⟩
      exact ⟨hxu, hx0, hxu.trans hu1⟩
  rw [heq, Real.volume_Icc, sub_zero]

variable {E J : Type*} [Fintype J] [Nonempty J]
  [MeasurableSpace J] [MeasurableSingletonClass J]

/-- Accepted labels form a finite discrete measurable space. -/
instance finiteOptionMeasurableSpace (J : Type*) [Fintype J] : MeasurableSpace (Option J) := ⊤

instance finiteOptionMeasurableSingletonClass : MeasurableSingletonClass (Option J) :=
  ⟨fun _ => trivial⟩

omit [Nonempty J] in
theorem measurable_thinningDecode (C : ℝ) (rate : J → E → ℝ) (x : E) :
    Measurable (thinningDecode C rate x) := by
  apply ((measurable_of_countable (some : J → Option J)).comp measurable_fst).ite
    (measurableSet_le (measurable_const.mul measurable_snd)
      ((measurable_of_countable (fun j => rate j x)).comp measurable_fst)) measurable_const

/-- Distribution of the actual accepted label, with `none` for rejection. -/
def acceptedLabelLaw (C : ℝ) (rate : J → E → ℝ) (x : E) : Measure (Option J) :=
  Measure.map (thinningDecode C rate x) (markLaw J)

instance acceptedLabelLaw_probability (C : ℝ) (rate : J → E → ℝ) (x : E) :
    IsProbabilityMeasure (acceptedLabelLaw C rate x) :=
  isProbabilityMeasure_map (measurable_thinningDecode C rate x).aemeasurable

/-- Exact acceptance probability, including repeated target states: labels,
rather than resulting states, are the distinct events being counted. -/
theorem acceptedLabelLaw_some {C : ℝ} (hC : 0 < C) (rate : J → E → ℝ) (x : E)
    (j : J) (hqC : rate j x ≤ C) :
    acceptedLabelLaw C rate x {some j} =
      (Fintype.card J : ℝ≥0∞)⁻¹ * ENNReal.ofReal (rate j x / C) := by
  rw [acceptedLabelLaw, Measure.map_apply (measurable_thinningDecode C rate x)
    (measurableSet_singleton _)]
  have heq : thinningDecode C rate x ⁻¹' {some j} = {j} ×ˢ Iic (rate j x / C) := by
    ext p
    rcases p with ⟨k, u⟩
    simp only [mem_preimage, mem_singleton_iff, mem_prod, mem_Iic, thinningDecode]
    by_cases h : C * u ≤ rate k x
    · simp only [h, ↓reduceIte, Option.some.injEq]
      constructor
      · intro hkj
        subst k
        exact ⟨rfl, (le_div_iff₀ hC).mpr (by nlinarith)⟩
      · exact fun h' => h'.1
    · simp only [h, ↓reduceIte]
      constructor
      · intro hn
        cases hn
      · rintro ⟨hkj, hu⟩
        subst k
        exact False.elim (h (by nlinarith [(le_div_iff₀ hC).mp hu]))
  rw [heq, markLaw, Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply,
    uniformUnit_Iic ((div_le_one hC).mpr hqC)]

theorem acceptedLabelLaw_real_some {C : ℝ} (hC : 0 < C) (rate : J → E → ℝ) (x : E)
    (j : J) (hq : 0 ≤ rate j x) (hqC : rate j x ≤ C) :
    (acceptedLabelLaw C rate x).real {some j} =
      (Fintype.card J : ℝ)⁻¹ * (rate j x / C) := by
  rw [measureReal_def, acceptedLabelLaw_some hC rate x j hqC,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (div_nonneg hq hC.le)]

/-- Every accepted label has its prescribed contribution to a one-step
expectation. Rejection contributes zero. -/
theorem integral_accepted_increment {C : ℝ} (hC : 0 < C) (rate : J → E → ℝ) (x : E)
    (hq : ∀ j, 0 ≤ rate j x) (hqC : ∀ j, rate j x ≤ C) (increment : J → ℝ) :
    (∫ o, o.elim 0 increment ∂acceptedLabelLaw C rate x) =
      ((Fintype.card J : ℝ) * C)⁻¹ * ∑ j, rate j x * increment j := by
  rw [integral_fintype _ Integrable.of_finite]
  simp only [univ_option, Finset.sum_insertNone, Option.elim_none,
    smul_zero, mul_zero, zero_add, Option.elim_some, smul_eq_mul]
  simp only [acceptedLabelLaw_real_some hC rate x _ (hq _) (hqC _),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [mul_inv_rev, div_eq_mul_inv]
  ring

variable [DecidableEq E]

omit [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J] [DecidableEq E] in
/-- Finitely many labels and active states always admit a strictly positive
finite rate bound. No global bound on the unfrozen rates is required. -/
theorem exists_positive_rate_bound (active : Finset E) (rate : J → E → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ active, ∀ j, rate j x ≤ C := by
  obtain ⟨b, hb⟩ := ((Finset.univ.product active).image
    (fun p : J × E => rate p.1 p.2)).finite_toSet.bddAbove
  refine ⟨max b 0 + 1, by positivity, ?_⟩
  intro x hx j
  have hr : rate j x ≤ b := hb (Finset.mem_image.mpr ⟨(j, x), by simp [hx], rfl⟩)
  linarith [le_max_left b 0]

/-- The frozen generator for a finite collection of possible jumps. -/
def frozenGenerator (active : Finset E) (jump : J → E → E)
    (rate : J → E → ℝ) (F : E → ℝ) (x : E) : ℝ :=
  if x ∈ active then ∑ j, rate j x * (F (jump j x) - F x) else 0

/-- Multiplying the mean mark increment by the proposal clock rate
`card(J) * C` gives exactly the frozen generator. -/
theorem clockRate_mul_integral_increment (active : Finset E) (jump : J → E → E)
    {C : ℝ} (hC : 0 < C) (rate : J → E → ℝ) (F : E → ℝ) (x : E)
    (hq : ∀ j, 0 ≤ rate j x) (hqC : ∀ j, rate j x ≤ C) :
    ((Fintype.card J : ℝ) * C) *
      (∫ m, F (Freezing.frozenStep active jump (thinningDecode C rate) x m) - F x
        ∂markLaw J) = frozenGenerator active jump rate F x := by
  by_cases hx : x ∈ active
  · have heq : (fun m => F (Freezing.frozenStep active jump (thinningDecode C rate) x m) - F x) =
        fun m => (thinningDecode C rate x m).elim 0 (fun j => F (jump j x) - F x) := by
      funext m
      simp only [Freezing.frozenStep, hx, ↓reduceIte]
      cases thinningDecode C rate x m <;> simp
    rw [heq, ← integral_map (measurable_thinningDecode C rate x).aemeasurable
      (measurable_of_countable (fun o : Option J => o.elim 0
        (fun j => F (jump j x) - F x))).aestronglyMeasurable]
    change _ * (∫ o, o.elim 0 (fun j => F (jump j x) - F x)
      ∂acceptedLabelLaw C rate x) = _
    rw [integral_accepted_increment hC rate x hq hqC, frozenGenerator, if_pos hx]
    have hn : (Fintype.card J : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card J ≠ 0)
    rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero hn (ne_of_gt hC)), one_mul]
  · simp [Freezing.frozenStep, hx, frozenGenerator]

end CarryingCapacity.FrozenProcess
