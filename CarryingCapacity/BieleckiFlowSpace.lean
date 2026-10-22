import CarryingCapacity.LyapunovFlowSpace

/-!
# The Bielecki metric on the manuscript's law-curve space

The distance is the actual supremum of exponentially weighted adapted
Wasserstein distances. Its metric axioms and two-sided comparison with the
uniform metric are proved. A uniform equivalence then transfers the previously
proved completeness of the closed Lyapunov curve space.

The final fixed-point theorem is conditional on a supplied invariant evolution
map and its genuine Volterra inequality. The kernel integration and contraction
factor are proved here; construction of the stochastic evolution map is not.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal Topology

namespace CarryingCapacity.BieleckiFlowSpace
open LyapunovFlowSpace

variable {D : ℕ} {κ : MomentScale} {Ψ : State D → ℝ} {ν : MomentLaw κ D}
  {C T : ℝ} {hT : 0 ≤ T}

/-- The exact weighted supremum in the manuscript. Nonnegative `lam` also
includes the uniform metric at `lam = 0`. -/
def weightedDistance (lam : ℝ≥0) (v w : ManuscriptCurves Ψ ν C T hT) : ℝ :=
  sSup (Set.range (fun t : Set.Icc (0 : ℝ) T =>
    Real.exp (-(lam : ℝ) * t.val) * wasserstein (v.val t) (w.val t)))

theorem weight_le_one (lam : ℝ≥0) (t : Set.Icc (0 : ℝ) T) :
    Real.exp (-(lam : ℝ) * t.val) ≤ 1 :=
  Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr lam.property) t.property.1)

theorem weighted_range_nonempty (lam : ℝ≥0) (v w : ManuscriptCurves Ψ ν C T hT) :
    (Set.range (fun t : Set.Icc (0 : ℝ) T =>
      Real.exp (-(lam : ℝ) * t.val) * wasserstein (v.val t) (w.val t))).Nonempty :=
  ⟨_, ⟨⟨0, le_rfl, hT⟩, rfl⟩⟩

theorem weighted_range_bddAbove (lam : ℝ≥0) (v w : ManuscriptCurves Ψ ν C T hT) :
    BddAbove (Set.range (fun t : Set.Icc (0 : ℝ) T =>
      Real.exp (-(lam : ℝ) * t.val) * wasserstein (v.val t) (w.val t))) := by
  refine ⟨dist v w, ?_⟩
  rintro _ ⟨t, rfl⟩
  calc
    _ ≤ 1 * wasserstein (v.val t) (w.val t) :=
      mul_le_mul_of_nonneg_right (weight_le_one lam t) (wasserstein_nonneg _ _)
    _ ≤ dist v w := by simpa using wasserstein_eval_le_dist v w t

/-- Each actual weighted pointwise transport distance lies below its supremum. -/
theorem weighted_eval_le (lam : ℝ≥0) (v w : ManuscriptCurves Ψ ν C T hT)
    (t : Set.Icc (0 : ℝ) T) :
    Real.exp (-(lam : ℝ) * t.val) * wasserstein (v.val t) (w.val t) ≤
      weightedDistance lam v w :=
  le_csSup (weighted_range_bddAbove lam v w) ⟨t, rfl⟩

theorem weightedDistance_nonneg (lam : ℝ≥0) (v w : ManuscriptCurves Ψ ν C T hT) :
    0 ≤ weightedDistance lam v w :=
  (mul_nonneg (Real.exp_pos _).le (wasserstein_nonneg _ _)).trans
    (weighted_eval_le lam v w ⟨0, le_rfl, hT⟩)

/-- The Bielecki distance never exceeds the uniform transport distance. -/
theorem weightedDistance_le_uniform (lam : ℝ≥0) (v w : ManuscriptCurves Ψ ν C T hT) :
    weightedDistance lam v w ≤ dist v w := by
  apply csSup_le (weighted_range_nonempty lam v w)
  rintro _ ⟨t, rfl⟩
  calc
    _ ≤ 1 * wasserstein (v.val t) (w.val t) :=
      mul_le_mul_of_nonneg_right (weight_le_one lam t) (wasserstein_nonneg _ _)
    _ ≤ dist v w := by simpa using wasserstein_eval_le_dist v w t

/-- The reverse uniform bound is finite on every compact time interval. -/
theorem uniform_le_weightedDistance (lam : ℝ≥0) (v w : ManuscriptCurves Ψ ν C T hT) :
    dist v w ≤ Real.exp ((lam : ℝ) * T) * weightedDistance lam v w := by
  change dist v.val w.val ≤ _
  apply (ContinuousMap.dist_le (mul_nonneg (Real.exp_pos _).le
    (weightedDistance_nonneg lam v w))).mpr
  intro t
  have he := weighted_eval_le lam v w t
  have h := mul_le_mul_of_nonneg_left he (Real.exp_pos ((lam : ℝ) * t.val)).le
  have hexp : Real.exp ((lam : ℝ) * t.val) * Real.exp (-(lam : ℝ) * t.val) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  calc
    dist (v.val t) (w.val t) = Real.exp ((lam : ℝ) * t.val) *
        (Real.exp (-(lam : ℝ) * t.val) * wasserstein (v.val t) (w.val t)) := by
      rw [← mul_assoc, hexp, one_mul, momentLaw_dist]
    _ ≤ Real.exp ((lam : ℝ) * t.val) * weightedDistance lam v w := h
    _ ≤ Real.exp ((lam : ℝ) * T) * weightedDistance lam v w :=
      mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left t.property.2 lam.property))
        (weightedDistance_nonneg lam v w)

/-- The paper's exact two-sided comparison of the weighted and uniform metrics. -/
theorem weightedDistance_bounds (lam : ℝ≥0) (v w : ManuscriptCurves Ψ ν C T hT) :
    Real.exp (-(lam : ℝ) * T) * dist v w ≤ weightedDistance lam v w ∧
      weightedDistance lam v w ≤ dist v w := by
  refine ⟨?_, weightedDistance_le_uniform lam v w⟩
  have h := mul_le_mul_of_nonneg_left (uniform_le_weightedDistance lam v w)
    (Real.exp_pos (-(lam : ℝ) * T)).le
  have he : Real.exp (-(lam : ℝ) * T) * Real.exp ((lam : ℝ) * T) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  simpa only [← mul_assoc, he, one_mul] using h

@[simp] theorem weightedDistance_self (lam : ℝ≥0) (v : ManuscriptCurves Ψ ν C T hT) :
    weightedDistance lam v v = 0 :=
  le_antisymm (by simpa only [dist_self] using weightedDistance_le_uniform lam v v)
    (weightedDistance_nonneg lam v v)

theorem weightedDistance_comm (lam : ℝ≥0) (v w : ManuscriptCurves Ψ ν C T hT) :
    weightedDistance lam v w = weightedDistance lam w v := by
  simp only [weightedDistance, wasserstein_symm]

theorem weightedDistance_triangle (lam : ℝ≥0) (v w z : ManuscriptCurves Ψ ν C T hT) :
    weightedDistance lam v z ≤ weightedDistance lam v w + weightedDistance lam w z := by
  apply csSup_le (weighted_range_nonempty lam v z)
  rintro _ ⟨t, rfl⟩
  calc
    _ ≤ Real.exp (-(lam : ℝ) * t.val) *
        (wasserstein (v.val t) (w.val t) + wasserstein (w.val t) (z.val t)) :=
      mul_le_mul_of_nonneg_left (wasserstein_triangle _ _ _) (Real.exp_pos _).le
    _ = _ + _ := mul_add _ _ _
    _ ≤ _ := add_le_add (weighted_eval_le lam v w t) (weighted_eval_le lam w z t)

theorem weightedDistance_eq_zero_iff (lam : ℝ≥0) (v w : ManuscriptCurves Ψ ν C T hT) :
    weightedDistance lam v w = 0 ↔ v = w := by
  constructor
  · intro h
    have hh := uniform_le_weightedDistance lam v w
    rw [h, mul_zero] at hh
    exact dist_eq_zero.mp (le_antisymm hh dist_nonneg)
  · rintro rfl
    exact weightedDistance_self lam v

/-- A type wrapper equips the same actual curves with the Bielecki metric
without replacing the uniform metric instance on the original curve space. -/
@[ext] structure BieleckiCurves (Ψ : State D → ℝ) (ν : MomentLaw κ D)
    (C T : ℝ) (hT : 0 ≤ T) (lam : ℝ≥0) where
  toCurve : ManuscriptCurves Ψ ν C T hT

instance (lam : ℝ≥0) : MetricSpace (BieleckiCurves Ψ ν C T hT lam) where
  dist v w := weightedDistance lam v.toCurve w.toCurve
  dist_self v := weightedDistance_self lam v.toCurve
  dist_comm v w := weightedDistance_comm lam v.toCurve w.toCurve
  dist_triangle v w z := weightedDistance_triangle lam v.toCurve w.toCurve z.toCurve
  eq_of_dist_eq_zero h := BieleckiCurves.ext ((weightedDistance_eq_zero_iff lam _ _).mp h)

@[simp] theorem bielecki_dist (lam : ℝ≥0) (v w : BieleckiCurves Ψ ν C T hT lam) :
    dist v w = weightedDistance lam v.toCurve w.toCurve := rfl

/-- The identity on underlying curves is Lipschitz from uniform to weighted distance. -/
theorem lipschitz_mk (lam : ℝ≥0) : LipschitzWith 1
    (BieleckiCurves.mk : ManuscriptCurves Ψ ν C T hT → BieleckiCurves Ψ ν C T hT lam) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simpa only [NNReal.coe_one, one_mul, bielecki_dist] using weightedDistance_le_uniform lam v w

/-- The reverse identity is Lipschitz with the explicit factor `exp (lam T)`. -/
theorem lipschitz_toCurve (lam : ℝ≥0) : LipschitzWith (Real.toNNReal (Real.exp ((lam : ℝ) * T)))
    (BieleckiCurves.toCurve : BieleckiCurves Ψ ν C T hT lam → ManuscriptCurves Ψ ν C T hT) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simpa only [Real.coe_toNNReal _ (Real.exp_pos _).le, bielecki_dist] using
    uniform_le_weightedDistance lam v.toCurve w.toCurve

/-- The actual Bielecki and uniform curve spaces are uniformly equivalent. -/
def uniformEquiv (lam : ℝ≥0) :
    BieleckiCurves Ψ ν C T hT lam ≃ᵤ ManuscriptCurves Ψ ν C T hT where
  toFun := BieleckiCurves.toCurve
  invFun := BieleckiCurves.mk
  left_inv _ := rfl
  right_inv _ := rfl
  uniformContinuous_toFun := (lipschitz_toCurve lam).uniformContinuous
  uniformContinuous_invFun := (lipschitz_mk lam).uniformContinuous

/-- Completeness is derived from the proved closed Lyapunov curve-space
completeness and the explicit two-sided metric comparison. -/
instance bieleckiCurvesCompleteSpace (lam : ℝ≥0) :
    CompleteSpace (BieleckiCurves Ψ ν C T hT lam) :=
  (uniformEquiv lam).completeSpace_iff.mpr inferInstance

/-- The same original finite Lyapunov moment assumptions supply nonemptiness. -/
theorem bieleckiCurves_nonempty (lam : ℝ≥0) (hΨ : ∀ x, 0 ≤ Ψ x)
    (hν : Integrable Ψ ν.measure) (hC : 0 ≤ C) :
    Nonempty (BieleckiCurves Ψ ν C T hT lam) := by
  obtain ⟨v⟩ := manuscriptCurves_nonempty hΨ ν hν hC hT
  exact ⟨⟨v⟩⟩

/-- A continuous extension is used only to write ordinary interval integrals.
On `[0,T]` it is the original curve; outside it is held at the nearest endpoint. -/
def extendedCurve (v : ManuscriptCurves Ψ ν C T hT) : ℝ → MomentLaw κ D :=
  fun s => v.val (Set.projIcc 0 T hT s)

theorem continuous_extendedCurve (v : ManuscriptCurves Ψ ν C T hT) :
    Continuous (extendedCurve v) := v.val.continuous.comp continuous_projIcc

@[simp] theorem extendedCurve_on_interval (v : ManuscriptCurves Ψ ν C T hT)
    (t : Set.Icc (0 : ℝ) T) : extendedCurve v t.val = v.val t := by
  simp only [extendedCurve, Set.projIcc_val]

/-- The decaying Volterra kernel has the required finite integral. -/
theorem integral_decay_kernel {b t : ℝ} (hb : 0 < b) :
    (∫ s in (0 : ℝ)..t, Real.exp (-b * (t - s))) =
      (1 - Real.exp (-b * t)) / b := by
  have hderiv (s : ℝ) : HasDerivAt (fun y => Real.exp (-b * (t - y)) / b)
      (Real.exp (-b * (t - s))) s := by
    convert ((((hasDerivAt_const s t).sub (hasDerivAt_id s)).const_mul (-b)).exp.div_const b)
      using 1
    field_simp
  have hi : IntervalIntegrable (fun s => Real.exp (-b * (t - s))) volume 0 t :=
    (by fun_prop : Continuous (fun s : ℝ => Real.exp (-b * (t - s)))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) hi]
  simp only [sub_self, mul_zero, Real.exp_zero, sub_zero]
  ring

/-- The pointwise Volterra bound yields the exact Bielecki contraction
coefficient, with all interval integrability supplied by continuity. -/
theorem weighted_volterra_bound (lam : ℝ≥0) {A : ℝ} (hA : 0 ≤ A)
    (hAlam : A < (lam : ℝ)) (v w : ManuscriptCurves Ψ ν C T hT)
    (t : Set.Icc (0 : ℝ) T) :
    Real.exp (-(lam : ℝ) * t.val) *
      (A * ∫ s in (0 : ℝ)..t.val, Real.exp (A * (t.val - s)) *
        wasserstein (extendedCurve v s) (extendedCurve w s)) ≤
      (A / ((lam : ℝ) - A)) * weightedDistance lam v w := by
  let d := weightedDistance lam v w
  let b := (lam : ℝ) - A
  have hb : 0 < b := sub_pos.mpr hAlam
  have hd : 0 ≤ d := weightedDistance_nonneg lam v w
  have hc : Continuous (fun s : ℝ =>
      wasserstein (extendedCurve v s) (extendedCurve w s)) :=
    (continuous_extendedCurve v).dist (continuous_extendedCurve w)
  have hcexp : Continuous (fun s : ℝ => Real.exp (A * (t.val - s))) := by fun_prop
  have hf : Continuous (fun s : ℝ => Real.exp (-(lam : ℝ) * t.val) *
      (Real.exp (A * (t.val - s)) *
        wasserstein (extendedCurve v s) (extendedCurve w s))) :=
    continuous_const.mul (hcexp.mul hc)
  have hg : Continuous (fun s : ℝ => Real.exp (-b * (t.val - s)) * d) := by fun_prop
  have hpoint (s : ℝ) (hs : s ∈ Set.Icc 0 t.val) :
      Real.exp (-(lam : ℝ) * t.val) * (Real.exp (A * (t.val - s)) *
        wasserstein (extendedCurve v s) (extendedCurve w s)) ≤
      Real.exp (-b * (t.val - s)) * d := by
    let s' : Set.Icc (0 : ℝ) T := ⟨s, hs.1, hs.2.trans t.property.2⟩
    have hsval : extendedCurve v s = v.val s' := extendedCurve_on_interval v s'
    have hsval' : extendedCurve w s = w.val s' := extendedCurve_on_interval w s'
    have he : Real.exp (-(lam : ℝ) * t.val) * Real.exp (A * (t.val - s)) =
        Real.exp (-b * (t.val - s)) * Real.exp (-(lam : ℝ) * s) := by
      simp only [← Real.exp_add]
      congr 1
      dsimp [b]
      ring
    rw [← mul_assoc, he, mul_assoc, hsval, hsval']
    exact mul_le_mul_of_nonneg_left (weighted_eval_le lam v w s') (Real.exp_pos _).le
  have hint := intervalIntegral.integral_mono_on (μ := volume) t.property.1
    (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _) hpoint
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
    integral_decay_kernel hb] at hint
  have hkernel : (1 - Real.exp (-b * t.val)) / b ≤ 1 / b :=
    (div_le_div_iff_of_pos_right hb).mpr (by linarith [Real.exp_pos (-b * t.val)])
  have hbound := hint.trans (mul_le_mul_of_nonneg_right hkernel hd)
  have hscaled := mul_le_mul_of_nonneg_left hbound hA
  change Real.exp (-(lam : ℝ) * t.val) * (A * _) ≤ (A / b) * d
  convert hscaled using 1 <;> ring

/-- A supplied invariant evolution map satisfying the genuine integral
estimate from the manuscript is Lipschitz in the derived Bielecki metric. -/
theorem lipschitz_of_volterra (lam : ℝ≥0) {A : ℝ} (hA : 0 ≤ A)
    (hAlam : A < (lam : ℝ))
    (F : BieleckiCurves Ψ ν C T hT lam → BieleckiCurves Ψ ν C T hT lam)
    (hF : ∀ v w (t : Set.Icc (0 : ℝ) T),
      wasserstein ((F v).toCurve.val t) ((F w).toCurve.val t) ≤
        A * ∫ s in (0 : ℝ)..t.val, Real.exp (A * (t.val - s)) *
          wasserstein (extendedCurve v.toCurve s) (extendedCurve w.toCurve s)) :
    LipschitzWith (Real.toNNReal (A / ((lam : ℝ) - A))) F := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [Real.coe_toNNReal _ (div_nonneg hA (sub_pos.mpr hAlam).le)]
  change weightedDistance lam (F v).toCurve (F w).toCurve ≤
    (A / ((lam : ℝ) - A)) * weightedDistance lam v.toCurve w.toCurve
  apply csSup_le (weighted_range_nonempty lam (F v).toCurve (F w).toCurve)
  rintro _ ⟨t, rfl⟩
  exact (mul_le_mul_of_nonneg_left (hF v w t) (Real.exp_pos _).le).trans
    (weighted_volterra_bound lam hA hAlam v.toCurve w.toCurve t)

/-- Conditional Banach conclusion: an independently constructed invariant map
with the manuscript's Volterra estimate has one fixed point when `lam > 2*A`.
This theorem does not construct that evolution map or prove its stochastic
estimate. Nonemptiness and completeness are derived from the original moment
assumptions and the metric results above. -/
theorem existsUnique_fixedPoint_of_volterra (lam : ℝ≥0) (hΨ : ∀ x, 0 ≤ Ψ x)
    (hν : Integrable Ψ ν.measure) (hC : 0 ≤ C) {A : ℝ} (hA : 0 ≤ A)
    (hAlam : 2 * A < (lam : ℝ))
    (F : BieleckiCurves Ψ ν C T hT lam → BieleckiCurves Ψ ν C T hT lam)
    (hF : ∀ v w (t : Set.Icc (0 : ℝ) T),
      wasserstein ((F v).toCurve.val t) ((F w).toCurve.val t) ≤
        A * ∫ s in (0 : ℝ)..t.val, Real.exp (A * (t.val - s)) *
          wasserstein (extendedCurve v.toCurve s) (extendedCurve w.toCurve s)) :
    ∃! v, F v = v := by
  letI : Nonempty (BieleckiCurves Ψ ν C T hT lam) :=
    bieleckiCurves_nonempty lam hΨ hν hC
  have hAlam' : A < (lam : ℝ) := by linarith
  have hratio : A / ((lam : ℝ) - A) < 1 := by
    apply (div_lt_one (sub_pos.mpr hAlam')).mpr
    linarith
  have hcontract : ContractingWith (Real.toNNReal (A / ((lam : ℝ) - A))) F := by
    refine ⟨?_, lipschitz_of_volterra lam hA hAlam' F hF⟩
    apply NNReal.coe_lt_coe.mp
    rwa [Real.coe_toNNReal _ (div_nonneg hA (sub_pos.mpr hAlam').le), NNReal.coe_one]
  exact ⟨hcontract.fixedPoint F, hcontract.fixedPoint_isFixedPt,
    fun v hv => hcontract.fixedPoint_unique hv⟩

end CarryingCapacity.BieleckiFlowSpace
