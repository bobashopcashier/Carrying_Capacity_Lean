import CarryingCapacity.TransportCompleteness

/-!
# Closed Lyapunov sublevels and complete spaces of law curves

The Lyapunov functional is a genuine nonnegative extended integral. Its lower
semicontinuity follows from continuous atom probabilities and a countable sum.
Finite bounds imply integrability, so the equivalent real integral bounds do
not use the zero value assigned to a nonintegrable Bochner integral.

This constructs the complete invariant candidate space from the manuscript's
nonlinear fixed-point argument. It does not construct a nonlinear flow or
assert that a stochastic evolution preserves this space.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace CarryingCapacity.LyapunovFlowSpace

variable {D : ℕ} {κ : MomentScale}

/-- The genuine extended Lyapunov moment; for nonnegative `Ψ`, this also
records infinite moments without totalizing them to zero. -/
def lyapunovIntegral (Ψ : State D → ℝ) (μ : MomentLaw κ D) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Ψ x) ∂μ.measure

/-- Atom probabilities are continuous for the actual adapted transport metric. -/
theorem continuous_atom_mass (x : State D) :
    Continuous (fun μ : MomentLaw κ D => μ.measure {x}) := by
  have h := ENNReal.continuous_ofReal.comp
    (event_probability_lipschitz (κ := κ) {x}).continuous
  convert h using 1
  funext μ
  letI : IsProbabilityMeasure μ.measure := μ.probability
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

/-- Nonnegative Lyapunov moments are lower semicontinuous in `Wκ`, with no
growth or integrability assumption on the Lyapunov function. -/
theorem lowerSemicontinuous_lyapunovIntegral (Ψ : State D → ℝ) :
    LowerSemicontinuous (lyapunovIntegral (κ := κ) Ψ) := by
  have h (x : State D) : LowerSemicontinuous
      (fun μ : MomentLaw κ D => ENNReal.ofReal (Ψ x) * μ.measure {x}) :=
    ((ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
      (continuous_atom_mass x)).lowerSemicontinuous
  change LowerSemicontinuous (fun μ : MomentLaw κ D =>
    ∫⁻ x, ENNReal.ofReal (Ψ x) ∂μ.measure)
  simp_rw [lintegral_countable']
  exact lowerSemicontinuous_tsum h

/-- Every finite extended-moment bound entails genuine Bochner integrability. -/
theorem integrable_of_lyapunovIntegral_le {Ψ : State D → ℝ}
    (hΨ : ∀ x, 0 ≤ Ψ x) {μ : MomentLaw κ D} {C : ℝ}
    (h : lyapunovIntegral Ψ μ ≤ ENNReal.ofReal C) : Integrable Ψ μ.measure := by
  refine ⟨(measurable_of_countable Ψ).aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hΨ)).mpr
    (lt_of_le_of_lt h ENNReal.ofReal_lt_top)

/-- At a nonnegative finite bound the extended constraint is exactly the
ordinary Lyapunov constraint, including the necessary integrability clause. -/
theorem lyapunovIntegral_le_iff {Ψ : State D → ℝ} (hΨ : ∀ x, 0 ≤ Ψ x)
    (μ : MomentLaw κ D) {C : ℝ} (hC : 0 ≤ C) :
    lyapunovIntegral Ψ μ ≤ ENNReal.ofReal C ↔
      Integrable Ψ μ.measure ∧ (∫ x, Ψ x ∂μ.measure) ≤ C := by
  constructor
  · intro h
    have hi := integrable_of_lyapunovIntegral_le hΨ h
    refine ⟨hi, ?_⟩
    apply (ENNReal.ofReal_le_ofReal_iff hC).mp
    rwa [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hΨ)]
  · rintro ⟨hi, h⟩
    rw [lyapunovIntegral, ← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall hΨ)]
    exact ENNReal.ofReal_le_ofReal h

/-- Closedness is proved from lower semicontinuity, not supplied as a field. -/
theorem isClosed_lyapunovSublevel (Ψ : State D → ℝ) (C : ℝ≥0∞) :
    IsClosed {μ : MomentLaw κ D | lyapunovIntegral Ψ μ ≤ C} :=
  (lowerSemicontinuous_lyapunovIntegral Ψ).isClosed_preimage C

/-- The formulation in terms of an ordinary integral has the same closedness,
provided integrability is included rather than silently assumed. -/
theorem isClosed_integralSublevel {Ψ : State D → ℝ} (hΨ : ∀ x, 0 ≤ Ψ x)
    {C : ℝ} (hC : 0 ≤ C) :
    IsClosed {μ : MomentLaw κ D |
      Integrable Ψ μ.measure ∧ (∫ x, Ψ x ∂μ.measure) ≤ C} := by
  simpa only [lyapunovIntegral_le_iff hΨ _ hC] using
    isClosed_lyapunovSublevel (κ := κ) Ψ (ENNReal.ofReal C)

/-- A fixed finite Lyapunov sublevel in the genuine adapted transport space. -/
def LyapunovSublevel (κ : MomentScale) (Ψ : State D → ℝ) (C : ℝ) :=
  {μ : MomentLaw κ D // lyapunovIntegral Ψ μ ≤ ENNReal.ofReal C}

instance (Ψ : State D → ℝ) (C : ℝ) : MetricSpace (LyapunovSublevel κ Ψ C) :=
  inferInstanceAs (MetricSpace {μ : MomentLaw κ D //
    lyapunovIntegral Ψ μ ≤ ENNReal.ofReal C})

/-- Actual completeness, inherited from the proved transport completeness and
the proved closedness of the sublevel. -/
instance lyapunovSublevelCompleteSpace (Ψ : State D → ℝ) (C : ℝ) :
    CompleteSpace (LyapunovSublevel κ Ψ C) :=
  (isClosed_lyapunovSublevel Ψ (ENNReal.ofReal C)).completeSpace_coe

section Curves

variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

/-- The candidate invariant set of continuous law curves with a prescribed
initial law and continuous Lyapunov envelope. -/
def curveSet (Ψ : State D → ℝ) (t₀ : T) (ν : MomentLaw κ D) (B : C(T, ℝ)) :
    Set C(T, MomentLaw κ D) :=
  {v | v t₀ = ν ∧ ∀ t, lyapunovIntegral Ψ (v t) ≤ ENNReal.ofReal (B t)}

omit [CompactSpace T] in
/-- Both the initial condition and every pointwise Lyapunov bound are closed
for the uniform adapted transport topology on continuous curves. -/
theorem isClosed_curveSet (Ψ : State D → ℝ) (t₀ : T) (ν : MomentLaw κ D)
    (B : C(T, ℝ)) : IsClosed (curveSet Ψ t₀ ν B) := by
  have h₀ : IsClosed {v : C(T, MomentLaw κ D) | v t₀ = ν} :=
    isClosed_eq (continuous_eval_const t₀) continuous_const
  have ht (t : T) : IsClosed {v : C(T, MomentLaw κ D) |
      lyapunovIntegral Ψ (v t) ≤ ENNReal.ofReal (B t)} :=
    (isClosed_lyapunovSublevel Ψ (ENNReal.ofReal (B t))).preimage
      (continuous_eval_const t)
  have hbound : IsClosed {v : C(T, MomentLaw κ D) |
      ∀ t, lyapunovIntegral Ψ (v t) ≤ ENNReal.ofReal (B t)} := by
    simpa only [Set.setOf_forall] using isClosed_iInter ht
  exact h₀.inter hbound

/-- The space used for the nonlinear fixed-point argument. This definition
does not contain any assumption asserting closedness or completeness. -/
def LyapunovCurves (Ψ : State D → ℝ) (t₀ : T) (ν : MomentLaw κ D) (B : C(T, ℝ)) :=
  ↥(curveSet Ψ t₀ ν B)

instance (Ψ : State D → ℝ) (t₀ : T) (ν : MomentLaw κ D) (B : C(T, ℝ)) :
    MetricSpace (LyapunovCurves Ψ t₀ ν B) :=
  inferInstanceAs (MetricSpace ↥(curveSet Ψ t₀ ν B))

/-- The uniform metric on the candidate invariant curve space is complete. -/
instance lyapunovCurvesCompleteSpace (Ψ : State D → ℝ) (t₀ : T)
    (ν : MomentLaw κ D) (B : C(T, ℝ)) : CompleteSpace (LyapunovCurves Ψ t₀ ν B) :=
  (isClosed_curveSet Ψ t₀ ν B).completeSpace_coe

omit [CompactSpace T] in
/-- Every curve in this space has the required initial law. -/
theorem curve_initial {Ψ : State D → ℝ} {t₀ : T} {ν : MomentLaw κ D}
    {B : C(T, ℝ)} (v : LyapunovCurves Ψ t₀ ν B) : v.val t₀ = ν :=
  v.property.1

omit [CompactSpace T] in
/-- Finite envelope bounds imply actual integrability at every time. -/
theorem curve_integrable {Ψ : State D → ℝ} (hΨ : ∀ x, 0 ≤ Ψ x)
    {t₀ : T} {ν : MomentLaw κ D} {B : C(T, ℝ)}
    (v : LyapunovCurves Ψ t₀ ν B) (t : T) : Integrable Ψ (v.val t).measure :=
  integrable_of_lyapunovIntegral_le hΨ (v.property.2 t)

omit [CompactSpace T] in
/-- The extended-moment formulation gives precisely the real integral bound
required by the manuscript, with integrability separately proved above. -/
theorem curve_integral_le {Ψ : State D → ℝ} (hΨ : ∀ x, 0 ≤ Ψ x)
    {t₀ : T} {ν : MomentLaw κ D} {B : C(T, ℝ)} (hB : ∀ t, 0 ≤ B t)
    (v : LyapunovCurves Ψ t₀ ν B) (t : T) :
    (∫ x, Ψ x ∂(v.val t).measure) ≤ B t :=
  ((lyapunovIntegral_le_iff hΨ (v.val t) (hB t)).mp (v.property.2 t)).2

/-- Uniform distance between candidate curves bounds their transport distance
at each time. -/
theorem wasserstein_eval_le_dist {Ψ : State D → ℝ} {t₀ : T}
    {ν : MomentLaw κ D} {B : C(T, ℝ)} (v w : LyapunovCurves Ψ t₀ ν B) (t : T) :
    wasserstein (v.val t) (w.val t) ≤ dist v w := by
  change dist (v.val t) (w.val t) ≤ dist v.val w.val
  exact ContinuousMap.dist_apply_le_dist t

omit [CompactSpace T] in
/-- If the envelope dominates the initial moment, the constant curve proves
that the complete candidate space is nonempty. -/
theorem nonempty_lyapunovCurves {Ψ : State D → ℝ} {t₀ : T}
    {ν : MomentLaw κ D} {B : C(T, ℝ)}
    (h : ∀ t, lyapunovIntegral Ψ ν ≤ ENNReal.ofReal (B t)) :
    Nonempty (LyapunovCurves Ψ t₀ ν B) :=
  ⟨⟨ContinuousMap.const T ν, rfl, h⟩⟩

end Curves

/-- The manuscript's Lyapunov envelope, with initial Lyapunov moment `m`
and drift constant `C`. -/
def exponentialEnvelope (m C : ℝ) : C(ℝ, ℝ) where
  toFun t := (m + 1 / 2) * Real.exp (2 * C * t) - 1 / 2
  continuous_toFun := by fun_prop

@[simp] theorem exponentialEnvelope_zero (m C : ℝ) :
    exponentialEnvelope m C 0 = m := by
  simp [exponentialEnvelope]

/-- For nonnegative drift constants and times, the envelope dominates its
initial moment. This proves that the constant initial-law curve is admissible. -/
theorem le_exponentialEnvelope {m C t : ℝ} (hm : 0 ≤ m) (hC : 0 ≤ C)
    (ht : 0 ≤ t) : m ≤ exponentialEnvelope m C t := by
  have he : 1 ≤ Real.exp (2 * C * t) :=
    Real.one_le_exp_iff.mpr (by positivity)
  change m ≤ (m + 1 / 2) * Real.exp (2 * C * t) - 1 / 2
  nlinarith

/-- Restrict the continuous manuscript envelope to the compact time interval. -/
def intervalEnvelope (m C T : ℝ) : C(Set.Icc (0 : ℝ) T, ℝ) :=
  (exponentialEnvelope m C).comp ⟨Subtype.val, continuous_subtype_val⟩

/-- The concrete space `𝔛_T` from the manuscript, equipped with the actual
uniform adapted transport metric inherited from continuous maps. -/
abbrev ManuscriptCurves (Ψ : State D → ℝ) (ν : MomentLaw κ D) (C T : ℝ)
    (hT : 0 ≤ T) :=
  LyapunovCurves Ψ (⟨0, le_rfl, hT⟩ : Set.Icc (0 : ℝ) T) ν
    (intervalEnvelope (∫ x, Ψ x ∂ν.measure) C T)

/-- The manuscript's curve space is complete for uniform adapted transport
distance, independently of any nonlinear process construction. -/
theorem manuscriptCurves_complete (Ψ : State D → ℝ) (ν : MomentLaw κ D)
    (C T : ℝ) (hT : 0 ≤ T) : CompleteSpace (ManuscriptCurves Ψ ν C T hT) :=
  inferInstance

/-- The manuscript's original finite-Lyapunov-moment assumption gives a
nonempty complete candidate space, via the actual constant curve. -/
theorem manuscriptCurves_nonempty {Ψ : State D → ℝ} (hΨ : ∀ x, 0 ≤ Ψ x)
    (ν : MomentLaw κ D) (hν : Integrable Ψ ν.measure) {C T : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) : Nonempty (ManuscriptCurves Ψ ν C T hT) := by
  apply nonempty_lyapunovCurves
  intro t
  have hm : 0 ≤ ∫ x, Ψ x ∂ν.measure := integral_nonneg hΨ
  change lyapunovIntegral Ψ ν ≤
    ENNReal.ofReal (exponentialEnvelope (∫ x, Ψ x ∂ν.measure) C t.val)
  rw [lyapunovIntegral, ← ofReal_integral_eq_lintegral_ofReal hν
    (Eventually.of_forall hΨ)]
  exact ENNReal.ofReal_le_ofReal (le_exponentialEnvelope hm hC t.property.1)

/-- Every admissible manuscript curve has a genuine finite Lyapunov moment
and satisfies its exponential moment bound at every time. -/
theorem manuscriptCurve_integrable_and_bound {Ψ : State D → ℝ}
    (hΨ : ∀ x, 0 ≤ Ψ x) {ν : MomentLaw κ D} {C T : ℝ} (hC : 0 ≤ C)
    {hT : 0 ≤ T} (v : ManuscriptCurves Ψ ν C T hT) (t : Set.Icc (0 : ℝ) T) :
    Integrable Ψ (v.val t).measure ∧
      (∫ x, Ψ x ∂(v.val t).measure) ≤
        exponentialEnvelope (∫ x, Ψ x ∂ν.measure) C t.val := by
  have hB (s : Set.Icc (0 : ℝ) T) :
      0 ≤ intervalEnvelope (∫ x, Ψ x ∂ν.measure) C T s :=
    (integral_nonneg hΨ).trans
      (le_exponentialEnvelope (integral_nonneg hΨ) hC s.property.1)
  exact ⟨curve_integrable hΨ v t, curve_integral_le hΨ hB v t⟩

end CarryingCapacity.LyapunovFlowSpace
