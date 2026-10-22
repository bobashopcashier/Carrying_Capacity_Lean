import CarryingCapacity.CouplingExpectation

/-!
# Continuity of the expected distance of a common-space pair

The four-point metric inequality bounds changes of a coupled distance by the
changes of its two endpoints. Uniform genuine superlinear Lyapunov moments
turn almost-sure endpoint convergence into expected-distance convergence by the
previously proved uniform-integrability argument. This yields continuity of
the actual pair's expected distance without assuming any expected continuity.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace CarryingCapacity.CoupledDistanceContinuity

variable {D : ℕ} {κ : MomentScale}

/-- The cost difference is controlled by the changes of its two endpoints. -/
theorem adaptedDistance_difference_le (x y x' y' : State D) :
    |adaptedDistance κ x y - adaptedDistance κ x' y'| ≤
      adaptedDistance κ x x' + adaptedDistance κ y y' := by
  have h₁ := adaptedDistance_triangle κ x x' y
  have h₂ := adaptedDistance_triangle κ x' y' y
  have h₃ := adaptedDistance_triangle κ x' x y'
  have h₄ := adaptedDistance_triangle κ x y y'
  rw [adaptedDistance_symm κ y' y] at h₂
  rw [adaptedDistance_symm κ x' x] at h₃
  exact abs_le.mpr ⟨by linarith, by linarith⟩

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- Genuine Lyapunov integrability supplies the endpoint weight needed for
the real-valued coupling integrals. -/
theorem integrable_weight_of_lyapunov (Ψ : State D → ℝ)
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x) (X : Ω → State D)
    (hX : Measurable X) (hΨ : Integrable (fun ω => Ψ (X ω)) P) :
    Integrable (fun ω => momentWeight κ (X ω)) P := by
  apply hΨ.mono' ((measurable_of_countable (momentWeight κ)).comp hX).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    dsimp only [Function.comp_def]
    rw [Real.norm_eq_abs, abs_of_nonneg (momentWeight_nonneg κ _)]
    linarith [hdom (X ω)]

/-- Comparing two actual coupled costs uses their endpoint changes. All
four weights are integrable, so no totalized-integral convention is involved. -/
theorem abs_integral_distance_sub_le (X Y X' Y' : Ω → State D)
    (hX : Measurable X) (hY : Measurable Y) (hX' : Measurable X') (hY' : Measurable Y')
    (hWX : Integrable (fun ω => momentWeight κ (X ω)) P)
    (hWY : Integrable (fun ω => momentWeight κ (Y ω)) P)
    (hWX' : Integrable (fun ω => momentWeight κ (X' ω)) P)
    (hWY' : Integrable (fun ω => momentWeight κ (Y' ω)) P) :
    |(∫ ω, adaptedDistance κ (X ω) (Y ω) ∂P) -
      (∫ ω, adaptedDistance κ (X' ω) (Y' ω) ∂P)| ≤
      (∫ ω, adaptedDistance κ (X ω) (X' ω) ∂P) +
        (∫ ω, adaptedDistance κ (Y ω) (Y' ω) ∂P) := by
  have hxy := CouplingExpectation.integrable_distance κ P X Y hX hY hWX hWY
  have hxy' := CouplingExpectation.integrable_distance κ P X' Y' hX' hY' hWX' hWY'
  have hxx := CouplingExpectation.integrable_distance κ P X X' hX hX' hWX hWX'
  have hyy := CouplingExpectation.integrable_distance κ P Y Y' hY hY' hWY hWY'
  rw [← integral_sub hxy hxy']
  calc
    _ ≤ ∫ ω, |adaptedDistance κ (X ω) (Y ω) - adaptedDistance κ (X' ω) (Y' ω)| ∂P :=
      abs_integral_le_integral_abs
    _ ≤ ∫ ω, (adaptedDistance κ (X ω) (X' ω) + adaptedDistance κ (Y ω) (Y' ω)) ∂P :=
      integral_mono (hxy.sub hxy').abs (hxx.add hyy)
        (fun ω => adaptedDistance_difference_le (X ω) (Y ω) (X' ω) (Y' ω))
    _ = _ := integral_add hxx hyy

variable [IsProbabilityMeasure P]

/-- Almost-sure convergence of both endpoints yields convergence of the
expected pair distance under genuine uniform superlinear Lyapunov bounds. -/
theorem integral_distance_tendsto (Ψ : State D → ℝ)
    (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (X Y : ℕ → Ω → State D) (X₀ Y₀ : Ω → State D)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hX₀ : Measurable X₀) (hY₀ : Measurable Y₀)
    (hΨX : ∀ n, Integrable (fun ω => Ψ (X n ω)) P)
    (hΨY : ∀ n, Integrable (fun ω => Ψ (Y n ω)) P)
    (hΨX₀ : Integrable (fun ω => Ψ (X₀ ω)) P) (hΨY₀ : Integrable (fun ω => Ψ (Y₀ ω)) P)
    (C : ℝ) (hC : 0 ≤ C)
    (hboundX : ∀ n, (∫ ω, Ψ (X n ω) ∂P) ≤ C)
    (hboundY : ∀ n, (∫ ω, Ψ (Y n ω) ∂P) ≤ C)
    (hboundX₀ : (∫ ω, Ψ (X₀ ω) ∂P) ≤ C) (hboundY₀ : (∫ ω, Ψ (Y₀ ω) ∂P) ≤ C)
    (hconvX : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (X₀ ω)))
    (hconvY : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Y₀ ω))) :
    Tendsto (fun n => ∫ ω, adaptedDistance κ (X n ω) (Y n ω) ∂P)
      atTop (𝓝 (∫ ω, adaptedDistance κ (X₀ ω) (Y₀ ω) ∂P)) := by
  have hx := LawCurveContinuity.integral_distance_tendsto_zero P Ψ hdom hsuper X X₀ hX hX₀
    hΨX hΨX₀ C hC hboundX hboundX₀ hconvX
  have hy := LawCurveContinuity.integral_distance_tendsto_zero P Ψ hdom hsuper Y Y₀ hY hY₀
    hΨY hΨY₀ C hC hboundY hboundY₀ hconvY
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  apply squeeze_zero (fun _ => abs_nonneg _) (fun n => ?_) (by simpa only [zero_add] using hx.add hy)
  exact abs_integral_distance_sub_le P (X n) (Y n) X₀ Y₀ (hX n) (hY n) hX₀ hY₀
    (integrable_weight_of_lyapunov P Ψ hdom (X n) (hX n) (hΨX n))
    (integrable_weight_of_lyapunov P Ψ hdom (Y n) (hY n) (hΨY n))
    (integrable_weight_of_lyapunov P Ψ hdom X₀ hX₀ hΨX₀)
    (integrable_weight_of_lyapunov P Ψ hdom Y₀ hY₀ hΨY₀)

/-- The expected distance of two actual common-space path families is
continuous. Each fixed-time continuity assertion may have its own null set. -/
theorem continuous_expected_distance {I : Type*} [TopologicalSpace I] [SequentialSpace I]
    (Ψ : State D → ℝ) (hdom : ∀ x, 1 + momentWeight κ x ≤ Ψ x)
    (hsuper : Tendsto (fun x => Ψ x / (1 + momentWeight κ x))
      (Filter.comap populationSize atTop) atTop)
    (X Y : I → Ω → State D) (hX : ∀ t, Measurable (X t)) (hY : ∀ t, Measurable (Y t))
    (hΨX : ∀ t, Integrable (fun ω => Ψ (X t ω)) P)
    (hΨY : ∀ t, Integrable (fun ω => Ψ (Y t ω)) P)
    (C : ℝ) (hC : 0 ≤ C)
    (hboundX : ∀ t, (∫ ω, Ψ (X t ω) ∂P) ≤ C)
    (hboundY : ∀ t, (∫ ω, Ψ (Y t ω) ∂P) ≤ C)
    (hpathX : ∀ t, ∀ᵐ ω ∂P, ContinuousAt (fun s => X s ω) t)
    (hpathY : ∀ t, ∀ᵐ ω ∂P, ContinuousAt (fun s => Y s ω) t) :
    Continuous (fun t => ∫ ω, adaptedDistance κ (X t ω) (Y t ω) ∂P) := by
  apply continuous_iff_seqContinuous.mpr
  intro u t hut
  apply integral_distance_tendsto P Ψ hdom hsuper (fun n => X (u n)) (fun n => Y (u n)) (X t) (Y t)
    (fun n => hX (u n)) (fun n => hY (u n)) (hX t) (hY t)
    (fun n => hΨX (u n)) (fun n => hΨY (u n)) (hΨX t) (hΨY t) C hC
    (fun n => hboundX (u n)) (fun n => hboundY (u n)) (hboundX t) (hboundY t)
  · filter_upwards [hpathX t] with ω hω
    exact hω.tendsto.comp hut
  · filter_upwards [hpathY t] with ω hω
    exact hω.tendsto.comp hut

end CarryingCapacity.CoupledDistanceContinuity
