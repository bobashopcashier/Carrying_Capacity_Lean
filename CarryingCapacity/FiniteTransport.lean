import CarryingCapacity.TransportMetric

/-!
# Common-mass couplings on finite sets

The coupling keeps the common mass of each atom on the diagonal and couples
the residual masses independently. All transport bounds below are obtained
from this actual finite measure, with its marginals and cost verified.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Classical Topology

namespace CarryingCapacity.FiniteTransport

section Matrix
variable {I : Type*} [Fintype I] (p q : I → ℝ)

def residual (i : I) : ℝ := p i - min (p i) (q i)
def unmatched : ℝ := ∑ i, residual p q i

omit [Fintype I] in
theorem residual_nonneg (i : I) : 0 ≤ residual p q i := sub_nonneg.mpr (min_le_left _ _)
theorem unmatched_nonneg : 0 ≤ unmatched p q := Finset.sum_nonneg fun i _ => residual_nonneg p q i

theorem unmatched_swap (hs : ∑ i, p i = ∑ i, q i) : unmatched q p = unmatched p q := by
  simp only [unmatched, residual, Finset.sum_sub_distrib, min_comm]
  rw [hs]

theorem residual_eq_zero_of_unmatched_zero (h : unmatched p q = 0) (i : I) :
    residual p q i = 0 := by
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => residual_nonneg p q j)).mp h i (Finset.mem_univ i)

def commonMatrix (i j : I) : ℝ :=
  (if i = j then min (p i) (q i) else 0) +
    residual p q i * residual q p j / unmatched p q

theorem commonMatrix_nonneg (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (i j : I) :
    0 ≤ commonMatrix p q i j := by
  apply add_nonneg
  · split_ifs
    · exact le_min (hp i) (hq i)
    · exact le_rfl
  · exact div_nonneg (mul_nonneg (residual_nonneg p q i) (residual_nonneg q p j))
      (unmatched_nonneg p q)

theorem commonMatrix_row (hs : ∑ i, p i = ∑ i, q i) (i : I) :
    ∑ j, commonMatrix p q i j = p i := by
  simp only [commonMatrix, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, ← Finset.sum_div, ← Finset.mul_sum]
  change min (p i) (q i) + residual p q i * unmatched q p / unmatched p q = p i
  rw [unmatched_swap p q hs]
  by_cases ht : unmatched p q = 0
  · have hr := residual_eq_zero_of_unmatched_zero p q ht i
    simp only [ht, div_zero, add_zero]
    unfold residual at hr
    linarith
  · rw [mul_div_cancel_right₀ _ ht]
    unfold residual
    ring

theorem commonMatrix_col (hs : ∑ i, p i = ∑ i, q i) (j : I) :
    ∑ i, commonMatrix p q i j = q j := by
  simp only [commonMatrix, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, ← Finset.sum_div, ← Finset.sum_mul]
  change min (p j) (q j) + unmatched p q * residual q p j / unmatched p q = q j
  by_cases ht : unmatched p q = 0
  · have hswap : unmatched q p = 0 := (unmatched_swap p q hs).trans ht
    have hr := residual_eq_zero_of_unmatched_zero q p hswap j
    simp only [ht, zero_mul, zero_div, add_zero]
    unfold residual at hr
    rw [min_comm] at hr
    linarith
  · rw [mul_div_cancel_left₀ _ ht]
    unfold residual
    rw [min_comm]
    ring

theorem twice_unmatched (hs : ∑ i, p i = ∑ i, q i) :
    2 * unmatched p q = ∑ i, |p i - q i| := by
  have he (i : I) : residual p q i + residual q p i = |p i - q i| := by
    unfold residual
    rcases le_total (p i) (q i) with h | h
    · rw [min_eq_left h, min_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, min_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  calc
    2 * unmatched p q = unmatched p q + unmatched q p := by rw [unmatched_swap p q hs]; ring
    _ = _ := by simp only [unmatched, ← Finset.sum_add_distrib, he]

theorem commonMatrix_cost_le (hs : ∑ i, p i = ∑ i, q i)
    (c : I → I → ℝ) (hc : ∀ i, c i i = 0) (B : ℝ) (hB : ∀ i j, c i j ≤ B) :
    (∑ i, ∑ j, commonMatrix p q i j * c i j) ≤ B * unmatched p q := by
  have hterm (i j : I) : commonMatrix p q i j * c i j ≤
      (residual p q i * residual q p j / unmatched p q) * B := by
    unfold commonMatrix
    rw [add_mul]
    have hd : (if i = j then min (p i) (q i) else 0) * c i j = 0 := by
      by_cases h : i = j
      · subst j
        simp [hc]
      · simp [h]
    rw [hd, zero_add]
    exact mul_le_mul_of_nonneg_left (hB i j)
      (div_nonneg (mul_nonneg (residual_nonneg p q i) (residual_nonneg q p j))
        (unmatched_nonneg p q))
  calc
    _ ≤ ∑ i, ∑ j, (residual p q i * residual q p j / unmatched p q) * B :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = B * unmatched p q := by
      simp only [← Finset.sum_mul, ← Finset.sum_div, ← Finset.mul_sum]
      change (unmatched p q * unmatched q p / unmatched p q) * B = _
      rw [unmatched_swap p q hs]
      by_cases ht : unmatched p q = 0
      · simp [ht]
      · rw [mul_div_cancel_right₀ _ ht, mul_comm]
end Matrix

section Atomic
variable {I α β : Type*} [Fintype I] [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α]

def atomicMeasure (x : I → α) (p : I → ℝ) : Measure α :=
  ∑ i, ENNReal.ofReal (p i) • Measure.dirac (x i)

omit [MeasurableSingletonClass α] in
theorem map_atomicMeasure (x : I → α) (p : I → ℝ) (f : α → β) (hf : Measurable f) :
    Measure.map f (atomicMeasure x p) = atomicMeasure (fun i => f (x i)) p := by
  unfold atomicMeasure
  rw [← Measure.mapₗ_apply_of_measurable hf, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.mapₗ_apply_of_measurable hf, Measure.map_smul, Measure.map_dirac hf]

theorem integral_atomicMeasure (x : I → α) (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (f : α → ℝ) :
    (∫ a, f a ∂atomicMeasure x p) = ∑ i, p i * f (x i) := by
  unfold atomicMeasure
  rw [integral_finset_sum_measure (fun i _ => integrable_dirac.smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro i _
  simp [integral_smul_measure, ENNReal.toReal_ofReal (hp i)]

omit [MeasurableSingletonClass α] in
theorem atomicMeasure_const (x : α) (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) :
    atomicMeasure (fun _ => x) p = ENNReal.ofReal (∑ i, p i) • Measure.dirac x := by
  rw [atomicMeasure, ← Finset.sum_smul, ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i)]

end Atomic

section FiniteSupport
variable {D : ℕ} {κ : MomentScale}

theorem sum_atomMass (μ : MomentLaw κ D) (S : Finset (State D)) (hS : μ.measure S = 1) :
    (∑ x : S, μ.measure.real {x.val}) = 1 := by
  letI : IsProbabilityMeasure μ.measure := μ.probability
  haveI : IsFiniteMeasure μ.measure := inferInstance
  haveI : SigmaFinite μ.measure := inferInstance
  rw [show (∑ x : S, μ.measure.real {x.val}) = ∑ x ∈ S, μ.measure.real {x} from
    Finset.sum_attach S (fun x => μ.measure.real {x})]
  simpa [measureReal_def, hS] using sum_measureReal_singleton (μ := μ.measure) S

theorem atomicMeasure_atomMass (μ : MomentLaw κ D) (S : Finset (State D))
    (hS : μ.measure S = 1) :
    atomicMeasure (fun x : S => x.val) (fun x => μ.measure.real {x.val}) = μ.measure := by
  letI : IsProbabilityMeasure μ.measure := μ.probability
  haveI : IsFiniteMeasure μ.measure := inferInstance
  apply Measure.ext_of_singleton
  intro x
  simp only [atomicMeasure, Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton x), Set.mem_singleton_iff]
  by_cases hx : x ∈ S
  · let ix : S := ⟨x, hx⟩
    have hi (i : S) : i.val = x ↔ i = ix := by
      change i.val = ix.val ↔ i = ix
      exact Subtype.ext_iff.symm
    simp [Set.indicator, hi, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _), ix]
  · have hzero : μ.measure {x} = 0 := by
      apply measure_mono_null (show {x} ⊆ (S : Set (State D))ᶜ from by simpa)
      exact (prob_compl_eq_zero_iff S.measurableSet).mpr hS
    rw [hzero]
    apply Finset.sum_eq_zero
    intro i _
    have hi : i.val ≠ x := by intro hi; exact hx (hi ▸ i.property)
    simp [hi]

variable {I : Type*} [Fintype I]

theorem matrixMeasure_first (x : I → State D) (w : I → I → ℝ) (hw : ∀ i j, 0 ≤ w i j) :
    Measure.map Prod.fst (atomicMeasure (fun ij : I × I => (x ij.1, x ij.2))
      (fun ij => w ij.1 ij.2)) = atomicMeasure x (fun i => ∑ j, w i j) := by
  rw [map_atomicMeasure _ _ Prod.fst measurable_fst]
  unfold atomicMeasure
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  exact atomicMeasure_const (x i) (w i) (hw i)

theorem matrixMeasure_second (x : I → State D) (w : I → I → ℝ) (hw : ∀ i j, 0 ≤ w i j) :
    Measure.map Prod.snd (atomicMeasure (fun ij : I × I => (x ij.1, x ij.2))
      (fun ij => w ij.1 ij.2)) = atomicMeasure x (fun j => ∑ i, w i j) := by
  rw [map_atomicMeasure _ _ Prod.snd measurable_snd]
  unfold atomicMeasure
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact atomicMeasure_const (x j) (fun i => w i j) (fun i => hw i j)

/-- The common-mass matrix, lifted to an actual measure with both required marginals. -/
def commonCoupling (μ ν : MomentLaw κ D) (S : Finset (State D))
    (hμ : μ.measure S = 1) (hν : ν.measure S = 1) : Coupling μ ν where
  measure := atomicMeasure (fun ij : S × S => (ij.1.val, ij.2.val))
    (fun ij => commonMatrix (fun i : S => μ.measure.real {i.val})
      (fun j : S => ν.measure.real {j.val}) ij.1 ij.2)
  first_marginal := by
    rw [matrixMeasure_first _ _ (commonMatrix_nonneg _ _ (fun _ => measureReal_nonneg)
      (fun _ => measureReal_nonneg))]
    simp_rw [commonMatrix_row _ _ ((sum_atomMass μ S hμ).trans (sum_atomMass ν S hν).symm)]
    exact atomicMeasure_atomMass μ S hμ
  second_marginal := by
    rw [matrixMeasure_second _ _ (commonMatrix_nonneg _ _ (fun _ => measureReal_nonneg)
      (fun _ => measureReal_nonneg))]
    simp_rw [commonMatrix_col _ _ ((sum_atomMass μ S hμ).trans (sum_atomMass ν S hν).symm)]
    exact atomicMeasure_atomMass ν S hν

/-- Transport is bounded by half the finite ℓ¹ mass discrepancy times a diameter bound. -/
theorem wasserstein_le_commonMass (μ ν : MomentLaw κ D) (S : Finset (State D))
    (hμ : μ.measure S = 1) (hν : ν.measure S = 1) (B : ℝ)
    (hB : ∀ x ∈ S, ∀ y ∈ S, adaptedDistance κ x y ≤ B) :
    wasserstein μ ν ≤ (B / 2) * ∑ x : S, |μ.measure.real {x.val} - ν.measure.real {x.val}| := by
  let p : S → ℝ := fun x => μ.measure.real {x.val}
  let q : S → ℝ := fun x => ν.measure.real {x.val}
  have hs : ∑ i, p i = ∑ i, q i := (sum_atomMass μ S hμ).trans (sum_atomMass ν S hν).symm
  calc
    wasserstein μ ν ≤ (commonCoupling μ ν S hμ hν).cost := wasserstein_le_cost _
    _ = ∑ i : S, ∑ j : S, commonMatrix p q i j * adaptedDistance κ i.val j.val := by
      change (∫ a : State D × State D, adaptedDistance κ a.1 a.2
        ∂atomicMeasure (fun ij : S × S => (ij.1.val, ij.2.val))
          (fun ij => commonMatrix p q ij.1 ij.2)) = _
      rw [integral_atomicMeasure (fun ij : S × S => (ij.1.val, ij.2.val))
        (fun ij => commonMatrix p q ij.1 ij.2) (fun ij => commonMatrix_nonneg p q
          (fun _ => measureReal_nonneg) (fun _ => measureReal_nonneg) ij.1 ij.2)
        (fun a : State D × State D => adaptedDistance κ a.1 a.2), Fintype.sum_prod_type]
    _ ≤ B * unmatched p q := commonMatrix_cost_le p q hs _ (fun i => adaptedDistance_self κ i.val)
      B (fun i j => hB i.val i.property j.val j.property)
    _ = _ := by rw [← twice_unmatched p q hs]; ring

end FiniteSupport

/-- On a fixed finite support, convergence of atom probabilities implies
convergence in the actual adapted Wasserstein distance. -/
theorem wasserstein_tendsto_of_finite_support {D : ℕ} {κ : MomentScale}
    {A : Type*} {l : Filter A} (μ : A → MomentLaw κ D) (ν : MomentLaw κ D)
    (S : Finset (State D)) (hμ : ∀ a, (μ a).measure S = 1) (hν : ν.measure S = 1)
    (h : ∀ x ∈ S, Tendsto (fun a => (μ a).measure.real {x}) l (𝓝 (ν.measure.real {x}))) :
    Tendsto (fun a => wasserstein (μ a) ν) l (𝓝 0) := by
  let B : ℝ := 2 * ∑ x : S, momentWeight κ x.val
  have hB (x : State D) (hx : x ∈ S) (y : State D) (hy : y ∈ S) :
      adaptedDistance κ x y ≤ B := by
    have hx' : momentWeight κ x ≤ ∑ z : S, momentWeight κ z.val :=
      Finset.single_le_sum (fun (z : S) _ => momentWeight_nonneg κ z.val)
        (Finset.mem_univ (⟨x, hx⟩ : S))
    have hy' : momentWeight κ y ≤ ∑ z : S, momentWeight κ z.val :=
      Finset.single_le_sum (fun (z : S) _ => momentWeight_nonneg κ z.val)
        (Finset.mem_univ (⟨y, hy⟩ : S))
    have hd := adaptedDistance_le_weights (κ := κ) x y
    change adaptedDistance κ x y ≤ 2 * ∑ z : S, momentWeight κ z.val
    linarith
  have hsum : Tendsto (fun a => ∑ x : S, |(μ a).measure.real {x.val} - ν.measure.real {x.val}|)
      l (𝓝 0) := by
    have hh := tendsto_finset_sum Finset.univ (fun x (_ : x ∈ (Finset.univ : Finset S)) =>
      ((h x.val x.property).sub (tendsto_const_nhds (x := ν.measure.real {x.val}))).abs)
    simpa only [sub_self, abs_zero, Finset.sum_const_zero] using hh
  apply squeeze_zero (fun a => wasserstein_nonneg (μ a) ν)
    (fun a => wasserstein_le_commonMass (μ a) ν S (hμ a) hν B hB)
  simpa only [mul_zero] using hsum.const_mul (B / 2)

end CarryingCapacity.FiniteTransport
