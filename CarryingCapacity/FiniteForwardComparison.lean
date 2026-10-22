import CarryingCapacity.IntegralGronwall

/-!
# Comparison for finite integrated forward systems

Nonnegative off-diagonal coefficients preserve componentwise ordering. The
proof uses every subinterval of the actual integral equation: after the last
nonpositive value of a component, its diagonal contribution is bounded by its
positive part. Summing these bounds reduces the result to integral Gronwall.
Thus no differentiability, integrating-factor identity, or comparison
conclusion is supplied as an assumption.

A one-sided inequality anchored only at time zero would not suffice when the
diagonal is negative. The main core theorem instead assumes increments on
all subintervals; the equality wrappers derive those increments explicitly.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace CarryingCapacity.FiniteForwardComparison

/-- The last nonpositive time reduces a positive-part estimate to an
increment estimate on an interval where the function is positive. -/
theorem positivePart_le_integral {f g : ℝ → ℝ} {T : ℝ}
    (hf : ContinuousOn f (Icc 0 T)) (hf0 : f 0 ≤ 0)
    (hg : IntegrableOn g (Ioc 0 T)) (hg0 : ∀ s ∈ Ioc 0 T, 0 ≤ g s)
    (hinc : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc s T,
      (∀ r ∈ Ioc s t, 0 < f r) → f t - f s ≤ ∫ r in Ioc s t, g r) :
    ∀ t ∈ Icc 0 T, max (f t) 0 ≤ ∫ r in Ioc 0 t, g r := by
  intro t ht
  have hgt := hg.mono_set (Ioc_subset_Ioc_right ht.2)
  have hgn : 0 ≤ ∫ r in Ioc 0 t, g r := integral_nonneg_of_ae
    ((ae_restrict_mem measurableSet_Ioc).mono
      (fun r hr => hg0 r ⟨hr.1, hr.2.trans ht.2⟩))
  by_cases hft : f t ≤ 0
  · simpa only [max_eq_right hft] using hgn
  let S : Set ℝ := {s ∈ Icc 0 t | f s ≤ 0}
  have hS : IsCompact S := isCompact_Icc.of_isClosed_subset
    (isClosed_Icc.isClosed_le (hf.mono (Icc_subset_Icc_right ht.2)) continuousOn_const)
    (fun _ hs => hs.1)
  have hSne : S.Nonempty := ⟨0, ⟨⟨le_rfl, ht.1⟩, hf0⟩⟩
  obtain ⟨s, hs, hmax⟩ := hS.exists_isMaxOn hSne continuousOn_id
  have hsT : s ∈ Icc 0 T := ⟨hs.1.1, hs.1.2.trans ht.2⟩
  have hpos : ∀ r ∈ Ioc s t, 0 < f r := by
    intro r hr
    by_contra h
    have hrS : r ∈ S := ⟨⟨hs.1.1.trans hr.1.le, hr.2⟩, le_of_not_gt h⟩
    exact (not_le_of_gt hr.1) (hmax hrS)
  have hi := hinc s hsT t ⟨hs.1.2, ht.2⟩ hpos
  have hmono : (∫ r in Ioc s t, g r) ≤ ∫ r in Ioc 0 t, g r :=
    setIntegral_mono_set hgt
      ((ae_restrict_mem measurableSet_Ioc).mono
        (fun r hr => hg0 r ⟨hr.1, hr.2.trans ht.2⟩))
      (Filter.Eventually.of_forall (fun r hr => ⟨hs.1.1.trans_lt hr.1, hr.2⟩))
  rw [max_eq_left (le_of_not_ge hft)]
  linarith [hs.2]

variable {ι : Type*} [Fintype ι]

/-- The finite incoming operator, with source index first and target second. -/
def forward (Q : ℝ → ι → ι → ℝ) (u : ι → ℝ → ℝ) (i : ι) (t : ℝ) : ℝ :=
  ∑ j, Q t j i * u j t

theorem forward_sub (Q : ℝ → ι → ι → ℝ) (u v : ι → ℝ → ℝ) (i : ι) (t : ℝ) :
    forward Q (fun j s => u j s - v j s) i t = forward Q u i t - forward Q v i t := by
  simp only [forward, mul_sub, Finset.sum_sub_distrib]

/-- Positive comparison for genuine increment subsolutions. Diagonal
coefficients may have either sign; only off-diagonal coefficients must be
nonnegative. The finite coefficient bound is only an upper bound. -/
theorem nonpos_of_increment_le {u : ι → ℝ → ℝ} {Q : ℝ → ι → ι → ℝ} {C T : ℝ}
    (hT : 0 ≤ T) (hu : ∀ i, ContinuousOn (u i) (Icc 0 T)) (hC : 0 ≤ C)
    (hQpos : ∀ t ∈ Icc 0 T, ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hQbound : ∀ t ∈ Icc 0 T, ∀ i j, Q t i j ≤ C)
    (hinit : ∀ i, u i 0 ≤ 0)
    (hInt : ∀ i, IntegrableOn (forward Q u i) (Ioc 0 T))
    (hinc : ∀ i s, s ∈ Icc 0 T → ∀ t ∈ Icc s T,
      u i t - u i s ≤ ∫ r in Ioc s t, forward Q u i r) :
    ∀ t ∈ Icc 0 T, ∀ i, u i t ≤ 0 := by
  classical
  let U : ℝ → ℝ := fun t => ∑ j, max (u j t) 0
  have hU : ContinuousOn U (Icc 0 T) :=
    continuousOn_finset_sum _ (fun j _ => (hu j).sup continuousOn_const)
  have hU0 (t : ℝ) : 0 ≤ U t := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hpart (i : ι) (t : ℝ) (ht : t ∈ Icc 0 T) :
      max (u i t) 0 ≤ C * ∫ r in Ioc 0 t, U r := by
    have hi : IntegrableOn (fun r => C * U r) (Ioc 0 T) :=
      (hU.integrableOn_Icc (μ := volume)).mono_set Ioc_subset_Icc_self |>.const_mul C
    have h := positivePart_le_integral (hu i) (hinit i) hi
      (fun r _ => mul_nonneg hC (hU0 r)) (by
        intro s hs t ht hpos
        apply (hinc i s hs t ht).trans
        apply setIntegral_mono_on
          ((hInt i).mono_set (Ioc_subset_Ioc hs.1 ht.2))
          (hi.mono_set (Ioc_subset_Ioc hs.1 ht.2)) measurableSet_Ioc
        intro r hr
        have hrT : r ∈ Icc 0 T := ⟨hs.1.trans hr.1.le, hr.2.trans ht.2⟩
        change (∑ j, Q r j i * u j r) ≤ C * ∑ j, max (u j r) 0
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j _
        by_cases hji : j = i
        · subst j
          rw [max_eq_left (hpos r hr).le]
          exact mul_le_mul_of_nonneg_right (hQbound r hrT i i) (hpos r hr).le
        · exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (hQpos r hrT j i hji)).trans
            (mul_le_mul_of_nonneg_right (hQbound r hrT j i) (le_max_right _ _))) t ht
    simpa only [integral_const_mul] using h
  have hG := IntegralGronwall.le_exp_mul_of_setIntegral hT hU
    (mul_nonneg (Nat.cast_nonneg (Fintype.card ι)) hC) (a := 0) (by
      intro t ht
      calc
        U t ≤ ∑ i : ι, C * ∫ r in Ioc 0 t, U r := Finset.sum_le_sum (fun i _ => hpart i t ht)
        _ = 0 + ((Fintype.card ι : ℝ) * C) * ∫ r in Ioc 0 t, U r := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, zero_add]
          ring)
  intro t ht i
  have hUi : max (u i t) 0 ≤ U t :=
    Finset.single_le_sum (fun j _ => le_max_right (u j t) 0) (Finset.mem_univ i)
  have hz := hG t ht
  simp only [zero_mul] at hz
  exact (le_max_left _ _).trans (hUi.trans hz)

/-- An anchored integral equality supplies the exact equation on every
subinterval. Integrability is explicit, so no totalized-integral convention
can erase the drift. -/
theorem increment_eq_of_integral_eq {u F : ℝ → ℝ} {T : ℝ}
    (hF : IntegrableOn F (Ioc 0 T))
    (hEq : ∀ t ∈ Icc 0 T, u t = u 0 + ∫ r in Ioc 0 t, F r)
    (s : ℝ) (hs : s ∈ Icc 0 T) (t : ℝ) (ht : t ∈ Icc s T) :
    u t - u s = ∫ r in Ioc s t, F r := by
  have h0s := hF.mono_set (Ioc_subset_Ioc_right hs.2)
  have hst := hF.mono_set (Ioc_subset_Ioc hs.1 ht.2)
  have hadd := setIntegral_union (Ioc_disjoint_Ioc_of_le (a := (0 : ℝ)) (d := t) le_rfl)
    measurableSet_Ioc h0s hst
  rw [Ioc_union_Ioc_eq_Ioc hs.1 ht.1] at hadd
  rw [hEq t ⟨hs.1.trans ht.1, ht.2⟩, hEq s hs]
  linarith

/-- A finite forward system with nonpositive forcing preserves nonpositive
initial data. Only the trajectories must be continuous; the coefficients
and forcing are allowed to be merely integrable as they occur in the equation. -/
theorem nonpos_of_integral_eq {u f : ι → ℝ → ℝ} {Q : ℝ → ι → ι → ℝ} {C T : ℝ}
    (hT : 0 ≤ T) (hu : ∀ i, ContinuousOn (u i) (Icc 0 T)) (hC : 0 ≤ C)
    (hQpos : ∀ t ∈ Icc 0 T, ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hQbound : ∀ t ∈ Icc 0 T, ∀ i j, Q t i j ≤ C)
    (hinit : ∀ i, u i 0 ≤ 0)
    (hInt : ∀ i, IntegrableOn (forward Q u i) (Ioc 0 T))
    (hfInt : ∀ i, IntegrableOn (f i) (Ioc 0 T))
    (hf : ∀ i t, t ∈ Ioc 0 T → f i t ≤ 0)
    (hEq : ∀ i t, t ∈ Icc 0 T →
      u i t = u i 0 + ∫ r in Ioc 0 t, (forward Q u i r + f i r)) :
    ∀ t ∈ Icc 0 T, ∀ i, u i t ≤ 0 := by
  apply nonpos_of_increment_le hT hu hC hQpos hQbound hinit hInt
  intro i s hs t ht
  rw [increment_eq_of_integral_eq ((hInt i).add (hfInt i)) (hEq i) s hs t ht]
  simp only [Pi.add_apply]
  rw [integral_add ((hInt i).mono_set (Ioc_subset_Ioc hs.1 ht.2))
    ((hfInt i).mono_set (Ioc_subset_Ioc hs.1 ht.2))]
  have hfnonpos : (∫ r in Ioc s t, f i r) ≤ 0 := integral_nonpos_of_ae
    ((ae_restrict_mem measurableSet_Ioc).mono
      (fun r hr => hf i r ⟨hs.1.trans_lt hr.1, hr.2.trans ht.2⟩))
  linarith

/-- Continuous finite coefficients give the genuine drift integrability
needed by the comparison theorem on every compact time interval. -/
theorem integrableOn_forward {u : ι → ℝ → ℝ} {Q : ℝ → ι → ι → ℝ} {T : ℝ}
    (hu : ∀ i, ContinuousOn (u i) (Icc 0 T))
    (hQ : ∀ i j, ContinuousOn (fun t => Q t i j) (Icc 0 T)) (i : ι) :
    IntegrableOn (forward Q u i) (Ioc 0 T) :=
  (continuousOn_finset_sum _ (fun j _ => (hQ j i).mul (hu j))).integrableOn_Icc.mono_set
    Ioc_subset_Icc_self

/-- The continuous-coefficient version discharges all integrability
requirements from continuity, rather than assuming a comparison bound. -/
theorem nonpos_of_continuous_integral_eq
    {u f : ι → ℝ → ℝ} {Q : ℝ → ι → ι → ℝ} {C T : ℝ}
    (hT : 0 ≤ T) (hu : ∀ i, ContinuousOn (u i) (Icc 0 T))
    (hQ : ∀ i j, ContinuousOn (fun t => Q t i j) (Icc 0 T))
    (hfCont : ∀ i, ContinuousOn (f i) (Icc 0 T)) (hC : 0 ≤ C)
    (hQpos : ∀ t ∈ Icc 0 T, ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hQbound : ∀ t ∈ Icc 0 T, ∀ i j, Q t i j ≤ C)
    (hinit : ∀ i, u i 0 ≤ 0)
    (hf : ∀ i t, t ∈ Ioc 0 T → f i t ≤ 0)
    (hEq : ∀ i t, t ∈ Icc 0 T →
      u i t = u i 0 + ∫ r in Ioc 0 t, (forward Q u i r + f i r)) :
    ∀ t ∈ Icc 0 T, ∀ i, u i t ≤ 0 :=
  nonpos_of_integral_eq hT hu hC hQpos hQbound hinit (integrableOn_forward hu hQ)
    (fun i => (hfCont i).integrableOn_Icc.mono_set Ioc_subset_Icc_self) hf hEq

/-- The finite restriction of a full forward law dominates the homogeneous
finite system when the omitted incoming contribution is nonnegative. Both
equations and their integrability are supplied, and the ordering is proved. -/
theorem le_of_integral_eq {u v g : ι → ℝ → ℝ} {Q : ℝ → ι → ι → ℝ} {C T : ℝ}
    (hT : 0 ≤ T) (hu : ∀ i, ContinuousOn (u i) (Icc 0 T))
    (hv : ∀ i, ContinuousOn (v i) (Icc 0 T)) (hC : 0 ≤ C)
    (hQpos : ∀ t ∈ Icc 0 T, ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hQbound : ∀ t ∈ Icc 0 T, ∀ i j, Q t i j ≤ C)
    (hinit : ∀ i, u i 0 ≤ v i 0)
    (huInt : ∀ i, IntegrableOn (forward Q u i) (Ioc 0 T))
    (hvInt : ∀ i, IntegrableOn (forward Q v i) (Ioc 0 T))
    (hgInt : ∀ i, IntegrableOn (g i) (Ioc 0 T))
    (hg : ∀ i t, t ∈ Ioc 0 T → 0 ≤ g i t)
    (huEq : ∀ i t, t ∈ Icc 0 T → u i t = u i 0 + ∫ r in Ioc 0 t, forward Q u i r)
    (hvEq : ∀ i t, t ∈ Icc 0 T →
      v i t = v i 0 + ∫ r in Ioc 0 t, (forward Q v i r + g i r)) :
    ∀ t ∈ Icc 0 T, ∀ i, u i t ≤ v i t := by
  have hdInt (i : ι) : IntegrableOn (forward Q (fun j s => u j s - v j s) i) (Ioc 0 T) := by
    have he : forward Q (fun j s => u j s - v j s) i =
        (fun r => forward Q u i r - forward Q v i r) := funext (forward_sub Q u v i)
    rw [he]
    exact (huInt i).sub (hvInt i)
  have h := nonpos_of_integral_eq (u := fun i s => u i s - v i s)
    (f := fun i s => -g i s) hT (fun i => (hu i).sub (hv i)) hC hQpos hQbound
    (fun i => sub_nonpos.mpr (hinit i)) hdInt (fun i => (hgInt i).neg)
    (fun i s hs => neg_nonpos.mpr (hg i s hs)) (by
      intro i t ht
      have hit := huInt i |>.mono_set (Ioc_subset_Ioc_right ht.2)
      have hjt := hvInt i |>.mono_set (Ioc_subset_Ioc_right ht.2)
      have hgt := hgInt i |>.mono_set (Ioc_subset_Ioc_right ht.2)
      have hx := huEq i t ht
      have hy := hvEq i t ht
      rw [integral_add hjt hgt] at hy
      simp only [forward_sub, ← sub_eq_add_neg]
      rw [integral_sub (f := fun r => forward Q u i r - forward Q v i r)
        (g := g i) (hit.sub hjt) hgt, integral_sub hit hjt]
      linarith)
  intro t ht i
  exact sub_nonpos.mp (h t ht i)

/-- A direct continuous-coefficient comparison corollary for finite
forward equations with nonnegative external inflow. -/
theorem le_of_continuous_integral_eq
    {u v g : ι → ℝ → ℝ} {Q : ℝ → ι → ι → ℝ} {C T : ℝ}
    (hT : 0 ≤ T) (hu : ∀ i, ContinuousOn (u i) (Icc 0 T))
    (hv : ∀ i, ContinuousOn (v i) (Icc 0 T))
    (hQ : ∀ i j, ContinuousOn (fun t => Q t i j) (Icc 0 T))
    (hgCont : ∀ i, ContinuousOn (g i) (Icc 0 T)) (hC : 0 ≤ C)
    (hQpos : ∀ t ∈ Icc 0 T, ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hQbound : ∀ t ∈ Icc 0 T, ∀ i j, Q t i j ≤ C)
    (hinit : ∀ i, u i 0 ≤ v i 0)
    (hg : ∀ i t, t ∈ Ioc 0 T → 0 ≤ g i t)
    (huEq : ∀ i t, t ∈ Icc 0 T → u i t = u i 0 + ∫ r in Ioc 0 t, forward Q u i r)
    (hvEq : ∀ i t, t ∈ Icc 0 T →
      v i t = v i 0 + ∫ r in Ioc 0 t, (forward Q v i r + g i r)) :
    ∀ t ∈ Icc 0 T, ∀ i, u i t ≤ v i t :=
  le_of_integral_eq hT hu hv hC hQpos hQbound hinit (integrableOn_forward hu hQ)
    (integrableOn_forward hv hQ)
    (fun i => (hgCont i).integrableOn_Icc.mono_set Ioc_subset_Icc_self) hg huEq hvEq

end CarryingCapacity.FiniteForwardComparison
