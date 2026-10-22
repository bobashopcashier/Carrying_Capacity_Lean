import CarryingCapacity.MarkedProducts

/-!
# Products of iid marks in disjoint deterministic blocks

Distinct coordinates of the actual infinite uniform product measure have the
finite product law. Finite Fubini therefore factors products over any finite
family of disjoint index sets. Consecutive blocks specified by their lengths
are a particular case, including empty blocks.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

namespace CarryingCapacity.MarkedBlockProducts
open FrozenProcess MarkedNoise

theorem independent_marks : iIndepFun (fun n : ℕ => fun u : ℕ → ℝ => u n) unitMarksLaw := by
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro I sets hs
  have heq : (⋂ i ∈ I, (fun u : ℕ → ℝ => u i) ⁻¹' sets i) = Set.pi I sets := by
    ext u
    simp
  rw [heq, unitMarksLaw, Measure.infinitePi_pi _ hs]
  apply Finset.prod_congr rfl
  intro i hi
  have h := congrArg (fun μ : Measure ℝ => μ (sets i)) (unitMarks_coordinate_map i)
  dsimp only at h
  rw [Measure.map_apply (measurable_pi_apply i) (hs i hi)] at h
  exact h.symm

/-- Any finite collection of distinct actual mark coordinates has the iid product law. -/
theorem distinct_coordinates_map {I : Type*} [Fintype I]
    (e : I → ℕ) (he : Function.Injective e) :
    Measure.map (fun u : ℕ → ℝ => fun i => u (e i)) unitMarksLaw =
      Measure.pi (fun _ : I => uniformUnit) := by
  have h := (iIndepFun_iff_map_fun_eq_pi_map (fun i =>
    (measurable_pi_apply (e i)).aemeasurable)).mp (independent_marks.precomp he)
  simpa only [unitMarks_coordinate_map] using h

/-- Finite Fubini for coordinate-dependent factors at distinct mark indices. -/
theorem integral_distinct_products {I : Type*} [Fintype I]
    (e : I → ℕ) (he : Function.Injective e) (g : I → ℝ → ℂ)
    (hg : ∀ i, Measurable (g i)) :
    (∫ u, ∏ i, g i (u (e i)) ∂unitMarksLaw) =
      ∏ i, ∫ x, g i x ∂uniformUnit := by
  have hf : Measurable (fun v : I → ℝ => ∏ i, g i (v i)) :=
    Finset.measurable_prod _ (fun i _ => (hg i).comp (measurable_pi_apply i))
  calc
    _ = ∫ v : I → ℝ, ∏ i, g i (v i)
        ∂Measure.map (fun u : ℕ → ℝ => fun i => u (e i)) unitMarksLaw :=
      (integral_map_of_stronglyMeasurable
        (measurable_pi_lambda _ (fun i => measurable_pi_apply (e i)))
        hf.stronglyMeasurable).symm
    _ = _ := ?_
  rw [distinct_coordinates_map e he]
  letI : MeasureSpace ℝ := ⟨uniformUnit⟩
  letI : IsProbabilityMeasure (volume : Measure ℝ) := uniformUnit_probability
  exact integral_fintype_prod_eq_prod I g

/-- Arbitrary pairwise disjoint finite index sets factor into independent block means. -/
theorem integral_disjoint_products {I : Type*} [Fintype I]
    (s : I → Finset ℕ) (hdis : Pairwise (fun a b => Disjoint (s a) (s b)))
    (g : I → ℝ → ℂ) (hg : ∀ a, Measurable (g a)) :
    (∫ u, ∏ a, ∏ n ∈ s a, g a (u n) ∂unitMarksLaw) =
      ∏ a, (∫ x, g a x ∂uniformUnit) ^ (s a).card := by
  classical
  let e : (Σ a : I, s a) → ℕ := fun p => p.2.val
  have he : Function.Injective e := by
    rintro ⟨a, n⟩ ⟨b, k⟩ h
    change n.val = k.val at h
    have hab : a = b := by
      by_contra hab
      exact Finset.disjoint_left.mp (hdis hab) n.property
        (show n.val ∈ s b from h.symm ▸ k.property)
    subst b
    have hnk : n = k := Subtype.ext h
    subst k
    rfl
  have h := integral_distinct_products e he (fun p => g p.1) (fun p => hg p.1)
  have hprod (u : ℕ → ℝ) : (∏ p : Σ a : I, s a, g p.1 (u p.2)) =
      ∏ a, ∏ n ∈ s a, g a (u n) := by
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro a _
    exact Finset.prod_coe_sort (s a) (fun n => g a (u n))
  have hmean : (∏ p : Σ a : I, s a, ∫ x, g p.1 x ∂uniformUnit) =
      ∏ a, (∫ x, g a x ∂uniformUnit) ^ (s a).card := by
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro a _
    simp
  simpa only [e, hprod, hmean] using h

def blockStart {q : ℕ} (l : Fin q → ℕ) (a : Fin q) : ℕ :=
  ∑ b ∈ Finset.Iio a, l b

def blockIndices {q : ℕ} (l : Fin q → ℕ) (a : Fin q) : Finset ℕ :=
  Finset.Ico (blockStart l a) (blockStart l a + l a)

theorem blockEnd_le_start {q : ℕ} (l : Fin q → ℕ) {a b : Fin q} (hab : a < b) :
    blockStart l a + l a ≤ blockStart l b := by
  have hsub : insert a (Finset.Iio a) ⊆ Finset.Iio b := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact Finset.mem_Iio.mpr hab
    · exact Finset.mem_Iio.mpr ((Finset.mem_Iio.mp hc).trans hab)
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := l) hsub
    (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_insert (by simp)] at h
  simpa only [blockStart, Nat.add_comm] using h

theorem pairwise_blockIndices {q : ℕ} (l : Fin q → ℕ) :
    Pairwise (fun a b => Disjoint (blockIndices l a) (blockIndices l b)) := by
  intro a b hab
  apply Finset.disjoint_left.mpr
  intro n hna hnb
  have ha := Finset.mem_Ico.mp hna
  have hb := Finset.mem_Ico.mp hnb
  rcases lt_or_gt_of_ne hab with hab | hba
  · have h := blockEnd_le_start l hab
    omega
  · have h := blockEnd_le_start l hba
    omega

theorem card_blockIndices {q : ℕ} (l : Fin q → ℕ) (a : Fin q) :
    (blockIndices l a).card = l a := by
  simp [blockIndices]

/-- Consecutive deterministic blocks have exactly the specified powers of mark means. -/
theorem integral_consecutive_products {q : ℕ} (l : Fin q → ℕ)
    (g : Fin q → ℝ → ℂ) (hg : ∀ a, Measurable (g a)) :
    (∫ u, ∏ a, ∏ n ∈ blockIndices l a, g a (u n) ∂unitMarksLaw) =
      ∏ a, (∫ x, g a x ∂uniformUnit) ^ l a := by
  simpa only [card_blockIndices] using
    integral_disjoint_products (blockIndices l) (pairwise_blockIndices l) g hg

/-- Monotone endpoints give disjoint blocks, with no requirement on the first offset. -/
theorem pairwise_endpointBlocks {q : ℕ} (f : Fin (q + 1) → ℕ) (hf : Monotone f) :
    Pairwise (fun a b : Fin q => Disjoint
      (Finset.Ico (f a.castSucc) (f a.succ))
      (Finset.Ico (f b.castSucc) (f b.succ))) := by
  intro a b hab
  apply Finset.disjoint_left.mpr
  intro n hna hnb
  have ha := Finset.mem_Ico.mp hna
  have hb := Finset.mem_Ico.mp hnb
  rcases lt_or_gt_of_ne hab with hab | hba
  · have hi : a.succ ≤ b.castSucc := Fin.succ_le_castSucc_iff.mpr hab
    have h := hf hi
    omega
  · have hi : b.succ ≤ a.castSucc := Fin.succ_le_castSucc_iff.mpr hba
    have h := hf hi
    omega

theorem integral_endpoint_products {q : ℕ} (f : Fin (q + 1) → ℕ) (hf : Monotone f)
    (g : Fin q → ℝ → ℂ) (hg : ∀ a, Measurable (g a)) :
    (∫ u, ∏ a : Fin q, ∏ n ∈ Finset.Ico (f a.castSucc) (f a.succ),
      g a (u n) ∂unitMarksLaw) =
      ∏ a : Fin q, (∫ x, g a x ∂uniformUnit) ^ (f a.succ - f a.castSucc) := by
  simpa only [Nat.card_Ico] using integral_disjoint_products
    (fun a : Fin q => Finset.Ico (f a.castSucc) (f a.succ))
    (pairwise_endpointBlocks f hf) g hg

end CarryingCapacity.MarkedBlockProducts
