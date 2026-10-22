import CarryingCapacity.MarkedGridLaw
import CarryingCapacity.MarkedBoundedCounts
import CarryingCapacity.PoissonSuperposition

/-!
# Bounded marked time-grid laws on the original common noise

Each complete strip grid vector has the proved product Poisson law. Independent
strip records can therefore be superposed. The resulting finite natural count
vector agrees almost surely with the original counting measure on every grid
rectangle. Height categories may vary between windows and only need to be
disjoint within each individual window.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace CarryingCapacity.MarkedGridRectangles
open MarkedNoise MarkedStripCounts MarkedTimeCounts MarkedGridLaw
  MarkedBoundedCounts MarkedIntensity

variable {J : Type*} {q : ℕ} {ι : Type*} [Fintype ι]

def stripGridVector (j : J) (n : ℕ) (B : Fin q → ι → Set ℝ)
    (u : Fin (q + 1) → ℝ) (ω : MarkedNoise.Sample J) : (Fin q × ι) → ℕ :=
  gridVector (fun a i => (fun x : ℝ => (n : ℝ) + x) ⁻¹' B a i) u (ω (j, n))

omit [Fintype ι] in
theorem measurable_stripGridVector (j : J) (n : ℕ) (B : Fin q → ι → Set ℝ)
    (hB : ∀ a i, MeasurableSet (B a i)) (u : Fin (q + 1) → ℝ) :
    Measurable (stripGridVector j n B u) :=
  (measurable_gridVector _ (fun a i =>
    (hB a i).preimage (measurable_const.add measurable_id)) u).comp
      (measurable_pi_apply (j, n))

theorem stripGridVector_map (j : J) (n : ℕ) (B : Fin q → ι → Set ℝ)
    (hB : ∀ a i, MeasurableSet (B a i))
    (hdis : ∀ a, Pairwise (fun i l => Disjoint (B a i) (B a l)))
    (u : Fin (q + 1) → ℝ) (hu : Monotone u) (hu0 : 0 ≤ u 0) :
    Measure.map (stripGridVector j n B u) (law J) =
      Measure.pi (fun p : Fin q × ι => poissonMeasure
        ⟨(u p.1.succ - u p.1.castSucc) *
          FrozenProcess.uniformUnit.real ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B p.1 p.2),
          mul_nonneg (sub_nonneg.mpr (hu (Fin.castSucc_le_succ p.1)))
            measureReal_nonneg⟩) := by
  let A : Fin q → ι → Set ℝ := fun a i => (fun x : ℝ => (n : ℝ) + x) ⁻¹' B a i
  have hA (a : Fin q) (i : ι) : MeasurableSet (A a i) :=
    (hB a i).preimage (measurable_const.add measurable_id)
  have hd (a : Fin q) : Pairwise (fun i l => Disjoint (A a i) (A a l)) := by
    intro i l hil
    exact (hdis a hil).preimage _
  change Measure.map ((gridVector A u) ∘ (fun ω : Sample J => ω (j, n))) (law J) = _
  rw [← Measure.map_map (measurable_gridVector A hA u) (measurable_pi_apply (j, n)),
    strip_map J (j, n)]
  exact gridVector_map A hA hd u hu hu0

omit [Fintype ι] in
/-- Entire vectors, including all time windows and categories, are independent across strips. -/
theorem independent_stripGridVectors (j : J) (m : ℕ) (B : Fin q → ι → Set ℝ)
    (hB : ∀ a i, MeasurableSet (B a i)) (u : Fin (q + 1) → ℝ) :
    iIndepFun (fun n : Fin m => stripGridVector j n B u) (law J) := by
  have hinj : Function.Injective (fun n : Fin m => (j, (n : ℕ))) := by
    intro n l h
    exact Fin.ext (congrArg Prod.snd h)
  have hi := (independent_strips J).precomp hinj
  exact hi.comp (fun n => gridVector
    (fun a i => (fun x : ℝ => (n : ℝ) + x) ⁻¹' B a i) u)
    (fun n => measurable_gridVector _ (fun a i =>
      (hB a i).preimage (measurable_const.add measurable_id)) u)

def boundedGridVector (j : J) (m : ℕ) (B : Fin q → ι → Set ℝ)
    (u : Fin (q + 1) → ℝ) (ω : MarkedNoise.Sample J) (p : Fin q × ι) : ℕ :=
  boundedWindowCount j m (B p.1 p.2) (u p.1.castSucc) (u p.1.succ) ω

omit [Fintype ι] in
theorem measurable_boundedGridVector (j : J) (m : ℕ) (B : Fin q → ι → Set ℝ)
    (hB : ∀ a i, MeasurableSet (B a i)) (u : Fin (q + 1) → ℝ) :
    Measurable (boundedGridVector j m B u) :=
  measurable_pi_lambda _ (fun p => measurable_boundedWindowCount j m (B p.1 p.2)
    (hB p.1 p.2) (u p.1.castSucc) (u p.1.succ))

/-- Full product Poisson law of the bounded grid counts on the actual common sample space. -/
theorem boundedGridVector_map (j : J) (m : ℕ) (B : Fin q → ι → Set ℝ)
    (hB : ∀ a i, MeasurableSet (B a i))
    (hbound : ∀ a i, B a i ⊆ Iio (m : ℝ))
    (hdis : ∀ a, Pairwise (fun i l => Disjoint (B a i) (B a l)))
    (u : Fin (q + 1) → ℝ) (hu : Monotone u) (hu0 : 0 ≤ u 0) :
    Measure.map (boundedGridVector j m B u) (law J) =
      Measure.pi (fun p : Fin q × ι => poissonMeasure
        ⟨(u p.1.succ - u p.1.castSucc) * positiveVolume.real (B p.1 p.2),
          mul_nonneg (sub_nonneg.mpr (hu (Fin.castSucc_le_succ p.1)))
            measureReal_nonneg⟩) := by
  let X : Fin m → Sample J → ((Fin q × ι) → ℕ) := fun n => stripGridVector j n B u
  let r : Fin m → (Fin q × ι) → ℝ≥0 := fun n p =>
    ⟨(u p.1.succ - u p.1.castSucc) *
      FrozenProcess.uniformUnit.real ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B p.1 p.2),
      mul_nonneg (sub_nonneg.mpr (hu (Fin.castSucc_le_succ p.1))) measureReal_nonneg⟩
  have hX (n : Fin m) : Measurable (X n) := measurable_stripGridVector j n B hB u
  have hLaw (n : Fin m) : Measure.map (X n) (law J) =
      Measure.pi (fun p => poissonMeasure (r n p)) :=
    stripGridVector_map j n B hB hdis u hu hu0
  have h := PoissonSuperposition.sumCounts_map X hX
    (independent_stripGridVectors j m B hB u) r hLaw
  have hfun : PoissonSuperposition.sumCounts X = boundedGridVector j m B u := by
    funext ω p
    exact Fin.sum_univ_eq_sum_range (fun n : ℕ =>
      windowCount ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B p.1 p.2)
        (u p.1.castSucc) (u p.1.succ) (ω (j, n))) m
  have hr (p : Fin q × ι) : (∑ n, r n p) =
      (⟨(u p.1.succ - u p.1.castSucc) * positiveVolume.real (B p.1 p.2),
        mul_nonneg (sub_nonneg.mpr (hu (Fin.castSucc_le_succ p.1)))
          measureReal_nonneg⟩ : ℝ≥0) := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_sum]
    change (∑ n : Fin m, (u p.1.succ - u p.1.castSucc) * FrozenProcess.uniformUnit.real
      ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B p.1 p.2)) =
        (u p.1.succ - u p.1.castSucc) * positiveVolume.real (B p.1 p.2)
    rw [← Finset.mul_sum]
    congr 1
    calc
      _ = ∑ n ∈ Finset.range m, FrozenProcess.uniformUnit.real
          ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B p.1 p.2) :=
        Fin.sum_univ_eq_sum_range _ m
      _ = _ := sum_uniformUnit_real_preimage m (B p.1 p.2) (hB p.1 p.2) (hbound p.1 p.2)
  simpa only [hfun, hr] using h

/-- The genuine grid rectangle masses have the jointly independent Poisson law.
The product law is embedded into extended nonnegative reals by natural casts. -/
theorem countingMeasure_gridRectangles_map (j : J) (m : ℕ) (B : Fin q → ι → Set ℝ)
    (hB : ∀ a i, MeasurableSet (B a i))
    (hbound : ∀ a i, B a i ⊆ Iio (m : ℝ))
    (hdis : ∀ a, Pairwise (fun i l => Disjoint (B a i) (B a l)))
    (u : Fin (q + 1) → ℝ) (hu : Monotone u) (hu0 : 0 ≤ u 0) :
    Measure.map (fun ω : Sample J => fun p : Fin q × ι =>
      countingMeasure j ω (Ioc (u p.1.castSucc) (u p.1.succ) ×ˢ B p.1 p.2)) (law J) =
      Measure.map (fun v : (Fin q × ι) → ℕ => fun p => (v p : ℝ≥0∞))
        (Measure.pi (fun p : Fin q × ι => poissonMeasure
          ⟨(u p.1.succ - u p.1.castSucc) * positiveVolume.real (B p.1 p.2),
            mul_nonneg (sub_nonneg.mpr (hu (Fin.castSucc_le_succ p.1)))
              measureReal_nonneg⟩)) := by
  rw [← boundedGridVector_map j m B hB hbound hdis u hu hu0,
    Measure.map_map (measurable_of_countable _) (measurable_boundedGridVector j m B hB u)]
  apply Measure.map_congr
  filter_upwards [ae_countingMeasure_eq_boundedWindowCount j] with ω hω
  funext p
  exact hω m (B p.1 p.2) (hB p.1 p.2) (hbound p.1 p.2)
    (u p.1.castSucc) (u p.1.succ) (hu0.trans (hu (Fin.zero_le _)))
    (hu (Fin.castSucc_le_succ p.1))

end CarryingCapacity.MarkedGridRectangles
