import CarryingCapacity.MarkedSplitting
import CarryingCapacity.MarkedBoundedCounts
import CarryingCapacity.PoissonSuperposition

/-!
# Laws of bounded marked rectangles on the common noise

Each translated strip has the proved joint category law. The complete strip
records are independent under the actual common-noise product law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace CarryingCapacity.MarkedRectangleLaw
open MarkedNoise MarkedStripCounts MarkedSplitting
  MarkedBoundedCounts MarkedIntensity

variable {J : Type*} {k : ℕ}

def stripVector (j : J) (n : ℕ) (B : Fin k → Set ℝ) (T : ℝ)
    (ω : MarkedNoise.Sample J) : Fin k → ℕ :=
  fun i => clockCount ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B i) T (ω (j, n))

theorem measurable_stripVector (j : J) (n : ℕ) (B : Fin k → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i)) (T : ℝ) :
    Measurable (stripVector j n B T) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_clockCount _ ((hB i).preimage
    (measurable_const.add measurable_id)) T).comp (measurable_pi_apply (j, n))

theorem stripVector_map (j : J) (n : ℕ) (B : Fin k → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hdis : Pairwise (fun i l => Disjoint (B i) (B l))) (T : ℝ) (hT : 0 ≤ T) :
    Measure.map (stripVector j n B T) (law J) =
      Measure.pi (fun i => poissonMeasure
        ⟨T * FrozenProcess.uniformUnit.real ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B i),
          mul_nonneg hT measureReal_nonneg⟩) := by
  let A : Fin k → Set ℝ := fun i => (fun x : ℝ => (n : ℝ) + x) ⁻¹' B i
  have hA (i : Fin k) : MeasurableSet (A i) :=
    (hB i).preimage (measurable_const.add measurable_id)
  have hd : Pairwise (fun i l => Disjoint (A i) (A l)) := by
    intro i l hil
    exact (hdis hil).preimage _
  have hm : Measurable (fun ω : StripSample => fun i => clockCount (A i) T ω) :=
    measurable_pi_lambda _ (fun i => measurable_clockCount (A i) (hA i) T)
  change Measure.map ((fun ω : StripSample => fun i => clockCount (A i) T ω) ∘
    (fun ω : Sample J => ω (j, n))) (law J) = _
  rw [← Measure.map_map hm (measurable_pi_apply (j, n)), strip_map J (j, n)]
  exact categoryCounts_map A hA hd T hT

/-- Independence is between complete category vectors in distinct actual strips. -/
theorem independent_stripVectors (j : J) (m : ℕ) (B : Fin k → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i)) (T : ℝ) :
    iIndepFun (fun n : Fin m => stripVector j n B T) (law J) := by
  have hinj : Function.Injective (fun n : Fin m => (j, (n : ℕ))) := by
    intro n l h
    exact Fin.ext (congrArg Prod.snd h)
  have hi := (independent_strips J).precomp hinj
  exact hi.comp (fun n => fun ω : StripSample => fun i =>
    clockCount ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B i) T ω)
    (fun n => measurable_pi_lambda _ (fun i => measurable_clockCount _
      ((hB i).preimage (measurable_const.add measurable_id)) T))

/-- Independent Poisson category counts for the full common noise in bounded height. -/
theorem boundedCounts_map (j : J) (m : ℕ) (B : Fin k → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hbound : ∀ i, B i ⊆ Iio (m : ℝ))
    (hdis : Pairwise (fun i l => Disjoint (B i) (B l))) (T : ℝ) (hT : 0 ≤ T) :
    Measure.map (fun ω : Sample J => fun i => boundedCount j m (B i) T ω) (law J) =
      Measure.pi (fun i => poissonMeasure
        ⟨T * positiveVolume.real (B i), mul_nonneg hT measureReal_nonneg⟩) := by
  let X : Fin m → Sample J → (Fin k → ℕ) := fun n => stripVector j n B T
  let r : Fin m → Fin k → ℝ≥0 := fun n i =>
    ⟨T * FrozenProcess.uniformUnit.real ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B i),
      mul_nonneg hT measureReal_nonneg⟩
  have hX (n : Fin m) : Measurable (X n) := measurable_stripVector j n B hB T
  have hLaw (n : Fin m) : Measure.map (X n) (law J) =
      Measure.pi (fun i => poissonMeasure (r n i)) := stripVector_map j n B hB hdis T hT
  have h := PoissonSuperposition.sumCounts_map X hX
    (independent_stripVectors j m B hB T) r hLaw
  have hfun : PoissonSuperposition.sumCounts X =
      (fun ω : Sample J => fun i => boundedCount j m (B i) T ω) := by
    funext ω i
    exact Fin.sum_univ_eq_sum_range (fun n : ℕ =>
      clockCount ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B i) T (ω (j, n))) m
  have hr (i : Fin k) : (∑ n, r n i) =
      (⟨T * positiveVolume.real (B i), mul_nonneg hT measureReal_nonneg⟩ : ℝ≥0) := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_sum]
    change (∑ n : Fin m, T * FrozenProcess.uniformUnit.real
      ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B i)) = T * positiveVolume.real (B i)
    rw [← Finset.mul_sum]
    congr 1
    calc
      _ = ∑ n ∈ Finset.range m, FrozenProcess.uniformUnit.real
          ((fun x : ℝ => (n : ℝ) + x) ⁻¹' B i) :=
        Fin.sum_univ_eq_sum_range _ m
      _ = _ := sum_uniformUnit_real_preimage m (B i) (hB i) (hbound i)
  simpa only [hfun, hr] using h

/-- Joint law of the genuine masses of disjoint bounded-height rectangles.
The right side is a product Poisson vector embedded in extended nonnegative reals. -/
theorem countingMeasure_rectangles_map (j : J) (m : ℕ) (B : Fin k → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hbound : ∀ i, B i ⊆ Iio (m : ℝ))
    (hdis : Pairwise (fun i l => Disjoint (B i) (B l))) (T : ℝ) (hT : 0 ≤ T) :
    Measure.map (fun ω : Sample J => fun i => countingMeasure j ω (Iic T ×ˢ B i)) (law J) =
      Measure.map (fun v : Fin k → ℕ => fun i => (v i : ℝ≥0∞))
        (Measure.pi (fun i => poissonMeasure
          ⟨T * positiveVolume.real (B i), mul_nonneg hT measureReal_nonneg⟩)) := by
  have hm : Measurable (fun ω : Sample J => fun i => boundedCount j m (B i) T ω) :=
    measurable_pi_lambda _ (fun i => measurable_boundedCount j m (B i) (hB i) T)
  rw [← boundedCounts_map j m B hB hbound hdis T hT,
    Measure.map_map (measurable_of_countable _) hm]
  apply Measure.map_congr
  filter_upwards [ae_countingMeasure_eq_boundedCount j] with ω hω
  funext i
  exact hω m (B i) (hB i) (hbound i) T hT

end CarryingCapacity.MarkedRectangleLaw
