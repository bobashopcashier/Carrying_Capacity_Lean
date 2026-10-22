import CarryingCapacity.IndependentNoiseLabels
import CarryingCapacity.CommonNoiseFiltration

/-!
# Particle projections of the actual common marked noise

Noise labelled by a particle and a jump direction contains a complete copy of
the original jump-labelled noise for each particle. These projections have
the exact original marginal law and are jointly independent as entire records,
including all clocks and marks. A finite array therefore has the genuine
product law. Its counting measures are pointwise the corresponding original
counting measures, so projection retains the same driving randomness.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set MeasurableSpace
open scoped ENNReal

namespace CarryingCapacity.ParticleNoiseProjection
open MarkedNoise

variable {I J : Type*}

/-- Retain all jump labels and vertical strips belonging to one particle. -/
def project (i : I) (ω : Sample (I × J)) : Sample J :=
  fun p => ω ((i, p.1), p.2)

theorem measurable_project (i : I) : Measurable (project (J := J) i) :=
  measurable_pi_lambda _ (fun p => measurable_pi_apply ((i, p.1), p.2))

/-- Each whole projected record has the original common-noise law. No
finiteness or countability of the particle or jump index is required. -/
theorem project_map (i : I) :
    (law (I × J)).map (project i) = law J := by
  classical
  have hinj : Function.Injective (fun p : J × ℕ => ((i, p.1), p.2)) := by
    intro p q h
    exact congrArg (fun z : (I × J) × ℕ => (z.1.2, z.2)) h
  have hi := (independent_strips (I × J)).precomp hinj
  apply Measure.eq_infinitePi
  intro K sets hsets
  rw [Measure.map_apply (measurable_project i) (.pi K.countable_toSet hsets)]
  have he : (project i) ⁻¹' Set.pi (K : Set (J × ℕ)) sets =
      ⋂ p ∈ K, (fun ω : Sample (I × J) => ω ((i, p.1), p.2)) ⁻¹' sets p := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_iInter, project]
  rw [he, hi.measure_inter_preimage_eq_mul K hsets]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← Measure.map_apply (measurable_pi_apply ((i, p.1), p.2)) (hsets p hp),
    strip_map]

/-- All projected records are jointly independent. This groups the independent
strip sigma algebras into disjoint particle blocks, rather than using only
pairwise independence. -/
theorem independent_projects :
    iIndepFun (project (I := I) (J := J)) (law (I × J)) := by
  let m : (I × J) × ℕ → MeasurableSpace (Sample (I × J)) :=
    fun p => MeasurableSpace.comap (fun ω => ω p) inferInstance
  have hG : Pairwise (fun i k : I =>
      Disjoint {p : (I × J) × ℕ | p.1.1 = i} {p | p.1.1 = k}) := by
    intro i k hik
    exact Set.disjoint_left.mpr (fun p hi hk => hik (hi.symm.trans hk))
  have hi := IndependentNoiseLabels.iIndep_grouped m
    (fun p => (measurable_pi_apply p).comap_le)
    (independent_strips (I × J)) (fun i => {p : (I × J) × ℕ | p.1.1 = i}) hG
  have he (i : I) : (⨆ p ∈ {p : (I × J) × ℕ | p.1.1 = i}, m p) =
      MeasurableSpace.comap (project (J := J) i) inferInstance := by
    rw [CylinderIndependence.comap_pi_eq_iSup]
    apply le_antisymm
    · apply iSup_le
      rintro ⟨⟨k, j⟩, n⟩
      apply iSup_le
      intro hp
      change k = i at hp
      subst k
      exact le_iSup (fun p : J × ℕ =>
        MeasurableSpace.comap (fun ω => project i ω p) inferInstance) (j, n)
    · apply iSup_le
      rintro ⟨j, n⟩
      exact le_iSup_of_le ((i, j), n) (le_iSup_of_le rfl le_rfl)
  simpa only [he] using hi

/-- The finite array of complete particle noise records has its exact product
law, including the empty-index case. -/
theorem array_map [Fintype I] :
    (law (I × J)).map (fun ω i => project i ω) =
      Measure.pi (fun _ : I => law J) := by
  have h := (iIndepFun_iff_map_fun_eq_pi_map
    (fun i : I => (measurable_project (J := J) i).aemeasurable)).mp independent_projects
  simpa only [project_map] using h

/-- The actual arrival time and height are unchanged by particle projection. -/
@[simp] theorem point_project (i : I) (j : J) (ω : Sample (I × J)) (k : ℕ × ℕ) :
    point j (project i ω) k = point (i, j) ω k := rfl

/-- A projected counting measure is exactly the original counting measure
with that particle and jump label, on every sample and every measurable set. -/
@[simp] theorem countingMeasure_project (i : I) (j : J) (ω : Sample (I × J)) :
    countingMeasure j (project i ω) = countingMeasure (i, j) ω := rfl

/-- Projection also preserves the censored noise history, including the
deterministic sentinel for every point which has not yet arrived. -/
@[simp] theorem view_project (i : I) (t : ℝ) (ω : Sample (I × J)) :
    CommonNoiseFiltration.view t (project i ω) =
      fun e => CommonNoiseFiltration.view t ω ((i, e.1), e.2) := rfl

/-- Each particle's noise history is contained in the common raw history at
the same time, on every sample. -/
theorem measurable_project_at (i : I) (t : ℝ) :
    @Measurable (Sample (I × J)) (Sample J)
      (CommonNoiseFiltration.filtration (I × J) t)
      (CommonNoiseFiltration.filtration J t) (project i) := by
  have hm : Measurable[CommonNoiseFiltration.filtration (I × J) t]
      (fun ω : Sample (I × J) => CommonNoiseFiltration.view t (project i ω)) := by
    letI : MeasurableSpace (Sample (I × J)) := CommonNoiseFiltration.filtration (I × J) t
    apply measurable_pi_lambda
    intro e
    exact (measurable_pi_apply ((i, e.1), e.2)).comp
      (CommonNoiseFiltration.measurable_view_at t)
  apply Measurable.of_comap_le
  change MeasurableSpace.comap (project i)
    (MeasurableSpace.comap (CommonNoiseFiltration.view (J := J) t) inferInstance) ≤ _
  rw [MeasurableSpace.comap_comp]
  exact hm.comap_le

end CarryingCapacity.ParticleNoiseProjection
