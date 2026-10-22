import CarryingCapacity.FiniteGenerator
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.ProductMeasure

/-!
# Integrable-observable laws of large numbers for independent finite rows

Every finite row is transferred by its exact product law to an initial segment
of a canonical infinite iid sequence. The strong law on that auxiliary space
then gives centered tail convergence on the original, possibly different row
spaces. No compatibility or independence between different rows is imposed.
The observable only needs to be integrable, and the row maps may be merely
almost-everywhere measurable for their actual row measures.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical BigOperators ENNReal Topology

namespace CarryingCapacity.IndependentArrayLLN
open FiniteGenerator

variable {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]

/-- Auxiliary infinite iid records with the prescribed single-record law. -/
def canonicalLaw : Measure (ℕ → E) := Measure.infinitePi (fun _ : ℕ => μ)

instance canonicalLaw_probability : IsProbabilityMeasure (canonicalLaw μ) := by
  unfold canonicalLaw
  infer_instance

theorem canonical_coordinate_event (i : ℕ) (s : Set E) (hs : MeasurableSet s) :
    canonicalLaw μ {ω | ω i ∈ s} = μ s := by
  have he : {ω : ℕ → E | ω i ∈ s} = Set.pi ({i} : Finset ℕ) (fun _ => s) := by
    ext ω
    simp
  rw [he, canonicalLaw, Measure.infinitePi_pi _ (fun _ _ => hs)]
  simp

theorem canonical_coordinate_map (i : ℕ) :
    (canonicalLaw μ).map (fun ω => ω i) = μ := by
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  exact canonical_coordinate_event μ i s hs

/-- Complete mutual independence is derived from the actual infinite product. -/
theorem canonical_independent :
    iIndepFun (fun i (ω : ℕ → E) => ω i) (canonicalLaw μ) := by
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S sets hs
  have he : (⋂ i ∈ S, (fun ω : ℕ → E => ω i) ⁻¹' sets i) = Set.pi S sets := by
    ext ω
    simp
  rw [he, canonicalLaw, Measure.infinitePi_pi _ hs]
  exact Finset.prod_congr rfl (fun i hi => (canonical_coordinate_event μ i (sets i) (hs i hi)).symm)

/-- Each positive-length canonical prefix has the exact finite product law. -/
theorem canonical_vector_map (n : ℕ) :
    (canonicalLaw μ).map (fun ω (i : Fin (n + 1)) => ω i.val) =
      Measure.pi (fun _ : Fin (n + 1) => μ) := by
  have hi : iIndepFun (fun i : Fin (n + 1) => fun ω : ℕ → E => ω i.val) (canonicalLaw μ) :=
    (canonical_independent μ).precomp Fin.val_injective
  have hm := (iIndepFun_iff_map_fun_eq_pi_map
    (fun i : Fin (n + 1) => (measurable_pi_apply i.val).aemeasurable)).mp hi
  simpa only [canonical_coordinate_map] using hm

theorem finite_coordinate_map (n : ℕ) (i : Fin (n + 1)) :
    (Measure.pi (fun _ : Fin (n + 1) => μ)).map (fun z => z i) = μ := by
  rw [← canonical_vector_map μ n]
  have hm : Measurable (fun ω : ℕ → E => fun j : Fin (n + 1) => ω j.val) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply j.val)
  rw [Measure.map_map (measurable_pi_apply i) hm]
  exact canonical_coordinate_map μ i.val

variable (f : E → ℝ) (hf : Integrable f μ)
include hf

/-- Integrability of the finite empirical observable requires no global
measurability representative of the original observable. -/
theorem integrable_finite_mean (n : ℕ) :
    Integrable (empiricalMean (N := n + 1) f) (Measure.pi (fun _ : Fin (n + 1) => μ)) := by
  have hi (i : Fin (n + 1)) : Integrable (fun z : Fin (n + 1) → E => f (z i))
      (Measure.pi (fun _ : Fin (n + 1) => μ)) := by
    have hh : Integrable f ((Measure.pi (fun _ : Fin (n + 1) => μ)).map (fun z => z i)) := by
      rwa [finite_coordinate_map]
    exact hh.comp_measurable (measurable_pi_apply i)
  exact (integrable_finset_sum _ (fun i _ => hi i)).const_mul _

theorem integrable_canonical_mean (n : ℕ) :
    Integrable (fun ω : ℕ → E => empiricalMean f (fun i : Fin (n + 1) => ω i.val))
      (canonicalLaw μ) := by
  have hh : Integrable (empiricalMean (N := n + 1) f)
      ((canonicalLaw μ).map (fun ω (i : Fin (n + 1)) => ω i.val)) := by
    rw [canonical_vector_map]
    exact integrable_finite_mean μ f hf n
  exact hh.comp_measurable (measurable_pi_lambda _ (fun i => measurable_pi_apply i.val))

/-- The canonical strong law allows an arbitrary integrable real observable,
including one that is only almost-everywhere measurable under μ. -/
theorem canonical_mean_strongLaw : ∀ᵐ ω ∂canonicalLaw μ,
    Tendsto (fun n => empiricalMean f (fun i : Fin (n + 1) => ω i.val))
      atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hfi (i : ℕ) : Integrable f ((canonicalLaw μ).map (fun ω => ω i)) := by
    rwa [canonical_coordinate_map]
  have hi := (canonical_independent μ).comp₀ (fun _ => f)
    (fun i => (measurable_pi_apply i).aemeasurable) (fun i => (hfi i).aemeasurable)
  have hid (i : ℕ) : IdentDistrib (fun ω : ℕ → E => f (ω i)) (fun ω => f (ω 0))
      (canonicalLaw μ) (canonicalLaw μ) := by
    have hcoord : IdentDistrib (fun ω : ℕ → E => ω i) (fun ω => ω 0)
        (canonicalLaw μ) (canonicalLaw μ) :=
      ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
        (canonical_coordinate_map μ i).trans (canonical_coordinate_map μ 0).symm⟩
    exact hcoord.comp_of_aemeasurable (hfi i).aemeasurable
  have heq : (∫ ω : ℕ → E, f (ω 0) ∂canonicalLaw μ) = ∫ x, f x ∂μ := by
    have hh := integral_map (μ := canonicalLaw μ) (φ := fun ω : ℕ → E => ω 0)
      (f := f) (measurable_pi_apply 0).aemeasurable (hfi 0).aestronglyMeasurable
    rw [canonical_coordinate_map] at hh
    exact hh.symm
  have hs := strong_law_ae_real (fun i (ω : ℕ → E) => f (ω i))
    ((hfi 0).comp_measurable (measurable_pi_apply 0)) (fun i j hij => hi.indepFun hij) hid
  filter_upwards [hs] with ω hω
  have hh := hω.comp (tendsto_add_atTop_nat 1)
  have hmean (n : ℕ) : empiricalMean f (fun i : Fin (n + 1) => ω i.val) =
      (∑ i ∈ Finset.range (n + 1), f (ω i)) / (n + 1) := by
    unfold empiricalMean
    rw [Fin.sum_univ_eq_sum_range (fun i => f (ω i))]
    simp only [div_eq_mul_inv, mul_comm, Nat.cast_add, Nat.cast_one]
  simpa only [hmean, heq, Function.comp_def, Nat.cast_add, Nat.cast_one] using hh

/-- Almost-sure canonical convergence supplies actual convergence in measure. -/
theorem canonical_mean_tendstoInMeasure :
    TendstoInMeasure (canonicalLaw μ)
      (fun n ω => empiricalMean f (fun i : Fin (n + 1) => ω i.val))
      atTop (fun _ => ∫ x, f x ∂μ) :=
  tendstoInMeasure_of_tendsto_ae (fun n => (integrable_canonical_mean μ f hf n).aestronglyMeasurable)
    (canonical_mean_strongLaw μ f hf)

section Row
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
  (n : ℕ) (Y : Ω → Fin (n + 1) → E) (hY : AEMeasurable Y P)
  (hlaw : P.map Y = Measure.pi (fun _ : Fin (n + 1) => μ))
include hY hlaw

/-- Exact finite-vector law transfers the entire empirical observable law;
integrability supplies the required AE composition measurability. -/
theorem mean_identDistrib :
    IdentDistrib (fun ω => empiricalMean f (Y ω))
      (fun ω : ℕ → E => empiricalMean f (fun i : Fin (n + 1) => ω i.val))
      P (canonicalLaw μ) := by
  have hv : IdentDistrib Y (fun ω : ℕ → E => fun i : Fin (n + 1) => ω i.val)
      P (canonicalLaw μ) :=
    ⟨hY, (measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)).aemeasurable,
      hlaw.trans (canonical_vector_map μ n).symm⟩
  have hm : AEMeasurable (empiricalMean (N := n + 1) f) (P.map Y) := by
    rw [hlaw]
    exact (integrable_finite_mean μ f hf n).aemeasurable
  exact hv.comp_of_aemeasurable hm

/-- Actual row averages are genuinely integrable on their own row spaces. -/
theorem integrable_mean : Integrable (fun ω => empiricalMean f (Y ω)) P :=
  (mean_identDistrib μ f hf P n Y hY hlaw).integrable_iff.mpr (integrable_canonical_mean μ f hf n)

/-- Exact equality of centered tail masses with the canonical iid prefix. -/
theorem centered_tail_eq (ε : ℝ) :
    P {ω | ε ≤ |empiricalMean f (Y ω) - ∫ x, f x ∂μ|} =
      canonicalLaw μ {ω | ε ≤ |empiricalMean f (fun i : Fin (n + 1) => ω i.val) - ∫ x, f x ∂μ|} :=
  (mean_identDistrib μ f hf P n Y hY hlaw).measure_mem_eq
    (measurableSet_le measurable_const ((measurable_id.sub_const _).abs))

end Row

section Array
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (P : ∀ n, Measure (Ω n))
  (Y : ∀ n, Ω n → Fin (n + 1) → E) (hY : ∀ n, AEMeasurable (Y n) (P n))
  (hlaw : ∀ n, (P n).map (Y n) = Measure.pi (fun _ : Fin (n + 1) => μ))
include hY hlaw

/-- Centered empirical means converge in probability for arbitrary iid rows.
Different population sizes may have different probability spaces, without any
cross-row dependence or compatibility premise. -/
theorem measure_centered_mean_ge_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P n {ω | ε ≤ |empiricalMean f (Y n ω) - ∫ x, f x ∂μ|}) atTop (𝓝 0) := by
  have he (n : ℕ) := centered_tail_eq μ f hf (P n) n (Y n) (hY n) (hlaw n) ε
  simp_rw [he]
  simpa only [Real.dist_eq] using (canonical_mean_tendstoInMeasure μ f hf) ε hε

/-- Strict centered tails inherit the same actual finite-row limit. -/
theorem measure_centered_mean_gt_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P n {ω | ε < |empiricalMean f (Y n ω) - ∫ x, f x ∂μ|}) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (measure_centered_mean_ge_tendsto_zero μ f hf P Y hY hlaw ε hε) (fun _ => zero_le _)
  intro n
  apply measure_mono
  intro ω hω
  change ε < |empiricalMean f (Y n ω) - ∫ x, f x ∂μ| at hω
  exact hω.le

/-- The real tail masses also tend to zero, by continuity of `toReal` at zero. -/
theorem probability_centered_mean_ge_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (P n).real {ω | ε ≤ |empiricalMean f (Y n ω) - ∫ x, f x ∂μ|})
      atTop (𝓝 0) := by
  simpa only [ENNReal.toReal_zero, Measure.real, Function.comp_def] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (measure_centered_mean_ge_tendsto_zero μ f hf P Y hY hlaw ε hε)

/-- In particular, an integrable nonnegative variation observable has no
asymptotic upper tail above its own mean plus any positive tolerance. -/
theorem measure_mean_gt_integral_add_tendsto_zero (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => P n {ω | (∫ x, f x ∂μ) + ε < empiricalMean f (Y n ω)})
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (measure_centered_mean_gt_tendsto_zero μ f hf P Y hY hlaw ε hε) (fun _ => zero_le _)
  apply fun n => measure_mono ?_
  intro ω hω
  change (∫ x, f x ∂μ) + ε < empiricalMean f (Y n ω) at hω
  exact (by linarith : ε < empiricalMean f (Y n ω) - ∫ x, f x ∂μ).trans_le (le_abs_self _)

end Array
end CarryingCapacity.IndependentArrayLLN
