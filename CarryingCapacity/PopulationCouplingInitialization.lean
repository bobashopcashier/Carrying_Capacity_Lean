import CarryingCapacity.InitialCoupling
import CarryingCapacity.NonlinearParticleConfiguration
import CarryingCapacity.PopulationCouplingAlgebra

/-!
# Initial laws for the actual population comparison

The optimal exchangeable coupling preserves the full original vector law and
the full independent vector law. Consequently it also preserves the genuine
initial Lyapunov integrability and expectations needed by the constructed
processes and their uniform exit estimate. No new initial moment assumption is
introduced when passing to the paired probability space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Classical BigOperators Topology ENNReal

namespace CarryingCapacity.PopulationCouplingInitialization
open ConfigurationLocalization PopulationCouplingAlgebra

variable {N D : ℕ} {κ : MomentScale} {q : Rates D (MomentLaw κ D)}
  (control : LyapunovControl κ q)

/-- Paired initial records on which both actual configurations are constructed. -/
abbrev Record (N D : ℕ) := Fin N → State D × State D

def left (a : Record N D) : Configuration N D := fun i => (a i).1
def right (a : Record N D) : Configuration N D := fun i => (a i).2

theorem measurable_left : Measurable (left (N := N) (D := D)) := measurable_of_countable _
theorem measurable_right : Measurable (right (N := N) (D := D)) := measurable_of_countable _

/-- Equality of full vector marginals transfers the actual Lyapunov moment. -/
theorem integrable_initial_of_map {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
    (γ : Measure A) (P : Measure Ω) (initial : A → Configuration N D)
    (z : Ω → Configuration N D) (hi : Measurable initial) (hz : Measurable z)
    (hmap : γ.map initial = P.map z)
    (hΨ : Integrable (fun ω => lyapunov control (z ω)) P) :
    Integrable (fun a => lyapunov control (initial a)) γ := by
  have hm := (measurable_of_countable (lyapunov control (N := N))).stronglyMeasurable
  apply (integrable_map_measure hm.aestronglyMeasurable hi.aemeasurable).mp
  rw [hmap]
  exact (integrable_map_measure hm.aestronglyMeasurable hz.aemeasurable).mpr hΨ

/-- The actual averaged initial Lyapunov expectation is unchanged. -/
theorem integral_initial_of_map {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
    (γ : Measure A) (P : Measure Ω) (initial : A → Configuration N D)
    (z : Ω → Configuration N D) (hi : Measurable initial) (hz : Measurable z)
    (hmap : γ.map initial = P.map z) :
    (∫ a, lyapunov control (initial a) ∂γ) = ∫ ω, lyapunov control (z ω) ∂P := by
  rw [← integral_map_of_stronglyMeasurable hi (measurable_of_countable _).stronglyMeasurable,
    hmap, integral_map_of_stronglyMeasurable hz (measurable_of_countable _).stronglyMeasurable]

/-- The independent marginal has the same expected empirical Lyapunov value
for every positive population size. -/
theorem integral_initial_iid {A : Type*} [MeasurableSpace A]
    (hN : 0 < N) (ν : MomentLaw κ D) (hMoment : Integrable control.function ν.measure)
    (γ : Measure A) (initial : A → Configuration N D) (hi : Measurable initial)
    (hmap : γ.map initial = Measure.pi (fun _ : Fin N => ν.measure)) :
    (∫ a, lyapunov control (initial a) ∂γ) = ∫ x, control.function x ∂ν.measure := by
  letI : IsProbabilityMeasure ν.measure := ν.probability
  have he (i : Fin N) : γ.map (fun a => initial a i) = ν.measure := by
    change γ.map ((fun z : Configuration N D => z i) ∘ initial) = _
    rw [← Measure.map_map (measurable_pi_apply i) hi, hmap,
      ParticleInputRecords.pi_coordinate_map]
  have hint (i : Fin N) : Integrable (fun a => control.function (initial a i)) γ :=
    NonlinearParticleConfiguration.integrable_initial_coordinate control ν hMoment initial hi γ hmap i
  have heq (i : Fin N) : (∫ a, control.function (initial a i) ∂γ) =
      ∫ x, control.function x ∂ν.measure := by
    have hh : (∫ x, control.function x ∂γ.map (fun a => initial a i)) =
        ∫ a, control.function (initial a i) ∂γ :=
      integral_map_of_stronglyMeasurable ((measurable_pi_apply i).comp hi)
        (measurable_of_countable _).stronglyMeasurable
    rw [he] at hh
    exact hh.symm
  unfold lyapunov FiniteGenerator.empiricalMean
  rw [integral_const_mul, integral_finset_sum _ (fun i _ => hint i)]
  simp only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.ne_of_gt hN), one_mul]

/-- The original initialization hypotheses supply a coupled family with all
initial moments required by the actual stopped comparison. The convergence
of expected pairing errors is derived by the initial-coupling theorem. -/
theorem exists_initialization {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : MomentLaw κ D)
    (hMoment : Integrable control.function ν.measure)
    (z : ∀ n, Ω → Configuration (n + 1) D) (hz : ∀ n, Measurable (z n))
    (hex : ∀ n, ExchangeableMatching.ExchangeableLaw (P.map (z n)))
    (hΨ : ∀ n, Integrable (fun ω => lyapunov control (z n ω)) P)
    (C : ℝ) (hbound : ∀ n, (∫ ω, lyapunov control (z n ω) ∂P) ≤ C)
    (hconv : TendstoInMeasure P
      (fun n ω => wasserstein (empiricalLaw κ (Nat.succ_pos n) (z n ω)) ν) atTop 0) :
    ∃ γ : ∀ n, Measure (Record (n + 1) D),
      (∀ n, IsProbabilityMeasure (γ n)) ∧
      (∀ n, ExchangeableMatching.ExchangeableLaw (γ n)) ∧
      (∀ n, (γ n).map left = P.map (z n)) ∧
      (∀ n, (γ n).map right = Measure.pi (fun _ : Fin (n + 1) => ν.measure)) ∧
      (∀ n, Integrable (fun a => lyapunov control (left a)) (γ n)) ∧
      (∀ n, Integrable (fun a => lyapunov control (right a)) (γ n)) ∧
      (∀ n, (∫ a, lyapunov control (left a) ∂γ n) ≤
        max C (∫ x, control.function x ∂ν.measure)) ∧
      (∀ n, (∫ a, lyapunov control (right a) ∂γ n) ≤
        max C (∫ x, control.function x ∂ν.measure)) ∧
      Tendsto (fun n => ∫ a, meanDistance κ (left a) (right a) ∂γ n) atTop (𝓝 0) := by
  obtain ⟨γ, hp, he, hl, hr, _hi, _hopt, hlim⟩ :=
    InitialCoupling.exists_initial_coupling P ν control.function control.dominates
      control.superlinear hMoment z hz hex hΨ C hbound hconv
  refine ⟨γ, hp, he, hl, hr, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact integrable_initial_of_map control (γ n) P left (z n) measurable_left (hz n) (hl n) (hΨ n)
  · intro n
    exact NonlinearParticleConfiguration.integrable_initial_lyapunov control ν hMoment
      right measurable_right (γ n) (hr n)
  · intro n
    rw [integral_initial_of_map control (γ n) P left (z n) measurable_left (hz n) (hl n)]
    exact (hbound n).trans (le_max_left _ _)
  · intro n
    rw [integral_initial_iid control (Nat.succ_pos n) ν hMoment (γ n) right measurable_right (hr n)]
    exact le_max_right _ _
  · exact hlim

end CarryingCapacity.PopulationCouplingInitialization
