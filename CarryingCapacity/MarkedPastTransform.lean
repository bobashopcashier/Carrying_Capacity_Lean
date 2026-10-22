import CarryingCapacity.ClockPastObservation
import CarryingCapacity.MarkedPastProducts
import CarryingCapacity.PoissonTransform
import CarryingCapacity.MarkedObservation

/-!
# Products across the observed marked past and a future window

The clock and marks are integrated separately. Once the clock is fixed, the
past and future use disjoint mark indices. The remaining past-clock function
is measurable in the augmented count history, so the proved clock increment
independence supplies the outer factorization.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

namespace CarryingCapacity.MarkedPastTransform
open CountableJumpProcess FrozenProcess MarkedNoise MarkedPastProducts
  ClockPastObservation PoissonIncrements
open MarkedObservation

/-- Complex product integrals factor under the actual independent joint law. -/
theorem integral_mul_complex_of_independent {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f g : Ω → ℂ)
    (hf : Measurable f) (hg : Measurable g) (hfg : IndepFun f g μ) :
    (∫ ω, f ω * g ω ∂μ) = (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ) := by
  have hlaw := (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).mp hfg
  calc
    _ = ∫ p : ℂ × ℂ, p.1 * p.2 ∂Measure.map (fun ω => (f ω, g ω)) μ :=
      (integral_map_of_stronglyMeasurable (hf.prodMk hg)
        (measurable_fst.mul measurable_snd).stronglyMeasurable).symm
    _ = (∫ x : ℂ, x ∂Measure.map f μ) * (∫ y : ℂ, y ∂Measure.map g μ) := by
      rw [hlaw]
      exact integral_prod_mul (fun x : ℂ => x) (fun y : ℂ => y)
    _ = _ := by
      congr 1
      · exact integral_map_of_stronglyMeasurable hf
          (show StronglyMeasurable (fun x : ℂ => x) from measurable_id.stronglyMeasurable)
      · exact integral_map_of_stronglyMeasurable hg
          (show StronglyMeasurable (fun x : ℂ => x) from measurable_id.stronglyMeasurable)

/-- The actual future block of marks in `(s,s+t]`. -/
def futureTimeProduct (s t : ℝ) (g : ℝ → ℂ) (ω : StripSample) : ℂ :=
  futureProduct (proposalCount ω.1 s) (proposalCount ω.1 (s+t)) g ω.2

theorem measurable_futureTimeProduct (s t : ℝ) (g : ℝ → ℂ) (hg : Measurable g) :
    Measurable (futureTimeProduct s t g) := by
  have h : Measurable (fun p : (ℕ → ℝ) × (ℕ × ℕ) =>
      futureProduct p.2.1 p.2.2 g p.1) :=
    measurable_from_prod_countable (fun p => measurable_futureProduct p.1 p.2 g hg)
  exact h.comp (measurable_snd.prodMk
    (((measurable_proposalCount s).comp measurable_fst).prodMk
      ((measurable_proposalCount (s+t)).comp measurable_fst)))

theorem norm_futureTimeProduct_le_one (s t : ℝ) (g : ℝ → ℂ)
    (hg : ∀ x, ‖g x‖ ≤ 1) (ω : StripSample) : ‖futureTimeProduct s t g ω‖ ≤ 1 :=
  norm_futureProduct_le_one _ _ g hg _

theorem integrable_futureTimeProduct (s t : ℝ) (g : ℝ → ℂ)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ 1) :
    Integrable (futureTimeProduct s t g) stripLaw :=
  (integrable_const (1 : ℝ)).mono' (measurable_futureTimeProduct s t g hg).aestronglyMeasurable
    (Eventually.of_forall (norm_futureTimeProduct_le_one s t g hb))

/-- A genuine function of the observed clock past factors from the next increment. -/
theorem integral_past_clock_pow (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (f : ClockSpace → ℂ) (hf : Measurable f)
    (hpast : Measurable[augmentedPast 1 (by norm_num) s] f) (z : ℂ) :
    (∫ ω, f ω * z ^ increment ω s t ∂waitingTimeLaw 1 (by norm_num)) =
      (∫ ω, f ω ∂waitingTimeLaw 1 (by norm_num)) *
        Complex.exp ((t : ℂ) * (z-1)) := by
  have hi := (independent_function_increment 1 (by norm_num) s t hs ht f hpast).comp
    measurable_id (measurable_of_countable (fun n : ℕ => z^n))
  have hm : Measurable (fun ω : ClockSpace => z ^ increment ω s t) :=
    (measurable_of_countable _).comp (measurable_increment s t)
  rw [integral_mul_complex_of_independent _ _ _ hf hm hi,
    PoissonTransform.integral_increment_pow 1 (by norm_num) s t hs ht]
  simp

theorem integrable_observedProduct_mul_future (s t : ℝ) (K : Finset ℕ)
    (F : ℕ → (ℝ × ℝ) → ℂ) (hF : ∀ k, Measurable (F k))
    (hFb : ∀ k p, ‖F k p‖ ≤ 1) (g : ℝ → ℂ) (hg : Measurable g)
    (hgb : ∀ x, ‖g x‖ ≤ 1) :
    Integrable (fun ω => observedProduct s K F ω * futureTimeProduct s t g ω) stripLaw := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_observedProduct s K F hF).mul
      (measurable_futureTimeProduct s t g hg)).aestronglyMeasurable
  filter_upwards [] with ω
  rw [norm_mul]
  exact (mul_le_mul (norm_observedProduct_le_one s K F hFb ω)
    (norm_futureTimeProduct_le_one s t g hgb ω) (norm_nonneg _) zero_le_one).trans_eq
      (mul_one 1)

/-- The actual observed past factors from the future mark transform.
The past test functions can depend on both arrival times and marks. -/
theorem integral_observedProduct_mul_future (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (K : Finset ℕ) (F : ℕ → (ℝ × ℝ) → ℂ) (hF : ∀ k, Measurable (F k))
    (hFb : ∀ k p, ‖F k p‖ ≤ 1) (g : ℝ → ℂ) (hg : Measurable g)
    (hgb : ∀ x, ‖g x‖ ≤ 1) :
    (∫ ω, observedProduct s K F ω * futureTimeProduct s t g ω ∂stripLaw) =
      (∫ ω, observedProduct s K F ω ∂stripLaw) *
        Complex.exp ((t : ℂ) * ((∫ x, g x ∂uniformUnit)-1)) := by
  rw [stripLaw, integral_prod _
    (integrable_observedProduct_mul_future s t K F hF hFb g hg hgb)]
  have he : (∫ ω, ∫ v, observedProduct s K F (ω,v) *
      futureTimeProduct s t g (ω,v) ∂unitMarksLaw ∂waitingTimeLaw 1 (by norm_num)) =
      ∫ ω, clockMean s K F ω * (∫ x, g x ∂uniformUnit) ^ increment ω s t
        ∂waitingTimeLaw 1 (by norm_num) := by
    apply integral_congr_ae
    filter_upwards [ae_locally_finite 1 (by norm_num), ae_arrival_tendsto 1 (by norm_num)]
      with ω hω hd
    exact integral_observedProduct_future_marks s t hs K F hF g hg ω hω.1 hd
  rw [he, integral_past_clock_pow s t hs ht _ (measurable_clockMean s K F hF)
    (measurable_clockMean_augmentedPast 1 (by norm_num) s hs K F hF)]
  rw [← integral_observedProduct s K F hF hFb]
  rfl

/-- The future mark transform, including windows starting at a positive time. -/
theorem integral_futureTimeProduct (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (g : ℝ → ℂ) (hg : Measurable g) (hgb : ∀ x, ‖g x‖ ≤ 1) :
    (∫ ω, futureTimeProduct s t g ω ∂stripLaw) =
      Complex.exp ((t : ℂ) * ((∫ x, g x ∂uniformUnit)-1)) := by
  simpa [observedProduct] using integral_observedProduct_mul_future s t hs ht ∅
    (fun _ _ => 1) (fun _ => measurable_const) (by intros; simp) g hg hgb

end CarryingCapacity.MarkedPastTransform
