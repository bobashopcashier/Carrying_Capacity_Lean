import CarryingCapacity.TimeDependentCountingIdentity
import CarryingCapacity.SynchronousPositiveIncrement

/-!
# Positive distance increments on a common chronological list

Two frozen recursions use exactly the same marked proposals. Their paired
finite recursion has the original runs as its two projections. Telescoping
bounds the terminal distance by its initial value and the sum of positive
increments. On a horizon where both actual left states remain active, those
increments are the unrestricted synchronous threshold increments. Finite
atomic box support proves integrability and identifies the sum with the
actual counting measures. No coupling identity is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal

namespace CarryingCapacity.SynchronousFrozenCounting
open Freezing MarkedNoise ChronologicalEvents TimeDependentFrozenProcess TimeDependentJumpIdentity
open SynchronousPositiveIncrement FrozenCountingIdentity

variable {E J M : Type*} [DecidableEq E]

/-- A pair of genuine finite recursions driven by each common proposal. -/
def pairedRun (activeX activeY : Finset E) (jump : J → E → E)
    (decodeX decodeY : E → M → Option J) : E × E → List M → E × E
  | z, [] => z
  | z, a :: l => pairedRun activeX activeY jump decodeX decodeY
      (frozenStep activeX jump decodeX z.1 a, frozenStep activeY jump decodeY z.2 a) l

theorem pairedRun_fst (activeX activeY : Finset E) (jump : J → E → E)
    (decodeX decodeY : E → M → Option J) (z : E × E) (l : List M) :
    (pairedRun activeX activeY jump decodeX decodeY z l).1 = run activeX jump decodeX z.1 l := by
  induction l generalizing z with
  | nil => rfl
  | cons a l ih => exact ih _

theorem pairedRun_snd (activeX activeY : Finset E) (jump : J → E → E)
    (decodeX decodeY : E → M → Option J) (z : E × E) (l : List M) :
    (pairedRun activeX activeY jump decodeX decodeY z l).2 = run activeY jump decodeY z.2 l := by
  induction l generalizing z with
  | nil => rfl
  | cons a l ih => exact ih _

/-- Deterministic positive-increment domination for the two actual finite runs. -/
theorem run_distance_le (activeX activeY : Finset E) (jump : J → E → E)
    (decodeX decodeY : E → M → Option J) (ρ : E → E → ℝ)
    (x y : E) (l : List M) :
    ρ (run activeX jump decodeX x l) (run activeY jump decodeY y l) ≤ ρ x y +
      ∑ n : Fin l.length,
        max (ρ (frozenStep activeX jump decodeX (run activeX jump decodeX x (l.take n.val)) (l.get n))
          (frozenStep activeY jump decodeY (run activeY jump decodeY y (l.take n.val)) (l.get n)) -
          ρ (run activeX jump decodeX x (l.take n.val)) (run activeY jump decodeY y (l.take n.val))) 0 := by
  simp_rw [← FrozenJumpIdentity.run_take_succ]
  have h := le_initial_add_positive_increments
    (fun n => ρ (run activeX jump decodeX x (l.take n))
      (run activeY jump decodeY y (l.take n))) l.length
  rw [Finset.sum_range] at h
  simpa only [List.take_length, List.take_zero, run] using h

variable (activeX activeY : Finset E) (jump : J → E → E)
  (rateX rateY : J → ℝ → E → ℝ) (ρ : E → E → ℝ)

/-- The synchronous increment evaluated at the two actual frozen left states. -/
def field (C : ℝ) (x y : E) (ω : MarkedNoise.Sample J) (j : J) (q : ℝ × ℝ) : ℝ :=
  positiveIncrement ρ jump j
    (rateX j q.1 (leftProcess activeX jump rateX C x ω q.1))
    (rateY j q.1 (leftProcess activeY jump rateY C y ω q.1))
    (leftProcess activeX jump rateX C x ω q.1)
    (leftProcess activeY jump rateY C y ω q.1) q.2

/-- Restriction to the actual common finite time-height box. -/
def boxField (C : ℝ) (x y : E) (ω : MarkedNoise.Sample J) (j : J) (T : ℝ) : ℝ × ℝ → ℝ :=
  (Iic T ×ˢ Iic C).indicator (field activeX activeY jump rateX rateY ρ C x y ω j)

theorem field_nonneg (C : ℝ) (x y : E) (ω : MarkedNoise.Sample J) (j : J) (q : ℝ × ℝ) :
    0 ≤ field activeX activeY jump rateX rateY ρ C x y ω j q := le_max_right _ _

theorem boxField_nonneg (C : ℝ) (x y : E) (ω : MarkedNoise.Sample J) (j : J) (T : ℝ) (q : ℝ × ℝ) :
    0 ≤ boxField activeX activeY jump rateX rateY ρ C x y ω j T q :=
  Set.indicator_nonneg (fun q _ => field_nonneg activeX activeY jump rateX rateY ρ C x y ω j q) q

theorem step_positiveIncrement (ω : MarkedNoise.Sample J) (x y : E)
    (hx : x ∈ activeX) (hy : y ∈ activeY) (a : Event J) :
    max (ρ (frozenStep activeX jump (eventDecode rateX ω) x a)
      (frozenStep activeY jump (eventDecode rateY ω) y a) - ρ x y) 0 =
      positiveIncrement ρ jump a.1 (rateX a.1 (point a.1 ω a.2).1 x)
        (rateY a.1 (point a.1 ω a.2).1 y) x y (point a.1 ω a.2).2 := by
  by_cases hX : (point a.1 ω a.2).2 ≤ rateX a.1 (point a.1 ω a.2).1 x <;>
    by_cases hY : (point a.1 ω a.2).2 ≤ rateY a.1 (point a.1 ω a.2).1 y <;>
      simp [frozenStep, eventDecode, hx, hy, hX, hY, positiveIncrement, pairUpdate]

variable [Fintype J]

/-- The common box has finite actual atomic support, so the real integrals exist. -/
theorem ae_integrable_boxField : ∀ᵐ ω ∂MarkedNoise.law J, ∀ C x y j T,
    Integrable (boxField activeX activeY jump rateX rateY ρ C x y ω j T)
      (countingMeasure j ω) := by
  filter_upwards [ae_integrable_box_weights (J := J)] with ω hω
  exact fun C x y j T => hω T C j _

/-- The actual terminal distance is dominated by its initial value plus
positive synchronous increments in the common box. Activity of the left states
is a local condition, later supplied by genuine first-exit bounds. -/
theorem ae_distance_le_integral : ∀ᵐ ω ∂MarkedNoise.law J, ∀ C x y T,
    (∀ s ∈ Ioc (0 : ℝ) T, leftProcess activeX jump rateX C x ω s ∈ activeX) →
    (∀ s ∈ Ioc (0 : ℝ) T, leftProcess activeY jump rateY C y ω s ∈ activeY) →
    ρ (process activeX jump rateX C x ω T) (process activeY jump rateY C y ω T) ≤
      ρ x y + ∑ j : J, ∫ q, boxField activeX activeY jump rateX rateY ρ C x y ω j T q
        ∂countingMeasure j ω := by
  filter_upwards [TimeDependentJumpIdentity.ae_leftProcess_at_event activeX jump rateX,
    TimeDependentJumpIdentity.ae_leftProcess_at_event activeY jump rateY,
    ae_integral_box_eq_sum (J := J), ae_boxedList_mem (J := J),
    MarkedNoise.ae_positive_points (J := J)] with ω hleftX hleftY hint hmem hpos
  intro C x y T hX hY
  have h := run_distance_le activeX activeY jump (eventDecode rateX ω) (eventDecode rateY ω)
    ρ x y (boxedList (ω,T,C))
  change ρ (process activeX jump rateX C x ω T) (process activeY jump rateY C y ω T) ≤ _ at h
  refine h.trans_eq ?_
  congr 1
  rw [show (∑ j : J, ∫ q, boxField activeX activeY jump rateX rateY ρ C x y ω j T q
      ∂countingMeasure j ω) = ∑ n : Fin (boxedList (ω,T,C)).length,
        let a := (boxedList (ω,T,C)).get n
        field activeX activeY jump rateX rateY ρ C x y ω a.1 (point a.1 ω a.2) from hint T C _]
  apply Finset.sum_congr rfl
  intro n _
  let a := (boxedList (ω,T,C)).get n
  have ha : (point a.1 ω a.2).1 ∈ Ioc (0 : ℝ) T :=
    ⟨(hpos a.1 a.2).1, ((hmem T C a).mp (List.get_mem _ n)).1⟩
  rw [← hleftX C x T n, ← hleftY C y T n]
  exact step_positiveIncrement activeX activeY jump rateX rateY ρ ω _ _
    (hX _ ha) (hY _ ha) a

/-- Extended nonnegative form of the actual paired path bound. -/
theorem ae_ofReal_distance_le_lintegral (hρ : ∀ x y, 0 ≤ ρ x y) :
    ∀ᵐ ω ∂MarkedNoise.law J, ∀ C x y T,
    (∀ s ∈ Ioc (0 : ℝ) T, leftProcess activeX jump rateX C x ω s ∈ activeX) →
    (∀ s ∈ Ioc (0 : ℝ) T, leftProcess activeY jump rateY C y ω s ∈ activeY) →
    ENNReal.ofReal (ρ (process activeX jump rateX C x ω T) (process activeY jump rateY C y ω T)) ≤
      ENNReal.ofReal (ρ x y) + ∑ j : J, ∫⁻ q,
        ENNReal.ofReal (boxField activeX activeY jump rateX rateY ρ C x y ω j T q)
          ∂countingMeasure j ω := by
  filter_upwards [ae_distance_le_integral activeX activeY jump rateX rateY ρ,
    ae_integrable_boxField activeX activeY jump rateX rateY ρ] with ω hd hi
  intro C x y T hX hY
  have hn (j : J) : 0 ≤ ∫ q, boxField activeX activeY jump rateX rateY ρ C x y ω j T q
      ∂countingMeasure j ω := integral_nonneg (boxField_nonneg activeX activeY jump rateX rateY ρ C x y ω j T)
  have h := ENNReal.ofReal_le_ofReal (hd C x y T hX hY)
  rw [ENNReal.ofReal_add (hρ x y) (Finset.sum_nonneg (fun j _ => hn j)),
    ENNReal.ofReal_sum_of_nonneg (fun j _ => hn j)] at h
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact (ofReal_integral_eq_lintegral_ofReal (hi C x y j T)
    (Eventually.of_forall (boxField_nonneg activeX activeY jump rateX rateY ρ C x y ω j T))).symm

end CarryingCapacity.SynchronousFrozenCounting
