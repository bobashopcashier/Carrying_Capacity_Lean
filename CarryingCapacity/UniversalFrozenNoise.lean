import CarryingCapacity.SynchronousFrozenCounting

/-!
# A coefficient-independent event for actual frozen thinning equations

All active sets, jump maps, time-dependent rate functions and test functions
are quantified after the almost-everywhere noise event. The event is built
only from chronological finite-box facts. Thus coefficients may subsequently
be selected from a random environment on the same sample, without taking an
uncountable intersection of coefficient-dependent probability-one events.
No measurability or boundedness of the substituted rates is needed for these
finite-box pathwise identities.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology ENNReal

namespace CarryingCapacity.UniversalFrozenNoise
open MarkedNoise ChronologicalEvents CommonFrozenRegularity Freezing
  TimeDependentFrozenProcess TimeDependentJumpIdentity FrozenCountingIdentity
  SynchronousFrozenCounting

variable {E J : Type*} [DecidableEq E] [Fintype J]

/-- One noise event works for every frozen decoder and every active set. -/
theorem ae_left_constant : ∀ᵐ ω ∂law J,
    ∀ (G : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ) C x t,
      ∃ b, b < t ∧ ∀ u ∈ Ico b t,
        process G jump rate C x ω u = leftProcess G jump rate C x ω t := by
  filter_upwards [ae_boxedList_time_filter (J := J)] with ω hω
  intro G jump rate C x t
  obtain ⟨b, hb, hl⟩ := filter_time_left_constant
    (fun e : Event J => (point e.1 ω e.2).1) (boxedList (ω,t,C)) t
  refine ⟨b, hb, ?_⟩
  intro u hu
  unfold process runBox leftProcess
  rw [← hω u t C hu.2.le, hl u hu]

theorem ae_right_constant : ∀ᵐ ω ∂law J,
    ∀ (G : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ) C x t,
      ∃ b, t < b ∧ ∀ u ∈ Ico t b,
        process G jump rate C x ω u = process G jump rate C x ω t := by
  filter_upwards [ae_boxedList_right_constant (J := J)] with ω hω
  intro G jump rate C x t
  obtain ⟨b, hb, hl⟩ := hω C t
  exact ⟨b, hb, fun u hu => by simp only [process, runBox, hl u hu]⟩

theorem ae_zero : ∀ᵐ ω ∂law J,
    ∀ (G : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ) C x,
      process G jump rate C x ω 0 = x := by
  filter_upwards [ae_boxedList_zero (J := J)] with ω hω
  intro G jump rate C x
  simp only [process, runBox, hω C, run]

theorem ae_left_at_event : ∀ᵐ ω ∂law J,
    ∀ (G : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ) C x T
      (n : Fin (boxedList (ω,T,C)).length),
      leftProcess G jump rate C x ω (point ((boxedList (ω,T,C)).get n).1 ω
        ((boxedList (ω,T,C)).get n).2).1 =
        run G jump (eventDecode rate ω) x ((boxedList (ω,T,C)).take n.val) := by
  filter_upwards [ae_boxedList_time_filter (J := J), ae_boxedList_mem (J := J),
    ae_boxedList_strict (J := J)] with ω hfilter hmem hstrict
  intro G jump rate C x T n
  let l := boxedList (ω,T,C)
  let e := l.get n
  let τ := (point e.1 ω e.2).1
  have hτ : τ ≤ T := ((hmem T C e).mp (List.get_mem l n)).1
  change run G jump (eventDecode rate ω) x ((boxedList (ω,τ,C)).filter
    (fun e => decide ((point e.1 ω e.2).1 < τ))) = _
  rw [← hfilter τ T C hτ, List.filter_filter]
  have he : (fun e' : Event J => decide ((point e'.1 ω e'.2).1 < τ) &&
      decide ((point e'.1 ω e'.2).1 ≤ τ)) =
      (fun e' => decide ((point e'.1 ω e'.2).1 < τ)) := by
    funext e'
    by_cases hh : (point e'.1 ω e'.2).1 < τ
    · simp [hh, hh.le]
    · simp [hh]
  rw [he]
  congr 1
  exact FrozenJumpIdentity.filter_before_get_eq_take _ l (hstrict T C) n.val n.isLt

/-- The frozen path has its genuine chronological left limit for every
sample-dependent choice of coefficients. -/
theorem ae_tendsto_left [TopologicalSpace E] : ∀ᵐ ω ∂law J,
    ∀ (G : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ) C x t,
      Tendsto (process G jump rate C x ω) (𝓝[<] t)
        (𝓝 (leftProcess G jump rate C x ω t)) := by
  filter_upwards [ae_left_constant (E := E) (J := J)] with ω hω
  intro G jump rate C x t
  obtain ⟨b, hb, he⟩ := hω G jump rate C x t
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hb)] with u hu hbu
  exact (he u ⟨hbu.le, hu⟩).symm

theorem ae_right_continuous [TopologicalSpace E] : ∀ᵐ ω ∂law J,
    ∀ (G : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ) C x t,
      ContinuousWithinAt (process G jump rate C x ω) (Ici t) t := by
  filter_upwards [ae_right_constant (E := E) (J := J)] with ω hω
  intro G jump rate C x t
  obtain ⟨b, hb, he⟩ := hω G jump rate C x t
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hb)] with u hu hub
  exact (he u ⟨hu, hub⟩).symm

/-- The finite-box equation written directly with its genuine left state. -/
def increment (G : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ)
    (C : ℝ) (x : E) (ω : Sample J) (f : E → ℝ) (j : J) (T : ℝ) (z : ℝ × ℝ) : ℝ :=
  if z.1 ∈ Ioc 0 T ∧ leftProcess G jump rate C x ω z.1 ∈ G ∧
      z.2 ≤ C ∧ z.2 ≤ rate j z.1 (leftProcess G jump rate C x ω z.1)
    then f (jump j (leftProcess G jump rate C x ω z.1)) - f (leftProcess G jump rate C x ω z.1)
    else 0

/-- Actual coordinate/test equations, simultaneously for every decoder.
The integrals are against the original common counting measures. -/
theorem ae_counting_identity : ∀ᵐ ω ∂law J,
    ∀ (G : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ) C x T (f : E → ℝ),
      f (process G jump rate C x ω T) - f x =
        ∑ j : J, ∫ z, increment G jump rate C x ω f j T z ∂countingMeasure j ω := by
  filter_upwards [ae_left_at_event (E := E) (J := J), ae_integral_box_eq_sum (J := J),
    ae_boxedList_mem (J := J), MarkedNoise.ae_positive_points (J := J)]
      with ω hleft hint hmem hpos
  intro G jump rate C x T f
  rw [process_telescope G jump rate f C x ω T]
  have he (j : J) : increment G jump rate C x ω f j T =
      (Iic T ×ˢ Iic C).indicator (fun z =>
        if leftProcess G jump rate C x ω z.1 ∈ G ∧
          z.2 ≤ rate j z.1 (leftProcess G jump rate C x ω z.1) ∧ 0 < z.1
        then f (jump j (leftProcess G jump rate C x ω z.1)) -
          f (leftProcess G jump rate C x ω z.1) else 0) := by
    funext z
    simp only [increment, Set.indicator_apply, mem_prod, mem_Iic, mem_Ioc]
    split_ifs <;> simp_all
  simp_rw [he]
  rw [hint T C]
  apply Finset.sum_congr rfl
  intro n _
  let a := (boxedList (ω,T,C)).get n
  rw [← hleft G jump rate C x T n]
  have hp := (hpos ((boxedList (ω,T,C)).get n).1 ((boxedList (ω,T,C)).get n).2).1
  simp only [acceptedIncrement, hp, and_true]

theorem ae_integrable_increment : ∀ᵐ ω ∂law J,
    ∀ (G : Finset E) (jump : J → E → E) (rate : J → ℝ → E → ℝ) C x T (f : E → ℝ) j,
      Integrable (increment G jump rate C x ω f j T) (countingMeasure j ω) := by
  filter_upwards [ae_integrable_box_weights (J := J)] with ω hω
  intro G jump rate C x T f j
  have he : increment G jump rate C x ω f j T =
      (Iic T ×ˢ Iic C).indicator (increment G jump rate C x ω f j T) := by
    funext z
    by_cases hz : z ∈ Iic T ×ˢ Iic C
    · exact (Set.indicator_of_mem hz _).symm
    · have hn : ¬(z.1 ∈ Ioc 0 T ∧ leftProcess G jump rate C x ω z.1 ∈ G ∧
          z.2 ≤ C ∧ z.2 ≤ rate j z.1 (leftProcess G jump rate C x ω z.1)) := by
        intro h
        exact hz ⟨h.1.2, h.2.2.1⟩
      rw [Set.indicator_of_not_mem hz]
      exact if_neg hn
  rw [he]
  exact hω T C j _

/-- The synchronous positive-jump bound is universal in both sets of
coefficients, including choices made from the same noise sample. -/
theorem ae_paired_distance_le_integral : ∀ᵐ ω ∂law J,
    ∀ (G H : Finset E) (jump : J → E → E) (rateX rateY : J → ℝ → E → ℝ)
      (ρ : E → E → ℝ) C x y T,
    (∀ s ∈ Ioc (0 : ℝ) T, leftProcess G jump rateX C x ω s ∈ G) →
    (∀ s ∈ Ioc (0 : ℝ) T, leftProcess H jump rateY C y ω s ∈ H) →
    ρ (process G jump rateX C x ω T) (process H jump rateY C y ω T) ≤
      ρ x y + ∑ j : J, ∫ z, boxField G H jump rateX rateY ρ C x y ω j T z
        ∂countingMeasure j ω := by
  filter_upwards [ae_left_at_event (E := E) (J := J), ae_integral_box_eq_sum (J := J),
    ae_boxedList_mem (J := J), MarkedNoise.ae_positive_points (J := J)]
      with ω hleft hint hmem hpos
  intro G H jump rateX rateY ρ C x y T hX hY
  have h := run_distance_le G H jump (eventDecode rateX ω) (eventDecode rateY ω)
    ρ x y (boxedList (ω,T,C))
  change ρ (process G jump rateX C x ω T) (process H jump rateY C y ω T) ≤ _ at h
  refine h.trans_eq ?_
  congr 1
  rw [show (∑ j : J, ∫ z, boxField G H jump rateX rateY ρ C x y ω j T z
      ∂countingMeasure j ω) = ∑ n : Fin (boxedList (ω,T,C)).length,
        let a := (boxedList (ω,T,C)).get n
        field G H jump rateX rateY ρ C x y ω a.1 (point a.1 ω a.2) from hint T C _]
  apply Finset.sum_congr rfl
  intro n _
  let a := (boxedList (ω,T,C)).get n
  have ha : (point a.1 ω a.2).1 ∈ Ioc (0 : ℝ) T :=
    ⟨(hpos a.1 a.2).1, ((hmem T C a).mp (List.get_mem _ n)).1⟩
  rw [← hleft G jump rateX C x T n, ← hleft H jump rateY C y T n]
  exact step_positiveIncrement G H jump rateX rateY ρ ω _ _ (hX _ ha) (hY _ ha) a

end CarryingCapacity.UniversalFrozenNoise
