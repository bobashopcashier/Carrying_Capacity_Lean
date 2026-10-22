import CarryingCapacity.PoissonIncrements

/-!
# Residual-clock restart and two-time count probabilities

These results concern the actual product exponential clock. Conditioning on
first-wait survival resets its full residual law. Renewal integration extends
that base case to two-time counts. Independence from the complete past and
mutual independence over arbitrary time grids remain separate obligations.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CarryingCapacity.PoissonIncrements
open CountableJumpProcess FrozenProcess PoissonClockLaw

def prepend (p : ℝ × ClockSpace) : ClockSpace
  | 0 => p.1
  | n + 1 => p.2 n

theorem measurable_prepend : Measurable prepend := by
  apply measurable_pi_lambda
  intro n
  cases n with
  | zero => exact measurable_fst
  | succ n => exact (measurable_pi_apply n).comp measurable_snd

theorem prepend_head_tail (ω : ClockSpace) : prepend (ω 0, shift 1 ω) = ω := by
  funext n
  cases n <;> simp [prepend, shift, Nat.add_comm]

theorem prepend_map (r : ℝ) (hr : 0 < r) :
    Measure.map prepend ((expMeasure r).prod (waitingTimeLaw r hr)) = waitingTimeLaw r hr := by
  rw [← head_tail_map, Measure.map_map measurable_prepend
    ((measurable_pi_apply 0).prodMk (measurable_shift 1))]
  simp only [Function.comp_def, prepend_head_tail]
  exact Measure.map_id

/-- Subtract elapsed time from the first waiting time, preserving the tail. -/
def subtractHead (s : ℝ) (ω : ClockSpace) : ClockSpace := prepend (ω 0 - s, shift 1 ω)

theorem measurable_subtractHead (s : ℝ) : Measurable (subtractHead s) :=
  measurable_prepend.comp (((measurable_pi_apply 0).sub_const s).prodMk (measurable_shift 1))

/-- Unnormalized memorylessness, useful when integrating over a random past. -/
theorem residual_restrict_map (r : ℝ) (hr : 0 < r) (s : ℝ) (hs : 0 ≤ s) :
    Measure.map (fun x : ℝ => x-s) ((expMeasure r).restrict (Ioi s)) =
      expMeasure r (Ioi s) • expMeasure r := by
  letI := isProbabilityMeasureExponential hr
  have hn : expMeasure r (Ioi s) ≠ 0 := by rw [exponential_survival r hr s hs]; positivity
  have h := congrArg (fun μ : Measure ℝ => expMeasure r (Ioi s) • μ)
    (conditional_residual_law r hr s hs)
  dsimp only at h
  rw [ProbabilityTheory.cond, Measure.map_smul, smul_smul,
    ENNReal.mul_inv_cancel hn (measure_ne_top _ _), one_smul] at h
  exact h

private theorem smul_prod_measure {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] (a : ℝ≥0∞) :
    (a • μ).prod ν = a • μ.prod ν := by
  ext s hs
  rw [Measure.prod_apply hs, lintegral_smul_measure, Measure.smul_apply,
    Measure.prod_apply hs]

/-- Conditional survival resets the entire clock, not just one coordinate. -/
theorem subtractHead_restrict_map (r : ℝ) (hr : 0 < r) (s : ℝ) (hs : 0 ≤ s) :
    Measure.map (subtractHead s)
      ((waitingTimeLaw r hr).restrict {ω : ClockSpace | s < ω 0}) =
      expMeasure r (Ioi s) • waitingTimeLaw r hr := by
  letI := isProbabilityMeasureExponential hr
  have hhead : Measure.map (fun ω : ClockSpace => (ω 0, shift 1 ω))
      ((waitingTimeLaw r hr).restrict {ω : ClockSpace | s < ω 0}) =
      ((expMeasure r).restrict (Ioi s)).prod (waitingTimeLaw r hr) := by
    have h := Measure.restrict_map (μ := waitingTimeLaw r hr)
      ((measurable_pi_apply 0).prodMk (measurable_shift 1))
      (measurableSet_Ioi.prod MeasurableSet.univ : MeasurableSet (Ioi s ×ˢ (univ : Set ClockSpace)))
    rw [head_tail_map, ← Measure.restrict_prod_eq_prod_univ] at h
    have heq : (fun ω : ClockSpace => (ω 0, shift 1 ω)) ⁻¹' (Ioi s ×ˢ (univ : Set ClockSpace)) =
        {ω : ClockSpace | s < ω 0} := by ext ω; simp
    simpa only [heq] using h.symm
  have hshift := congrArg (Measure.map (Prod.map (fun x : ℝ => x-s) (id : ClockSpace → ClockSpace))) hhead
  rw [← Measure.map_prod_map _ _ (show Measurable (fun x : ℝ => x-s) from measurable_id.sub_const s) measurable_id,
    residual_restrict_map r hr s hs, Measure.map_id, smul_prod_measure] at hshift
  have h := congrArg (Measure.map prepend) hshift
  rw [Measure.map_smul, prepend_map] at h
  have hp : Measurable (Prod.map (fun x : ℝ => x-s) (id : ClockSpace → ClockSpace)) :=
    (show Measurable (fun x : ℝ => x-s) from measurable_id.sub_const s).prodMap measurable_id
  rw [Measure.map_map measurable_prepend hp,
    Measure.map_map (measurable_prepend.comp hp)
      ((measurable_pi_apply 0).prodMk (measurable_shift 1))] at h
  exact h

theorem arrival_subtractHead (s : ℝ) (ω : ClockSpace) (n : ℕ) :
    arrival (subtractHead s ω) (n+1) = arrival ω (n+1) - s := by
  induction n with
  | zero => simp [arrival_succ, arrival_zero, subtractHead, prepend]
  | succ n ih =>
    rw [arrival_succ (subtractHead s ω) (n+1), arrival_succ ω (n+1), ih]
    simp only [subtractHead, prepend, shift, Nat.add_comm 1 n]
    ring

theorem proposalCount_subtractHead (s t : ℝ) (ω : ClockSpace) :
    proposalCount (subtractHead s ω) t = proposalCount ω (s+t) := by
  unfold proposalCount
  congr 1
  ext n
  simp only [mem_setOf_eq, arrival_subtractHead]
  constructor <;> intro h <;> linarith

/-- Joint law on the event of no proposal up to s, from full-clock memorylessness. -/
theorem probability_zero_then_count (r : ℝ) (hr : 0 < r) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (n : ℕ) :
    waitingTimeLaw r hr {ω | proposalCount ω s = 0 ∧ proposalCount ω (s+t) = n} =
      ENNReal.ofReal (Real.exp (-(r*s))) *
      ENNReal.ofReal (Real.exp (-(r*t)) * (r*t)^n / (n.factorial : ℝ)) := by
  have h := congrArg (fun μ : Measure ClockSpace => μ {ω | proposalCount ω t = n})
    (subtractHead_restrict_map r hr s hs)
  dsimp only at h
  have hA : MeasurableSet {ω : ClockSpace | proposalCount ω t = n} :=
    (measurable_proposalCount t) (measurableSet_singleton n)
  rw [Measure.map_apply (measurable_subtractHead s) hA,
    Measure.restrict_apply ((measurable_subtractHead s) hA), Measure.smul_apply,
    smul_eq_mul, exponential_survival r hr s hs, probability_count r hr t ht n] at h
  rw [← h]
  apply measure_congr
  filter_upwards [ae_locally_finite r hr] with ω hω
  change (proposalCount ω s = 0 ∧ proposalCount ω (s+t) = n) =
    (proposalCount (subtractHead s ω) t = n ∧ s < ω 0)
  rw [proposalCount_subtractHead, proposalCount_eq_zero_iff hω.1 hω.2 s, and_comm]

/-- On survival of the first wait, the whole residual clock has its original law. -/
theorem conditional_clock_restart (r : ℝ) (hr : 0 < r) (s : ℝ) (hs : 0 ≤ s) :
    Measure.map (subtractHead s)
      (ProbabilityTheory.cond (waitingTimeLaw r hr) {ω : ClockSpace | s < ω 0}) =
      waitingTimeLaw r hr := by
  letI := isProbabilityMeasureExponential hr
  have hmass : waitingTimeLaw r hr {ω : ClockSpace | s < ω 0} = expMeasure r (Ioi s) := by
    have h := congrArg (fun μ : Measure ℝ => μ (Ioi s)) (coordinate_map r hr 0)
    dsimp only at h
    rw [Measure.map_apply (measurable_pi_apply 0) measurableSet_Ioi] at h
    exact h
  have hn : expMeasure r (Ioi s) ≠ 0 := by rw [exponential_survival r hr s hs]; positivity
  rw [ProbabilityTheory.cond, Measure.map_smul, subtractHead_restrict_map r hr s hs,
    smul_smul, hmass, ENNReal.inv_mul_cancel hn (measure_ne_top _ _), one_smul]

/-- Splitting the first waiting time gives a renewal recurrence for two-time counts. -/
theorem probability_counts_succ (r : ℝ) (hr : 0 < r) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (m n : ℕ) :
    waitingTimeLaw r hr {ω | proposalCount ω s = m+1 ∧ proposalCount ω (s+t) = m+1+n} =
      ∫⁻ u in Iic s, waitingTimeLaw r hr
        {ω | proposalCount ω (s-u) = m ∧ proposalCount ω ((s-u)+t) = m+n} ∂expMeasure r := by
  letI := isProbabilityMeasureExponential hr
  have hsmono : ∀ᵐ ω ∂waitingTimeLaw r hr, StrictMono (arrival (shift 1 ω)) := by
    have h := (ae_locally_finite r hr).mono (fun _ h => h.1)
    rw [← shift_map r hr 1] at h
    exact ae_of_ae_map (measurable_shift 1).aemeasurable h
  have hsdiv : ∀ᵐ ω ∂waitingTimeLaw r hr,
      Tendsto (arrival (shift 1 ω)) atTop atTop := by
    have h := ae_arrival_tendsto r hr
    rw [← shift_map r hr 1] at h
    exact ae_of_ae_map (measurable_shift 1).aemeasurable h
  let S : Set (ℝ × ClockSpace) := {p | p.1 ≤ s ∧
    proposalCount p.2 (s-p.1) = m ∧ proposalCount p.2 ((s-p.1)+t) = m+n}
  have hfirst : Measurable (fun p : ℝ × ClockSpace => proposalCount p.2 (s-p.1)) :=
    measurable_joint_proposalCount.comp (f := fun p : ℝ × ClockSpace => (p.2, s-p.1))
      (measurable_snd.prodMk (measurable_const.sub measurable_fst))
  have hsecond : Measurable (fun p : ℝ × ClockSpace => proposalCount p.2 ((s-p.1)+t)) :=
    measurable_joint_proposalCount.comp (f := fun p : ℝ × ClockSpace => (p.2, (s-p.1)+t))
      (measurable_snd.prodMk ((measurable_const.sub measurable_fst).add_const t))
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_fst measurable_const).inter
      ((hfirst (measurableSet_singleton m)).inter (hsecond (measurableSet_singleton (m+n))))
  have heq : {ω : ClockSpace | proposalCount ω s = m+1 ∧ proposalCount ω (s+t) = m+1+n}
      =ᵐ[waitingTimeLaw r hr] (fun ω : ClockSpace => (ω 0, shift 1 ω)) ⁻¹' S := by
    filter_upwards [ae_locally_finite r hr, ae_arrival_tendsto r hr, hsmono, hsdiv]
      with ω hω hdiv hm hd
    change (proposalCount ω s = m+1 ∧ proposalCount ω (s+t) = m+1+n) =
      (ω 0 ≤ s ∧ proposalCount (shift 1 ω) (s-ω 0) = m ∧
        proposalCount (shift 1 ω) ((s-ω 0)+t) = m+n)
    apply propext
    rw [show m+1+n = (m+n)+1 by omega,
      proposalCount_succ_iff hω.1 hdiv hm hd s hs m,
      proposalCount_succ_iff hω.1 hdiv hm hd (s+t) (add_nonneg hs ht) (m+n),
      show s+t-ω 0 = (s-ω 0)+t by ring]
    constructor
    · rintro ⟨⟨hws, hfirst⟩, _, hsecond⟩
      exact ⟨hws, hfirst, hsecond⟩
    · rintro ⟨hws, hfirst, hsecond⟩
      exact ⟨⟨hws, hfirst⟩, by linarith, hsecond⟩
  rw [measure_congr heq,
    ← Measure.map_apply ((measurable_pi_apply 0).prodMk (measurable_shift 1)) hS,
    head_tail_map, Measure.prod_apply hS, ← lintegral_indicator measurableSet_Iic]
  apply lintegral_congr
  intro u
  by_cases hu : u ≤ s <;> simp [S, hu, Set.indicator, mem_Iic]

/-- Exact two-time count probabilities. The second index counts the additional proposals. -/
theorem probability_two_counts (r : ℝ) (hr : 0 < r) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (m n : ℕ) :
    waitingTimeLaw r hr {ω | proposalCount ω s = m ∧ proposalCount ω (s+t) = m+n} =
      ENNReal.ofReal (Real.exp (-(r*s)) * (r*s)^m / (m.factorial : ℝ)) *
      ENNReal.ofReal (Real.exp (-(r*t)) * (r*t)^n / (n.factorial : ℝ)) := by
  induction m generalizing s with
  | zero => simpa using probability_zero_then_count r hr s t hs ht n
  | succ m ih =>
    rw [probability_counts_succ r hr s t hs ht m n]
    calc
      _ = ∫⁻ u in Iic s,
          ENNReal.ofReal (Real.exp (-(r*(s-u))) * (r*(s-u))^m / (m.factorial : ℝ)) *
          ENNReal.ofReal (Real.exp (-(r*t)) * (r*t)^n / (n.factorial : ℝ)) ∂expMeasure r := by
        apply setLIntegral_congr_fun measurableSet_Iic
        exact ae_of_all _ (fun u hu => ih (s-u) (sub_nonneg.mpr hu))
      _ = _ := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          exponential_renewal_integral r hr s hs m, poisson_renewal_integral]

/-- Number of proposals in the interval (s,s+t]. -/
def increment (ω : ClockSpace) (s t : ℝ) : ℕ := proposalCount ω (s+t) - proposalCount ω s

theorem measurable_increment (s t : ℝ) : Measurable (fun ω => increment ω s t) :=
  (measurable_proposalCount (s+t)).sub (measurable_proposalCount s)

/-- The previous count and one subsequent increment have the product of their Poisson masses. -/
theorem probability_count_increment (r : ℝ) (hr : 0 < r) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (m n : ℕ) :
    waitingTimeLaw r hr {ω | proposalCount ω s = m ∧ increment ω s t = n} =
      ENNReal.ofReal (Real.exp (-(r*s)) * (r*s)^m / (m.factorial : ℝ)) *
      ENNReal.ofReal (Real.exp (-(r*t)) * (r*t)^n / (n.factorial : ℝ)) := by
  rw [← probability_two_counts r hr s t hs ht m n]
  apply measure_congr
  filter_upwards [ae_locally_finite r hr] with ω hω
  have hle := proposalCount_mono hω.2 (show s ≤ s+t by linarith)
  change (proposalCount ω s = m ∧ proposalCount ω (s+t) - proposalCount ω s = n) =
    (proposalCount ω s = m ∧ proposalCount ω (s+t) = m+n)
  apply propext
  omega

/-- The actual joint law of the previous count and next increment is the product Poisson law. -/
theorem count_increment_map (r : ℝ) (hr : 0 < r) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Measure.map (fun ω => (proposalCount ω s, increment ω s t)) (waitingTimeLaw r hr) =
      (poissonMeasure ⟨r*s, mul_nonneg hr.le hs⟩).prod
        (poissonMeasure ⟨r*t, mul_nonneg hr.le ht⟩) := by
  apply Measure.ext_of_singleton
  rintro ⟨m,n⟩
  rw [Measure.map_apply ((measurable_proposalCount s).prodMk (measurable_increment s t))
    (measurableSet_singleton (m,n))]
  have heq : (fun ω => (proposalCount ω s, increment ω s t)) ⁻¹' {(m,n)} =
      {ω | proposalCount ω s = m ∧ increment ω s t = n} := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, Prod.mk.injEq, mem_setOf_eq]
  rw [heq, probability_count_increment r hr s t hs ht m n]
  have hprod : ({(m,n)} : Set (ℕ × ℕ)) = {m} ×ˢ {n} := by
    ext p
    simp only [mem_singleton_iff, Prod.mk.injEq, mem_prod]
    exact Prod.ext_iff
  rw [hprod, Measure.prod_prod]
  change _ = (poissonPMF ⟨r*s, mul_nonneg hr.le hs⟩).toMeasure {m} *
    (poissonPMF ⟨r*t, mul_nonneg hr.le ht⟩).toMeasure {n}
  rw [PMF.toMeasure_apply_singleton _ m (measurableSet_singleton m),
    PMF.toMeasure_apply_singleton _ n (measurableSet_singleton n)]
  rfl

/-- A single increment has Poisson law depending only on its interval length. -/
theorem increment_map (r : ℝ) (hr : 0 < r) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Measure.map (fun ω => increment ω s t) (waitingTimeLaw r hr) =
      poissonMeasure ⟨r*t, mul_nonneg hr.le ht⟩ := by
  have h := congrArg (Measure.map Prod.snd) (count_increment_map r hr s t hs ht)
  rw [Measure.map_map measurable_snd
    ((measurable_proposalCount s).prodMk (measurable_increment s t)),
    Measure.map_snd_prod, measure_univ, one_smul] at h
  exact h

/-- The next increment is independent of the count at its starting time.
This does not assert independence from the entire natural filtration. -/
theorem independent_count_increment (r : ℝ) (hr : 0 < r) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IndepFun (fun ω => proposalCount ω s) (fun ω => increment ω s t) (waitingTimeLaw r hr) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map (measurable_proposalCount s).aemeasurable
    (measurable_increment s t).aemeasurable).mpr
  rw [count_increment_map r hr s t hs ht, proposalCount_map r hr s hs,
    increment_map r hr s t hs ht]

end CarryingCapacity.PoissonIncrements
