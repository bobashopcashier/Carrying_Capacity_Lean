import CarryingCapacity.PoissonClockLaw

/-!
# Renewal identities for the canonical exponential clock

The clock here is the actual product-measure construction. Its shifted tail
has the same law; the head is independent of the entire tail. The renewal
recurrence proves the complete one-time Poisson count law. Independent
stationary increments and the compensator are separate proof obligations.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace CarryingCapacity.PoissonIncrements
open CountableJumpProcess FrozenProcess PoissonClockLaw

def shift (k : ℕ) (ω : ClockSpace) : ClockSpace := fun n => ω (k + n)

theorem measurable_shift (k : ℕ) : Measurable (shift k) :=
  measurable_pi_lambda _ (fun n => measurable_pi_apply (k + n))

/-- Discarding a deterministic finite prefix leaves the same exponential law. -/
theorem shift_map (r : ℝ) (hr : 0 < r) (k : ℕ) :
    Measure.map (shift k) (waitingTimeLaw r hr) = waitingTimeLaw r hr := by
  letI := isProbabilityMeasureExponential hr
  change _ = Measure.infinitePi (fun _ : ℕ => expMeasure r)
  apply Measure.eq_infinitePi
  intro s sets hs
  rw [Measure.map_apply (measurable_shift k) (.pi s.countable_toSet hs)]
  have heq : shift k ⁻¹' Set.pi s sets =
      ⋂ i ∈ s, (fun ω : ClockSpace => ω (k + i)) ⁻¹' sets i := by
    ext ω
    simp [shift]
  rw [heq, ((independent_coordinates r hr).precomp
    (g := fun n => k + n)
    (fun _ _ h => Nat.add_left_cancel h)).measure_inter_preimage_eq_mul s hs]
  apply Finset.prod_congr rfl
  intro i hi
  have h := congrArg (fun μ : Measure ℝ => μ (sets i)) (coordinate_map r hr (k + i))
  dsimp only at h
  rw [Measure.map_apply (measurable_pi_apply (k + i)) (hs i hi)] at h
  exact h

/-- The entire shifted tail is independent of the first waiting time. -/
theorem independent_head_tail (r : ℝ) (hr : 0 < r) :
    IndepFun (fun ω : ClockSpace => ω 0) (shift 1) (waitingTimeLaw r hr) := by
  let m : ℕ → MeasurableSpace ClockSpace := fun i =>
    MeasurableSpace.comap (fun ω : ClockSpace => ω i) inferInstance
  have hind := indep_iSup_of_disjoint
    (fun i => (measurable_pi_apply i).comap_le)
    (independent_coordinates r hr).iIndep
    (S := ({0} : Set ℕ)) (T := Ioi 0) (by simp)
  have hleft : (⨆ i ∈ ({0} : Set ℕ), m i) = m 0 := by simp
  change Indep (⨆ i ∈ ({0} : Set ℕ), m i) (⨆ i ∈ Ioi 0, m i) _ at hind
  rw [hleft] at hind
  apply (IndepFun_iff_Indep _ _ _).mpr
  apply indep_of_indep_of_le_right hind
  change MeasurableSpace.comap (shift 1) MeasurableSpace.pi ≤ _
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  apply iSup_le
  intro n
  rw [MeasurableSpace.comap_comp]
  exact le_iSup_of_le (1 + n)
    (le_iSup_of_le (by change 0 < 1 + n; omega : 1 + n ∈ Ioi 0) le_rfl)

/-- The head and full tail have exactly the product law used in renewal integration. -/
theorem head_tail_map (r : ℝ) (hr : 0 < r) :
    Measure.map (fun ω : ClockSpace => (ω 0, shift 1 ω)) (waitingTimeLaw r hr) =
      (expMeasure r).prod (waitingTimeLaw r hr) := by
  have h := (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_apply 0).aemeasurable (measurable_shift 1).aemeasurable).mp
      (independent_head_tail r hr)
  rwa [coordinate_map, shift_map] at h

theorem arrival_shift_one (ω : ClockSpace) (n : ℕ) :
    arrival (shift 1 ω) n + ω 0 = arrival ω (n + 1) := by
  induction n with
  | zero => simp [arrival_succ, arrival_zero]
  | succ n ih =>
    rw [arrival_succ, arrival_succ]
    simp only [shift, Nat.add_comm 1 n]
    linarith

/-- Exact count events are the consecutive-arrival intervals. -/
theorem proposalCount_eq_iff {ω : ClockSpace}
    (hmono : StrictMono (arrival ω)) (hdiv : Tendsto (arrival ω) atTop atTop)
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    proposalCount ω t = n ↔ arrival ω n ≤ t ∧ t < arrival ω (n + 1) := by
  obtain ⟨m, hm⟩ := exists_arrival_interval hdiv ht
  have heq := proposalCount_between hmono hm.1 hm.2
  constructor
  · intro hn
    have hmn : m = n := heq.symm.trans hn
    simpa [hmn] using hm
  · intro hn
    exact proposalCount_between hmono hn.1 hn.2

/-- The successor count event is determined by the first wait and the restarted tail. -/
theorem proposalCount_succ_iff {ω : ClockSpace}
    (hmono : StrictMono (arrival ω)) (hdiv : Tendsto (arrival ω) atTop atTop)
    (hsmono : StrictMono (arrival (shift 1 ω)))
    (hsdiv : Tendsto (arrival (shift 1 ω)) atTop atTop)
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    proposalCount ω t = n + 1 ↔
      ω 0 ≤ t ∧ proposalCount (shift 1 ω) (t - ω 0) = n := by
  rw [proposalCount_eq_iff hmono hdiv t ht (n + 1)]
  constructor
  · intro h
    have hfirst : ω 0 ≤ t := by
      have hh := hmono.monotone (show 1 ≤ n + 1 by omega)
      simpa [arrival_succ, arrival_zero] using hh.trans h.1
    refine ⟨hfirst, (proposalCount_eq_iff hsmono hsdiv _ (by linarith) n).mpr ?_⟩
    have hlo := arrival_shift_one ω n
    have hhi := arrival_shift_one ω (n + 1)
    constructor <;> linarith
  · rintro ⟨hfirst, hcount⟩
    have h := (proposalCount_eq_iff hsmono hsdiv _ (by linarith) n).mp hcount
    have hlo := arrival_shift_one ω n
    have hhi := arrival_shift_one ω (n + 1)
    constructor <;> linarith

/-- An exponential waiting time has no atoms, directly from its density. -/
theorem exponential_noAtoms (r : ℝ) : NoAtoms (expMeasure r) := by
  constructor
  intro x
  rw [expMeasure, gammaMeasure, withDensity_apply _ (measurableSet_singleton x)]
  simp

/-- Every positive-index arrival has a nonatomic law. This also supports
proving that independent clock strips have no simultaneous arrivals. -/
theorem arrival_noAtoms (r : ℝ) (hr : 0 < r) (n : ℕ) :
    NoAtoms (Measure.map (fun ω => arrival ω (n + 1)) (waitingTimeLaw r hr)) := by
  letI := isProbabilityMeasureExponential hr
  letI := exponential_noAtoms r
  constructor
  intro t
  let S : Set (ℝ × ClockSpace) := {p | p.1 + arrival p.2 n = t}
  have hS : MeasurableSet S :=
    measurableSet_eq_fun
      (measurable_fst.add ((measurable_arrival n).comp measurable_snd)) measurable_const
  have heq : (fun ω => arrival ω (n + 1)) ⁻¹' {t} =
      (fun ω : ClockSpace => (ω 0, shift 1 ω)) ⁻¹' S := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, S, mem_setOf_eq]
    rw [← arrival_shift_one]
    constructor <;> intro h <;> linarith
  rw [Measure.map_apply (measurable_arrival (n + 1)) (measurableSet_singleton t), heq,
    ← Measure.map_apply ((measurable_pi_apply 0).prodMk (measurable_shift 1)) hS,
    head_tail_map, Measure.prod_apply_symm hS]
  have hs (ω : ClockSpace) : {s : ℝ | (s, ω) ∈ S} = {t - arrival ω n} := by
    ext s
    simp only [S, mem_setOf_eq, mem_singleton_iff]
    constructor <;> intro h <;> linarith
  simp only [show (fun y => expMeasure r ((fun x => (x, y)) ⁻¹' S)) = fun _ => 0 by
    funext ω; change expMeasure r {s : ℝ | (s, ω) ∈ S} = 0; rw [hs]; exact measure_singleton _]
  exact lintegral_zero

/-- Joint measurability includes a variable horizon in the renewal integral. -/
theorem measurable_joint_proposalCount :
    Measurable (fun p : ClockSpace × ℝ => proposalCount p.1 p.2) := by
  apply measurable_ncard.comp
  apply measurable_pi_lambda
  intro n
  apply measurable_to_prop
  simpa using measurableSet_le ((measurable_arrival (n + 1)).comp measurable_fst) measurable_snd

/-- Renewal recurrence for the actual constructed count, obtained by splitting
off its first waiting time. No count distribution is assumed. -/
theorem probability_count_succ (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    waitingTimeLaw r hr {ω | proposalCount ω t = n + 1} =
      ∫⁻ s in Iic t, waitingTimeLaw r hr {ω | proposalCount ω (t - s) = n} ∂expMeasure r := by
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
  let S : Set (ℝ × ClockSpace) := {p | p.1 ≤ t ∧ proposalCount p.2 (t - p.1) = n}
  have hcount : Measurable (fun p : ℝ × ClockSpace => proposalCount p.2 (t - p.1)) :=
    measurable_joint_proposalCount.comp (f := fun p : ℝ × ClockSpace => (p.2, t - p.1))
      (measurable_snd.prodMk (measurable_const.sub measurable_fst))
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_fst measurable_const).inter (hcount (measurableSet_singleton n))
  have heq : {ω : ClockSpace | proposalCount ω t = n + 1} =ᵐ[waitingTimeLaw r hr]
      (fun ω : ClockSpace => (ω 0, shift 1 ω)) ⁻¹' S := by
    filter_upwards [ae_locally_finite r hr, ae_arrival_tendsto r hr, hsmono, hsdiv]
      with ω hω hdiv hm hd
    exact propext (proposalCount_succ_iff hω.1 hdiv hm hd t ht n)
  rw [measure_congr heq,
    ← Measure.map_apply ((measurable_pi_apply 0).prodMk (measurable_shift 1)) hS,
    head_tail_map, Measure.prod_apply hS, ← lintegral_indicator measurableSet_Iic]
  apply lintegral_congr
  intro s
  by_cases hs : s ≤ t <;> simp [S, hs, Set.indicator, mem_Iic]

/-- Elementary renewal integral, evaluated using a polynomial antiderivative. -/
theorem poisson_renewal_integral (r t : ℝ) (n : ℕ) :
    (∫ s in (0 : ℝ)..t, r * Real.exp (-(r * s)) *
      (Real.exp (-(r * (t-s))) * (r * (t-s))^n / (n.factorial : ℝ))) =
      Real.exp (-(r*t)) * (r*t)^(n+1) / ((n+1).factorial : ℝ) := by
  have hf (s : ℝ) : r * Real.exp (-(r * s)) *
      (Real.exp (-(r * (t-s))) * (r * (t-s))^n / (n.factorial : ℝ)) =
      (r^(n+1) * Real.exp (-(r*t)) / (n.factorial : ℝ)) * (t-s)^n := by
    have he : Real.exp (-(r*s)) * Real.exp (-(r*(t-s))) = Real.exp (-(r*t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_pow]
    calc
      _ = r * (Real.exp (-(r*s)) * Real.exp (-(r*(t-s)))) * r^n * (t-s)^n /
          (n.factorial : ℝ) := by ring
      _ = _ := by rw [he, pow_succ]; ring
  simp_rw [hf]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^n) t]
  simp only [sub_self, sub_zero, integral_pow, zero_pow (Nat.succ_ne_zero n), sub_zero]
  rw [Nat.factorial_succ]
  push_cast
  rw [mul_pow, pow_succ]
  field_simp
  ring

/-- Density-based reduction of exponential renewal integration to Lebesgue integration. -/
theorem exponential_renewal_integral (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    (∫⁻ s in Iic t, ENNReal.ofReal
      (Real.exp (-(r * (t-s))) * (r * (t-s))^n / (n.factorial : ℝ)) ∂expMeasure r) =
      ENNReal.ofReal (∫ s in (0 : ℝ)..t, r * Real.exp (-(r * s)) *
        (Real.exp (-(r * (t-s))) * (r * (t-s))^n / (n.factorial : ℝ))) := by
  let f : ℝ → ℝ := fun s => Real.exp (-(r*(t-s))) * (r*(t-s))^n / (n.factorial : ℝ)
  change (∫⁻ s in Iic t, ENNReal.ofReal (f s) ∂volume.withDensity (exponentialPDF r)) = _
  have hm : Measurable (fun s => ENNReal.ofReal (f s)) := by dsimp [f]; fun_prop
  rw [setLIntegral_withDensity_eq_setLIntegral_mul volume
    (show Measurable (exponentialPDF r) from (measurable_exponentialPDFReal r).ennreal_ofReal) hm measurableSet_Iic]
  rw [lintegral_Iic_eq_lintegral_Iio_add_Icc _ ht]
  have hz : (∫⁻ s in Iio (0 : ℝ), (exponentialPDF r * fun s => ENNReal.ofReal (f s)) s) = 0 := by
    calc
      _ = ∫⁻ s in Iio (0 : ℝ), (0 : ℝ≥0∞) := by
        apply setLIntegral_congr_fun measurableSet_Iio
        exact ae_of_all _ (fun s hs => by simp [exponentialPDF_of_neg hs])
      _ = 0 := lintegral_zero
  rw [hz, zero_add]
  have heq : (∫⁻ s in Icc (0 : ℝ) t, (exponentialPDF r * fun s => ENNReal.ofReal (f s)) s) =
      ∫⁻ s in Icc (0 : ℝ) t, ENNReal.ofReal (r * Real.exp (-(r*s)) * f s) := by
    apply setLIntegral_congr_fun measurableSet_Icc
    exact ae_of_all _ (fun s hs => by
      rw [Pi.mul_apply, exponentialPDF_of_nonneg hs.1,
        ENNReal.ofReal_mul (by positivity : 0 ≤ r * Real.exp (-(r*s)))])
  rw [heq]
  have hc : Continuous (fun s => r * Real.exp (-(r*s)) * f s) := by dsimp [f]; fun_prop
  have hn : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) t)] (fun s => r * Real.exp (-(r*s)) * f s) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hts : 0 ≤ t - s := sub_nonneg.mpr hs.2
    dsimp [f]
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Icc hn,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht]

/-- The complete one-time Poisson count probabilities of the constructed clock. -/
theorem probability_count (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    waitingTimeLaw r hr {ω | proposalCount ω t = n} =
      ENNReal.ofReal (Real.exp (-(r*t)) * (r*t)^n / (n.factorial : ℝ)) := by
  induction n generalizing t with
  | zero => simpa using probability_zero_proposals r hr t ht
  | succ n ih =>
    rw [probability_count_succ r hr t ht n]
    calc
      _ = ∫⁻ s in Iic t, ENNReal.ofReal
          (Real.exp (-(r * (t-s))) * (r * (t-s))^n / (n.factorial : ℝ)) ∂expMeasure r := by
        apply setLIntegral_congr_fun measurableSet_Iic
        exact ae_of_all _ (fun s hs => ih (t-s) (sub_nonneg.mpr hs))
      _ = _ := by rw [exponential_renewal_integral r hr t ht n, poisson_renewal_integral]

/-- Equality of actual measures: the proposal count at time t has Poisson law of mean r*t. -/
theorem proposalCount_map (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : 0 ≤ t) :
    Measure.map (fun ω => proposalCount ω t) (waitingTimeLaw r hr) =
      poissonMeasure ⟨r*t, mul_nonneg hr.le ht⟩ := by
  apply Measure.ext_of_singleton
  intro n
  rw [Measure.map_apply (measurable_proposalCount t) (measurableSet_singleton n)]
  change waitingTimeLaw r hr {ω | proposalCount ω t = n} =
    (poissonPMF ⟨r*t, mul_nonneg hr.le ht⟩).toMeasure {n}
  rw [PMF.toMeasure_apply_singleton _ n (measurableSet_singleton n), probability_count r hr t ht n]
  rfl

end CarryingCapacity.PoissonIncrements
