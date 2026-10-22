import Mathlib

/-!
# A non-explosive clock from exponential waiting times

The probability space is the actual countable product of exponential laws.
We prove local finiteness of its arrival times; it is not an assumption about
a proposed process. This supplies the clock part of the finite-rate proposal
construction in Lemma 3.1 of the manuscript. Poisson increment laws, marks,
adapted state recursion, and compensation are separate results.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace CarryingCapacity.CountableJumpProcess

abbrev ClockSpace := ℕ → ℝ

/-- Canonical law of a sequence of independent exponential waiting times. -/
def waitingTimeLaw (r : ℝ) (hr : 0 < r) : Measure ClockSpace := by
  letI := isProbabilityMeasureExponential hr
  exact Measure.infinitePi (fun _ : ℕ => expMeasure r)

instance waitingTimeLaw_probability (r : ℝ) (hr : 0 < r) :
    IsProbabilityMeasure (waitingTimeLaw r hr) := by
  unfold waitingTimeLaw
  letI := isProbabilityMeasureExponential hr
  infer_instance

/-- A single cylinder has exactly the prescribed one-coordinate law. -/
theorem coordinate_event (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (s : Set ℝ) (hs : MeasurableSet s) :
    (Measure.infinitePi (fun _ : ℕ => μ)) {ω : ClockSpace | ω n ∈ s} = μ s := by
  have heq : {ω : ClockSpace | ω n ∈ s} = Set.pi ({n} : Finset ℕ) (fun _ => s) := by
    ext ω
    simp
  rw [heq, Measure.infinitePi_pi _ (fun _ _ => hs)]
  simp

/-- Each waiting-time coordinate has precisely the exponential marginal. -/
theorem coordinate_map (r : ℝ) (hr : 0 < r) (n : ℕ) :
    Measure.map (fun ω : ClockSpace => ω n) (waitingTimeLaw r hr) = expMeasure r := by
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply n) hs]
  unfold waitingTimeLaw
  letI := isProbabilityMeasureExponential hr
  exact coordinate_event _ n s hs

/-- Joint independence of the complete sequence, not only one chosen family
of threshold events. -/
theorem independent_coordinates (r : ℝ) (hr : 0 < r) :
    iIndepFun (fun n (ω : ClockSpace) => ω n) (waitingTimeLaw r hr) := by
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro I sets hs
  have heq : (⋂ n ∈ I, (fun ω : ClockSpace => ω n) ⁻¹' sets n) = Set.pi I sets := by
    ext ω
    simp
  rw [heq]
  unfold waitingTimeLaw
  letI := isProbabilityMeasureExponential hr
  rw [Measure.infinitePi_pi _ hs]
  apply Finset.prod_congr rfl
  intro n hn
  exact (coordinate_event _ n _ (hs n hn)).symm

/-- The exponential survival formula, with the strict-positive rate explicit. -/
theorem exponential_survival (r : ℝ) (hr : 0 < r) (t : ℝ) (ht : 0 ≤ t) :
    expMeasure r (Ioi t) = ENNReal.ofReal (Real.exp (-(r * t))) := by
  letI := isProbabilityMeasureExponential hr
  have hcdf := ofReal_cdf (expMeasure r) t
  change ENNReal.ofReal (exponentialCDFReal r t) = _ at hcdf
  rw [exponentialCDFReal_eq hr t, if_pos ht] at hcdf
  have he : Real.exp (-(r * t)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hr.le ht))
  rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _),
    measure_univ, ← hcdf, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (sub_nonneg.mpr he)]
  congr 1
  ring

/-- Almost surely every waiting time is strictly positive. -/
theorem ae_positive (r : ℝ) (hr : 0 < r) :
    ∀ᵐ ω ∂waitingTimeLaw r hr, ∀ n, 0 < ω n := by
  apply ae_all_iff.mpr
  intro n
  rw [ae_iff]
  have heq : {ω : ClockSpace | ¬ 0 < ω n} = {ω : ClockSpace | ω n ∈ Iic 0} := by
    ext ω
    simp
  rw [heq]
  unfold waitingTimeLaw
  letI := isProbabilityMeasureExponential hr
  rw [coordinate_event _ n _ measurableSet_Iic, ← ofReal_cdf (expMeasure r) 0]
  change ENNReal.ofReal (exponentialCDFReal r 0) = 0
  rw [exponentialCDFReal_eq hr]
  norm_num

/-- Independence of any chosen coordinate events follows from the product
measure's finite-dimensional cylinder formula. -/
theorem independent_coordinate_events (r : ℝ) (hr : 0 < r)
    (s : ℕ → Set ℝ) (hs : ∀ n, MeasurableSet (s n)) :
    iIndepSet (fun n => {ω : ClockSpace | ω n ∈ s n}) (waitingTimeLaw r hr) := by
  apply (iIndepSet_iff_meas_biInter (fun n => (hs n).preimage (measurable_pi_apply n))).mpr
  intro I
  have heq : (⋂ n ∈ I, {ω : ClockSpace | ω n ∈ s n}) = Set.pi I s := by
    ext ω
    simp
  change waitingTimeLaw r hr (⋂ n ∈ I, {ω : ClockSpace | ω n ∈ s n}) =
    ∏ n ∈ I, waitingTimeLaw r hr {ω : ClockSpace | ω n ∈ s n}
  rw [heq]
  unfold waitingTimeLaw
  letI := isProbabilityMeasureExponential hr
  rw [Measure.infinitePi_pi _ (fun n _ => hs n)]
  apply Finset.prod_congr rfl
  intro n _
  exact (coordinate_event _ n _ (hs n)).symm

/-- Infinitely many waiting times exceed one, derived using Borel-Cantelli.
This is enough for divergence and does not need an assumed strong law. -/
theorem ae_frequently_one_lt (r : ℝ) (hr : 0 < r) :
    ∀ᵐ ω ∂waitingTimeLaw r hr, ∃ᶠ n in atTop, 1 < ω n := by
  let events : ℕ → Set ClockSpace := fun n => {ω | 1 < ω n}
  have hm : ∀ n, MeasurableSet (events n) := fun n =>
    measurableSet_lt measurable_const (measurable_pi_apply n)
  have hind : iIndepSet events (waitingTimeLaw r hr) :=
    independent_coordinate_events r hr (fun _ => Ioi 1) (fun _ => measurableSet_Ioi)
  have hmeasure (n : ℕ) : waitingTimeLaw r hr (events n) =
      ENNReal.ofReal (Real.exp (-r)) := by
    unfold waitingTimeLaw
    letI := isProbabilityMeasureExponential hr
    change (Measure.infinitePi (fun _ : ℕ => expMeasure r))
      {ω : ClockSpace | ω n ∈ Ioi 1} = _
    rw [coordinate_event _ n (Ioi 1) measurableSet_Ioi, exponential_survival r hr 1 (by norm_num)]
    simp
  have hsum : (∑' n, waitingTimeLaw r hr (events n)) = ∞ := by
    simp_rw [hmeasure]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (by positivity)
  have hfull := measure_limsup_eq_one hm hind hsum
  have hae : ∀ᵐ ω ∂waitingTimeLaw r hr, ω ∈ limsup events atTop := by
    apply (ae_mem_iff_measure_eq ((MeasurableSet.measurableSet_limsup hm).nullMeasurableSet)).mpr
    simpa using hfull
  filter_upwards [hae] with ω hω
  exact mem_limsup_iff_frequently_mem.mp hω

/-- The n-th arrival is the sum of the first n waiting times; arrival zero is zero. -/
def arrival (ω : ClockSpace) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, ω i

@[simp] theorem arrival_zero (ω : ClockSpace) : arrival ω 0 = 0 := by
  simp [arrival]

@[simp] theorem arrival_succ (ω : ClockSpace) (n : ℕ) :
    arrival ω (n + 1) = arrival ω n + ω n := by
  exact Finset.sum_range_succ _ _

theorem measurable_arrival (n : ℕ) : Measurable (fun ω => arrival ω n) := by
  unfold arrival
  fun_prop

/-- Positive increments give a strictly ordered clock with no coincident arrivals. -/
theorem arrival_strictMono {ω : ClockSpace} (hω : ∀ n, 0 < ω n) : StrictMono (arrival ω) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [arrival_succ]
  linarith [hω n]

/-- On the actual product probability space, arrival times escape every finite
horizon almost surely. No non-explosion hypothesis is used. -/
theorem ae_arrival_tendsto (r : ℝ) (hr : 0 < r) :
    ∀ᵐ ω ∂waitingTimeLaw r hr, Tendsto (arrival ω) atTop atTop := by
  filter_upwards [ae_positive r hr, ae_frequently_one_lt r hr] with ω hpos hfreq
  apply (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => le_of_lt (hpos n))).mp
  intro hsum
  have hsmall : ∀ᶠ n in atTop, ω n < 1 :=
    hsum.tendsto_atTop_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨n, hn, hn'⟩ := (hfreq.and_eventually hsmall).exists
  linarith

/-- There are finitely many clock arrivals in every bounded time horizon,
simultaneously for all real horizons. This is the local finiteness required
before recursion through proposal events. -/
theorem ae_locally_finite (r : ℝ) (hr : 0 < r) :
    ∀ᵐ ω ∂waitingTimeLaw r hr,
      StrictMono (arrival ω) ∧ ∀ T : ℝ, {n : ℕ | arrival ω n ≤ T}.Finite := by
  filter_upwards [ae_positive r hr, ae_arrival_tendsto r hr] with ω hpos hdiv
  refine ⟨arrival_strictMono hpos, ?_⟩
  intro T
  have hevent : ∀ᶠ n in atTop, T < arrival ω n :=
    hdiv.eventually (eventually_gt_atTop T)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  apply (Set.finite_Iio N).subset
  intro n hn
  change n < N
  by_contra h
  exact (not_lt_of_ge hn) (hN n (Nat.le_of_not_gt h))

/-- The counting measure of positive-index arrivals. The deterministic origin
`arrival ω 0 = 0` is excluded from the proposal atoms. -/
def arrivalCountingMeasure (ω : ClockSpace) : Measure ℝ :=
  Measure.sum (fun n : ℕ => Measure.dirac (arrival ω (n + 1)))

/-- The random counting measure is measurable as a measure-valued map. -/
theorem measurable_arrivalCountingMeasure : Measurable arrivalCountingMeasure := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [arrivalCountingMeasure, Measure.sum_apply _ hs]
  apply Measurable.ennreal_tsum
  intro n
  exact (Measure.measurable_coe hs).comp
    (Measure.measurable_dirac.comp (measurable_arrival (n + 1)))

/-- A direct counting interpretation of the measure, including on arbitrary
measurable time sets. -/
theorem arrivalCountingMeasure_eq_map (ω : ClockSpace) :
    arrivalCountingMeasure ω =
      Measure.map (fun n : ℕ => arrival ω (n + 1)) Measure.count := by
  rw [Measure.count, Measure.map_sum (measurable_from_nat.aemeasurable)]
  simp only [Measure.map_dirac measurable_from_nat]
  rfl

/-- The constructed random counting measure has finite mass on every bounded
past interval, almost surely. This asserts local finiteness, not Poisson laws. -/
theorem ae_countingMeasure_locally_finite (r : ℝ) (hr : 0 < r) :
    ∀ᵐ ω ∂waitingTimeLaw r hr, ∀ T : ℝ, arrivalCountingMeasure ω (Iic T) < ∞ := by
  filter_upwards [ae_locally_finite r hr] with ω hω
  intro T
  rw [arrivalCountingMeasure_eq_map, Measure.map_apply measurable_from_nat measurableSet_Iic,
    Measure.count_apply_lt_top]
  exact Set.Finite.preimage (f := fun n : ℕ => n + 1)
    (fun _ _ _ _ h => Nat.succ_injective h) (hω.2 T)

end CarryingCapacity.CountableJumpProcess
