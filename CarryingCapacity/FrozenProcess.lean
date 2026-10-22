import CarryingCapacity.CountableJumpProcess
import CarryingCapacity.Freezing

/-!
# Frozen state paths on a canonical marked-clock probability space

The sample law combines the actual exponential clock with independent iid
uniform proposals: a uniform jump label and a uniform number in [0,1]. The
state at time t is obtained by applying finitely many frozen updates. The
measurability results concern these defined functions, not assumed processes.
Identification of the compensator and the Poisson SDE law remains separate.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace CarryingCapacity.FrozenProcess
open CountableJumpProcess

/-- Lebesgue probability on the unit interval. -/
def uniformUnit : Measure ℝ := volume.restrict (Icc 0 1)

instance uniformUnit_probability : IsProbabilityMeasure uniformUnit where
  measure_univ := by
    simp [uniformUnit, Real.volume_Icc]

section MarkedLaw

variable (J : Type*) [Fintype J] [Nonempty J] [MeasurableSpace J]

/-- One proposal has a uniform label and independent uniform thinning mark. -/
def markLaw : Measure (J × ℝ) := (PMF.uniformOfFintype J).toMeasure.prod uniformUnit

instance markLaw_probability : IsProbabilityMeasure (markLaw J) := by
  unfold markLaw
  infer_instance

def marksLaw : Measure (ℕ → J × ℝ) := Measure.infinitePi (fun _ : ℕ => markLaw J)

instance marksLaw_probability : IsProbabilityMeasure (marksLaw J) := by
  unfold marksLaw
  infer_instance

abbrev Sample := ClockSpace × (ℕ → J × ℝ)

/-- The full probability law makes the complete clock and mark sequences independent. -/
def law (r : ℝ) (hr : 0 < r) : Measure (Sample J) :=
  (waitingTimeLaw r hr).prod (marksLaw J)

instance law_probability (r : ℝ) (hr : 0 < r) : IsProbabilityMeasure (law J r hr) := by
  unfold law
  infer_instance

theorem clock_map (r : ℝ) (hr : 0 < r) :
    Measure.map Prod.fst (law J r hr) = waitingTimeLaw r hr := by
  simp [law, Measure.map_fst_prod]

theorem marks_map (r : ℝ) (hr : 0 < r) :
    Measure.map Prod.snd (law J r hr) = marksLaw J := by
  simp [law, Measure.map_snd_prod]

theorem independent_clock_marks (r : ℝ) (hr : 0 < r) :
    IndepFun Prod.fst Prod.snd (law J r hr) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
    measurable_snd.aemeasurable).mpr
  rw [clock_map, marks_map]
  change Measure.map id (law J r hr) = _
  rw [Measure.map_id]
  rfl

theorem ae_clock (r : ℝ) (hr : 0 < r) :
    ∀ᵐ ω ∂law J r hr, StrictMono (arrival ω.1) ∧
      ∀ T : ℝ, {n : ℕ | arrival ω.1 n ≤ T}.Finite := by
  have h := ae_locally_finite r hr
  rw [← clock_map J r hr] at h
  exact ae_of_ae_map measurable_fst.aemeasurable h

theorem ae_clock_tendsto (r : ℝ) (hr : 0 < r) :
    ∀ᵐ ω ∂law J r hr, Tendsto (arrival ω.1) atTop atTop := by
  have h := ae_arrival_tendsto r hr
  rw [← clock_map J r hr] at h
  exact ae_of_ae_map measurable_fst.aemeasurable h

end MarkedLaw

/-- Number of positive-index proposals up to time t. On the null set of bad
clocks `ncard` supplies a total definition; all path properties use the proved
full-measure clock event. -/
def proposalCount (ω : ClockSpace) (t : ℝ) : ℕ :=
  {n : ℕ | arrival ω (n + 1) ≤ t}.ncard

theorem measurable_proposalCount (t : ℝ) : Measurable (fun ω => proposalCount ω t) := by
  apply measurable_ncard.comp
  apply measurable_pi_lambda
  intro n
  apply measurable_to_prop
  simpa using measurableSet_le (measurable_arrival (n + 1)) measurable_const

theorem proposalCount_mono {ω : ClockSpace}
    (hfin : ∀ T : ℝ, {n : ℕ | arrival ω n ≤ T}.Finite) : Monotone (proposalCount ω) := by
  intro s t hst
  apply Set.ncard_le_ncard
  · intro n hn
    exact hn.trans hst
  · exact Set.Finite.preimage (f := fun n : ℕ => n + 1)
      (fun _ _ _ _ h => Nat.succ_injective h) (hfin t)

/-- The count is constant from one arrival through, but excluding, the next. -/
theorem proposalCount_between {ω : ClockSpace} (hmono : StrictMono (arrival ω))
    {n : ℕ} {t : ℝ} (hlo : arrival ω n ≤ t) (hhi : t < arrival ω (n + 1)) :
    proposalCount ω t = n := by
  have heq : {k : ℕ | arrival ω (k + 1) ≤ t} = Iio n := by
    ext k
    constructor
    · intro hk
      by_contra h
      change ¬ k < n at h
      have hnk : n + 1 ≤ k + 1 := by omega
      exact (not_lt_of_ge hk) (hhi.trans_le (hmono.monotone hnk))
    · intro hk
      exact (hmono.monotone (by simpa using hk)).trans hlo
  rw [proposalCount, heq]
  have hIio : Iio n = (Finset.range n : Set ℕ) := by ext k; simp
  rw [hIio, Set.ncard_coe_Finset, Finset.card_range]

/-- Every nonnegative time lies between consecutive arrivals of an
increasing clock which tends to infinity. -/
theorem exists_arrival_interval {ω : ClockSpace}
    (hdiv : Tendsto (arrival ω) atTop atTop) {t : ℝ} (ht : 0 ≤ t) :
    ∃ n, arrival ω n ≤ t ∧ t < arrival ω (n + 1) := by
  have hex : ∃ n, t < arrival ω n :=
    (hdiv.eventually (eventually_gt_atTop t)).exists
  have hpos : 0 < Nat.find hex := by
    by_contra h
    have hzero : Nat.find hex = 0 := by omega
    have h := Nat.find_spec hex
    rw [hzero, arrival_zero] at h
    linarith
  have heq : Nat.find hex - 1 + 1 = Nat.find hex := by omega
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · by_contra h
    have hmin := Nat.find_min' hex (lt_of_not_ge h)
    omega
  · rw [heq]
    exact Nat.find_spec hex

section StateRecursion

variable {E M J : Type*} [DecidableEq E] [Fintype J]
  (active : Finset E) (jump : J → E → E) (decode : E → M → Option J)

/-- State after n proposals, with the freezing rule applied at every step. -/
def stateAfter (x : E) (marks : ℕ → M) : ℕ → E
  | 0 => x
  | n + 1 => Freezing.frozenStep active jump decode (stateAfter x marks n) (marks n)

omit [Fintype J] in
@[simp] theorem stateAfter_zero (x : E) (marks : ℕ → M) :
    stateAfter active jump decode x marks 0 = x := rfl

omit [Fintype J] in
/-- The indexed recursion agrees with the already-checked finite-list recursion. -/
theorem stateAfter_eq_run (x : E) (marks : ℕ → M) (n : ℕ) :
    stateAfter active jump decode x marks n =
      Freezing.run active jump decode x (List.ofFn (fun i : Fin n => marks i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, Freezing.run_append]
    simp only [Fin.coe_castSucc, Fin.val_last, Freezing.run, stateAfter, ih]

omit [Fintype J] in
theorem stateAfter_frozen (x : E) (marks : ℕ → M) {n m : ℕ} (hnm : n ≤ m)
    (hout : stateAfter active jump decode x marks n ∉ active) :
    stateAfter active jump decode x marks m = stateAfter active jump decode x marks n := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    simp only [stateAfter, ih]
    exact Freezing.frozenStep_outside active jump decode hout (marks m)

/-- Continuous-time state obtained by running exactly the proposals seen by t. -/
def process (x : E) (ω : ClockSpace × (ℕ → M)) (t : ℝ) : E :=
  stateAfter active jump decode x ω.2 (proposalCount ω.1 t)

omit [Fintype J] in
theorem process_frozen (x : E) (ω : ClockSpace × (ℕ → M))
    (hfin : ∀ T : ℝ, {n : ℕ | arrival ω.1 n ≤ T}.Finite)
    {s t : ℝ} (hst : s ≤ t) (hout : process active jump decode x ω s ∉ active) :
    process active jump decode x ω t = process active jump decode x ω s := by
  exact stateAfter_frozen active jump decode x ω.2 (proposalCount_mono hfin hst) hout

theorem process_range (x : E) (ω : ClockSpace × (ℕ → M)) (t : ℝ) :
    process active jump decode x ω t ∈ Freezing.oneStepEnlargement active jump ∨
      process active jump decode x ω t = x := by
  unfold process
  rw [stateAfter_eq_run]
  exact Freezing.run_mem_or_eq_initial active jump decode x _

omit [Fintype J] in
/-- On each interarrival interval the process is exactly one fixed recursive state. -/
theorem process_between (x : E) (ω : ClockSpace × (ℕ → M))
    (hmono : StrictMono (arrival ω.1)) {n : ℕ} {t : ℝ}
    (hlo : arrival ω.1 n ≤ t) (hhi : t < arrival ω.1 (n + 1)) :
    process active jump decode x ω t = stateAfter active jump decode x ω.2 n := by
  unfold process
  rw [proposalCount_between hmono hlo hhi]

omit [Fintype J] in
/-- The path is constant on a nonempty right interval at every nonnegative time. -/
theorem process_right_constant (x : E) (ω : ClockSpace × (ℕ → M))
    (hmono : StrictMono (arrival ω.1)) (hdiv : Tendsto (arrival ω.1) atTop atTop)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ b, t < b ∧ ∀ u ∈ Ico t b,
      process active jump decode x ω u = process active jump decode x ω t := by
  obtain ⟨n, hlo, hhi⟩ := exists_arrival_interval hdiv ht
  refine ⟨arrival ω.1 (n + 1), hhi, ?_⟩
  intro u hu
  rw [process_between active jump decode x ω hmono (hlo.trans hu.1) hu.2,
    process_between active jump decode x ω hmono hlo hhi]

omit [Fintype J] in
/-- Every positive time has a left interval on which the path is constant. -/
theorem process_left_constant (x : E) (ω : ClockSpace × (ℕ → M))
    (hmono : StrictMono (arrival ω.1)) (hdiv : Tendsto (arrival ω.1) atTop atTop)
    {t : ℝ} (ht : 0 < t) :
    ∃ b y, b < t ∧ ∀ u ∈ Ico b t, process active jump decode x ω u = y := by
  have hex : ∃ n, t ≤ arrival ω.1 n := by
    obtain ⟨n, hn⟩ := (hdiv.eventually (eventually_gt_atTop t)).exists
    exact ⟨n, le_of_lt hn⟩
  have hpos : 0 < Nat.find hex := by
    by_contra h
    have hzero : Nat.find hex = 0 := by omega
    have h := Nat.find_spec hex
    rw [hzero, arrival_zero] at h
    linarith
  have heq : Nat.find hex - 1 + 1 = Nat.find hex := by omega
  have hprev : arrival ω.1 (Nat.find hex - 1) < t := by
    by_contra h
    have hmin := Nat.find_min' hex (le_of_not_gt h)
    omega
  refine ⟨arrival ω.1 (Nat.find hex - 1),
    stateAfter active jump decode x ω.2 (Nat.find hex - 1), hprev, ?_⟩
  intro u hu
  apply process_between active jump decode x ω hmono hu.1
  rw [heq]
  exact hu.2.trans_le (Nat.find_spec hex)

omit [Fintype J] in
/-- Right continuity and existence of left limits follow from the constructed
interarrival intervals, for any topology on the state space. -/
theorem process_cadlag [TopologicalSpace E] (x : E) (ω : ClockSpace × (ℕ → M))
    (hmono : StrictMono (arrival ω.1)) (hdiv : Tendsto (arrival ω.1) atTop atTop) :
    (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (process active jump decode x ω) (Ici t) t) ∧
    (∀ t : ℝ, 0 < t → ∃ y : E,
      Tendsto (process active jump decode x ω) (nhdsWithin t (Iio t)) (nhds y)) := by
  constructor
  · intro t ht
    obtain ⟨b, hbt, hb⟩ := process_right_constant active jump decode x ω hmono hdiv ht
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hbt)] with u hu hub
    exact (hb u ⟨hu, hub⟩).symm
  · intro t ht
    obtain ⟨b, y, hbt, hb⟩ := process_left_constant active jump decode x ω hmono hdiv ht
    refine ⟨y, ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hbt)] with u hu hbu
    exact (hb u ⟨le_of_lt hbu, hu⟩).symm

variable [MeasurableSpace E] [MeasurableSpace M]

omit [Fintype J] in
/-- A measurable update gives a measurable finite recursion. -/
theorem measurable_stateAfter
    (hstep : Measurable (fun p : E × M => Freezing.frozenStep active jump decode p.1 p.2))
    (x : E) (n : ℕ) : Measurable (fun marks => stateAfter active jump decode x marks n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact hstep.comp (ih.prodMk (measurable_pi_apply n))

omit [Fintype J] in
/-- The state at each deterministic time is an actual measurable random variable. -/
theorem measurable_process
    (hstep : Measurable (fun p : E × M => Freezing.frozenStep active jump decode p.1 p.2))
    (x : E) (t : ℝ) : Measurable (fun ω => process active jump decode x ω t) := by
  have h : Measurable (fun p : (ℕ → M) × ℕ => stateAfter active jump decode x p.1 p.2) :=
    measurable_from_prod_countable (fun n => measurable_stateAfter active jump decode hstep x n)
  exact h.comp (measurable_snd.prodMk ((measurable_proposalCount t).comp measurable_fst))

end StateRecursion

section Thinning

variable {E J : Type*} [DecidableEq E] [Countable E]
  [MeasurableSpace E] [MeasurableSingletonClass E]
  [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]

/-- State-dependent acceptance of a uniform mark. With `C > 0` and `0 ≤ rate j x ≤ C`,
the conditional acceptance probability is `rate j x / C`. The process
construction itself is defined for every real-valued rate function. -/
def thinningDecode (C : ℝ) (rate : J → E → ℝ) (x : E) (mark : J × ℝ) : Option J :=
  if C * mark.2 ≤ rate mark.1 x then some mark.1 else none

omit [Nonempty J] in
/-- The actual thinning update is measurable, using countability of states and
labels and the measurable threshold event in the uniform mark. -/
theorem measurable_thinningStep (active : Finset E) (jump : J → E → E)
    (C : ℝ) (rate : J → E → ℝ) :
    Measurable (fun p : E × (J × ℝ) =>
      Freezing.frozenStep active jump (thinningDecode C rate) p.1 p.2) := by
  classical
  have hrate : Measurable (fun p : E × (J × ℝ) => rate p.2.1 p.1) :=
    (measurable_of_countable (fun p : E × J => rate p.2 p.1)).comp
      (measurable_fst.prodMk measurable_snd.fst)
  have hjump : Measurable (fun p : E × (J × ℝ) => jump p.2.1 p.1) :=
    (measurable_of_countable (fun p : E × J => jump p.2 p.1)).comp
      (measurable_fst.prodMk measurable_snd.fst)
  have htest : MeasurableSet {p : E × (J × ℝ) | C * p.2.2 ≤ rate p.2.1 p.1} :=
    measurableSet_le (measurable_const.mul measurable_snd.snd) hrate
  have hactive : MeasurableSet {p : E × (J × ℝ) | p.1 ∈ active} :=
    (Finset.measurableSet active).preimage measurable_fst
  have hinner : Measurable (fun p : E × (J × ℝ) =>
      if C * p.2.2 ≤ rate p.2.1 p.1 then jump p.2.1 p.1 else p.1) :=
    hjump.ite htest measurable_fst
  have h : Measurable (fun p : E × (J × ℝ) =>
      if p.1 ∈ active then
        (if C * p.2.2 ≤ rate p.2.1 p.1 then jump p.2.1 p.1 else p.1)
      else p.1) := hinner.ite hactive measurable_fst
  convert h using 1
  funext p
  simp only [Freezing.frozenStep, thinningDecode]
  split_ifs <;> rfl

/-- An explicit frozen state process on the canonical marked-clock space. -/
def thinningProcess (active : Finset E) (jump : J → E → E) (C : ℝ)
    (rate : J → E → ℝ) (x : E) : Sample J → ℝ → E :=
  process active jump (thinningDecode C rate) x

omit [Nonempty J] in
theorem measurable_thinningProcess (active : Finset E) (jump : J → E → E)
    (C : ℝ) (rate : J → E → ℝ) (x : E) (t : ℝ) :
    Measurable (fun ω => thinningProcess active jump C rate x ω t) :=
  measurable_process active jump (thinningDecode C rate)
    (measurable_thinningStep active jump C rate) x t

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [MeasurableSingletonClass J] in
/-- The actual random frozen paths are right-continuous with left limits,
almost surely, as a consequence of their exponential construction. -/
theorem ae_thinningProcess_cadlag [TopologicalSpace E]
    (active : Finset E) (jump : J → E → E) (C : ℝ) (rate : J → E → ℝ)
    (x : E) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ ω ∂law J r hr,
      (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt
        (thinningProcess active jump C rate x ω) (Ici t) t) ∧
      (∀ t : ℝ, 0 < t → ∃ y : E, Tendsto
        (thinningProcess active jump C rate x ω) (nhdsWithin t (Iio t)) (nhds y)) := by
  filter_upwards [ae_clock J r hr, ae_clock_tendsto J r hr] with ω hclock hdiv
  exact process_cadlag active jump (thinningDecode C rate) x ω hclock.1 hdiv

omit [Countable E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [MeasurableSingletonClass J] in
/-- Once an actual path leaves the active set, it remains at that exit state. -/
theorem ae_thinningProcess_frozen (active : Finset E) (jump : J → E → E)
    (C : ℝ) (rate : J → E → ℝ) (x : E) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ ω ∂law J r hr, ∀ s t : ℝ, s ≤ t →
      thinningProcess active jump C rate x ω s ∉ active →
      thinningProcess active jump C rate x ω t = thinningProcess active jump C rate x ω s := by
  filter_upwards [ae_clock J r hr] with ω hclock
  intro s t hst hout
  exact process_frozen active jump (thinningDecode C rate) x ω hclock.2 hst hout

end Thinning

end CarryingCapacity.FrozenProcess
