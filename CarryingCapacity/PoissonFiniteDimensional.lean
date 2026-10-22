import CarryingCapacity.PoissonRestart

/-!
# Finite-dimensional laws of the canonical exponential clock

Finite-grid laws are derived directly by renewal integration. The proof uses
the entire residual clock on first-wait survival, rather than inferring joint
independence from two-time independence.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace CarryingCapacity.PoissonFiniteDimensional
open CountableJumpProcess FrozenProcess PoissonClockLaw PoissonIncrements

/-- Successive cumulative-count requirements, starting from time a and count b. -/
def countProfile (a : ℝ) (b : ℕ) : List (ℝ × ℕ) → Set ClockSpace
  | [] => univ
  | (t,n) :: g => {ω | proposalCount ω (a+t) = b+n} ∩ countProfile (a+t) (b+n) g

theorem measurableSet_countProfile_offset (b : ℕ) (g : List (ℝ × ℕ)) :
    MeasurableSet {p : ℝ × ClockSpace | p.2 ∈ countProfile p.1 b g} := by
  induction g generalizing b with
  | nil => exact MeasurableSet.univ
  | cons p g ih =>
    rcases p with ⟨t,n⟩
    have hc : Measurable (fun p : ℝ × ClockSpace => proposalCount p.2 (p.1+t)) :=
      measurable_joint_proposalCount.comp (f := fun p : ℝ × ClockSpace => (p.2,p.1+t))
        (measurable_snd.prodMk (measurable_fst.add_const t))
    exact (hc (measurableSet_singleton (b+n))).inter
      ((ih (b+n)).preimage ((measurable_fst.add_const t).prodMk measurable_snd))

theorem measurableSet_countProfile (a : ℝ) (b : ℕ) (g : List (ℝ × ℕ)) :
    MeasurableSet (countProfile a b g) :=
  (measurableSet_countProfile_offset b g).preimage (measurable_const.prodMk measurable_id)

/-- Subtracting the first residual time translates every later profile horizon. -/
theorem countProfile_subtractHead (s : ℝ) (ω : ClockSpace) (a : ℝ) (b : ℕ)
    (g : List (ℝ × ℕ)) :
    subtractHead s ω ∈ countProfile a b g ↔ ω ∈ countProfile (s+a) b g := by
  induction g generalizing a b with
  | nil => rfl
  | cons p g ih =>
    rcases p with ⟨t,n⟩
    simp only [countProfile, mem_inter_iff, mem_setOf_eq, proposalCount_subtractHead,
      ih, add_assoc]

/-- After the first proposal, deleting its waiting time reduces all later counts by one. -/
theorem proposalCount_after_first {ω : ClockSpace}
    (hmono : StrictMono (arrival ω)) (hdiv : Tendsto (arrival ω) atTop atTop)
    (hsmono : StrictMono (arrival (shift 1 ω)))
    (hsdiv : Tendsto (arrival (shift 1 ω)) atTop atTop)
    (a : ℝ) (ha : 0 ≤ a) (hwa : ω 0 ≤ a) :
    proposalCount ω a = proposalCount (shift 1 ω) (a-ω 0) + 1 :=
  (proposalCount_succ_iff hmono hdiv hsmono hsdiv a ha _).mpr ⟨hwa,rfl⟩

/-- The same deletion translates all the cumulative requirements in a finite profile. -/
theorem countProfile_after_first {ω : ClockSpace}
    (hmono : StrictMono (arrival ω)) (hdiv : Tendsto (arrival ω) atTop atTop)
    (hsmono : StrictMono (arrival (shift 1 ω)))
    (hsdiv : Tendsto (arrival (shift 1 ω)) atTop atTop)
    (g : List (ℝ × ℕ)) (hg : ∀ p ∈ g, 0 ≤ p.1)
    (a : ℝ) (ha : 0 ≤ a) (hwa : ω 0 ≤ a) (b : ℕ) :
    ω ∈ countProfile a (b+1) g ↔ shift 1 ω ∈ countProfile (a-ω 0) b g := by
  induction g generalizing a b with
  | nil => rfl
  | cons p g ih =>
    rcases p with ⟨t,n⟩
    have ht : 0 ≤ t := hg (t,n) (by simp)
    have hrest : ∀ p ∈ g, 0 ≤ p.1 := fun p hp => hg p (List.mem_cons_of_mem _ hp)
    have hat : 0 ≤ a+t := add_nonneg ha ht
    have hwat : ω 0 ≤ a+t := hwa.trans (by linarith)
    have heq : a+t-ω 0 = (a-ω 0)+t := by ring
    simp only [countProfile, mem_inter_iff, mem_setOf_eq]
    rw [proposalCount_after_first hmono hdiv hsmono hsdiv (a+t) hat hwat,
      show b+1+n = (b+n)+1 by omega,
      Nat.add_right_cancel_iff, ih hrest (a+t) hat hwat (b+n), heq]

/-- Zero proposals in the first interval leaves the entire remaining profile
with its original law after translation. -/
theorem probability_profile_zero (r : ℝ) (hr : 0 < r) (s : ℝ) (hs : 0 ≤ s)
    (g : List (ℝ × ℕ)) :
    waitingTimeLaw r hr (countProfile 0 0 ((s,0)::g)) =
      ENNReal.ofReal (Real.exp (-(r*s))) * waitingTimeLaw r hr (countProfile 0 0 g) := by
  have h := congrArg (fun μ : Measure ClockSpace => μ (countProfile 0 0 g))
    (subtractHead_restrict_map r hr s hs)
  dsimp only at h
  rw [Measure.map_apply (measurable_subtractHead s) (measurableSet_countProfile 0 0 g),
    Measure.restrict_apply ((measurable_subtractHead s) (measurableSet_countProfile 0 0 g)),
    Measure.smul_apply, smul_eq_mul, exponential_survival r hr s hs] at h
  rw [← h]
  apply measure_congr
  filter_upwards [ae_locally_finite r hr] with ω hω
  change (proposalCount ω (0+s) = 0+0 ∧ ω ∈ countProfile (0+s) (0+0) g) =
    (subtractHead s ω ∈ countProfile 0 0 g ∧ s < ω 0)
  simp only [zero_add, countProfile_subtractHead, add_zero,
    proposalCount_eq_zero_iff hω.1 hω.2 s, and_comm]

/-- Renewal recurrence with an arbitrary finite tail profile. -/
theorem probability_profile_succ (r : ℝ) (hr : 0 < r) (s : ℝ) (hs : 0 ≤ s)
    (m : ℕ) (g : List (ℝ × ℕ)) (hg : ∀ p ∈ g, 0 ≤ p.1) :
    waitingTimeLaw r hr (countProfile 0 0 ((s,m+1)::g)) =
      ∫⁻ u in Iic s, waitingTimeLaw r hr (countProfile 0 0 ((s-u,m)::g)) ∂expMeasure r := by
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
  let S : Set (ℝ × ClockSpace) := {p | p.1 ≤ s ∧ p.2 ∈ countProfile 0 0 ((s-p.1,m)::g)}
  have hfirst : Measurable (fun p : ℝ × ClockSpace => proposalCount p.2 (s-p.1)) :=
    measurable_joint_proposalCount.comp (f := fun p : ℝ × ClockSpace => (p.2,s-p.1))
      (measurable_snd.prodMk (measurable_const.sub measurable_fst))
  have htail : MeasurableSet {p : ℝ × ClockSpace | p.2 ∈ countProfile (s-p.1) m g} :=
    (measurableSet_countProfile_offset m g).preimage
      ((measurable_const.sub measurable_fst).prodMk measurable_snd)
  have hS : MeasurableSet S := by
    simp only [S, countProfile, zero_add]
    change MeasurableSet {p : ℝ × ClockSpace | p.1 ≤ s ∧
      proposalCount p.2 (s-p.1) = m ∧ p.2 ∈ countProfile (s-p.1) m g}
    exact (measurableSet_le measurable_fst measurable_const).inter
      ((hfirst (measurableSet_singleton m)).inter htail)
  have heq : countProfile 0 0 ((s,m+1)::g) =ᵐ[waitingTimeLaw r hr]
      (fun ω : ClockSpace => (ω 0,shift 1 ω)) ⁻¹' S := by
    filter_upwards [ae_locally_finite r hr, ae_arrival_tendsto r hr, hsmono, hsdiv]
      with ω hω hdiv hm hd
    simp only [countProfile, S, zero_add, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_preimage]
    change (proposalCount ω s = m+1 ∧ ω ∈ countProfile s (m+1) g) =
      (ω 0 ≤ s ∧ proposalCount (shift 1 ω) (s-ω 0) = m ∧
        shift 1 ω ∈ countProfile (s-ω 0) m g)
    apply propext
    rw [proposalCount_succ_iff hω.1 hdiv hm hd s hs m]
    constructor
    · rintro ⟨⟨hws,hn⟩,hprof⟩
      exact ⟨hws,hn,(countProfile_after_first hω.1 hdiv hm hd g hg s hs hws m).mp hprof⟩
    · rintro ⟨hws,hn,hprof⟩
      exact ⟨⟨hws,hn⟩,(countProfile_after_first hω.1 hdiv hm hd g hg s hs hws m).mpr hprof⟩
  rw [measure_congr heq,
    ← Measure.map_apply ((measurable_pi_apply 0).prodMk (measurable_shift 1)) hS,
    head_tail_map, Measure.prod_apply hS, ← lintegral_indicator measurableSet_Iic]
  apply lintegral_congr
  intro u
  by_cases hu : u ≤ s <;> simp [S,hu,Set.indicator,mem_Iic]

/-- Product of the prescribed Poisson masses over a finite interval list. -/
def profileMass (r : ℝ) : List (ℝ × ℕ) → ℝ≥0∞
  | [] => 1
  | (s,m) :: g => ENNReal.ofReal (Real.exp (-(r*s)) * (r*s)^m / (m.factorial : ℝ)) * profileMass r g

/-- Full finite-dimensional factorization, proved by grid-length and first-count induction. -/
theorem probability_countProfile (r : ℝ) (hr : 0 < r) (g : List (ℝ × ℕ))
    (hg : ∀ p ∈ g, 0 ≤ p.1) :
    waitingTimeLaw r hr (countProfile 0 0 g) = profileMass r g := by
  induction g with
  | nil => simp [countProfile,profileMass]
  | cons p g ih =>
    rcases p with ⟨s,m⟩
    have hs : 0 ≤ s := hg (s,m) (by simp)
    have hrest : ∀ p ∈ g, 0 ≤ p.1 := fun p hp => hg p (List.mem_cons_of_mem _ hp)
    have htail := ih hrest
    have hcons : ∀ (k : ℕ) (a : ℝ), 0 ≤ a →
        waitingTimeLaw r hr (countProfile 0 0 ((a,k)::g)) = profileMass r ((a,k)::g) := by
      intro k
      induction k with
      | zero =>
        intro a ha
        rw [probability_profile_zero r hr a ha g,htail]
        simp [profileMass]
      | succ k ihk =>
        intro a ha
        rw [probability_profile_succ r hr a ha k g hrest]
        calc
          _ = ∫⁻ u in Iic a,
              ENNReal.ofReal (Real.exp (-(r*(a-u))) * (r*(a-u))^k / (k.factorial : ℝ)) *
              profileMass r g ∂expMeasure r := by
            apply setLIntegral_congr_fun measurableSet_Iic
            exact ae_of_all _ (fun u hu => ihk (a-u) (sub_nonneg.mpr hu))
          _ = _ := by
            rw [lintegral_mul_const _ (by fun_prop),
              exponential_renewal_integral r hr a ha k,poisson_renewal_integral]
            rfl
    exact hcons m s hs

/-- Successive interval increment requirements, starting at time a. -/
def incrementProfile (a : ℝ) : List (ℝ × ℕ) → Set ClockSpace
  | [] => univ
  | (t,n) :: g => {ω | increment ω a t = n} ∩ incrementProfile (a+t) g

theorem countProfile_iff_incrementProfile {ω : ClockSpace}
    (hmono : Monotone (proposalCount ω)) (g : List (ℝ × ℕ))
    (hg : ∀ p ∈ g, 0 ≤ p.1) (a : ℝ) (b : ℕ) (hb : proposalCount ω a = b) :
    ω ∈ countProfile a b g ↔ ω ∈ incrementProfile a g := by
  induction g generalizing a b with
  | nil => rfl
  | cons p g ih =>
    rcases p with ⟨t,n⟩
    have ht : 0 ≤ t := hg (t,n) (by simp)
    have hrest : ∀ p ∈ g, 0 ≤ p.1 := fun p hp => hg p (List.mem_cons_of_mem _ hp)
    have hle := hmono (show a ≤ a+t by linarith)
    have hfirst : proposalCount ω (a+t) = b+n ↔ increment ω a t = n := by
      dsimp [increment]
      omega
    simp only [countProfile, incrementProfile, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨hn,hg⟩
      exact ⟨hfirst.mp hn,(ih hrest (a+t) (b+n) hn).mp hg⟩
    · rintro ⟨hn,hg⟩
      exact ⟨hfirst.mpr hn,(ih hrest (a+t) (b+n) (hfirst.mpr hn)).mpr hg⟩

/-- Exact joint atom probabilities for all increments in an arbitrary finite grid. -/
theorem probability_incrementProfile (r : ℝ) (hr : 0 < r) (g : List (ℝ × ℕ))
    (hg : ∀ p ∈ g, 0 ≤ p.1) :
    waitingTimeLaw r hr (incrementProfile 0 g) = profileMass r g := by
  rw [← probability_countProfile r hr g hg]
  apply measure_congr
  filter_upwards [ae_locally_finite r hr, ae_positive r hr] with ω hω hpos
  have hzero : proposalCount ω 0 = 0 :=
    (proposalCount_eq_zero_iff hω.1 hω.2 0).mpr (hpos 0)
  exact propext (countProfile_iff_incrementProfile (proposalCount_mono hω.2) g hg 0 0 hzero).symm

/-- The finite vector of successive increments, with the listed interval lengths. -/
def gridIncrements : {k : ℕ} → (Fin k → ℝ) → ℝ → ClockSpace → (Fin k → ℕ)
  | 0, _, _, _ => Fin.elim0
  | _+1, t, a, ω => Fin.cons (increment ω a (t 0))
      (gridIncrements (fun i => t i.succ) (a+t 0) ω)

theorem measurable_gridIncrements {k : ℕ} (t : Fin k → ℝ) (a : ℝ) :
    Measurable (gridIncrements t a) := by
  induction k generalizing a with
  | zero => exact measurable_pi_lambda _ (fun i => i.elim0)
  | succ k ih =>
    apply measurable_pi_lambda
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_increment a (t 0)
    · exact (measurable_pi_apply j).comp (ih (fun i => t i.succ) (a+t 0))

theorem gridIncrements_eq_iff_profile {k : ℕ} (t : Fin k → ℝ) (a : ℝ)
    (ω : ClockSpace) (n : Fin k → ℕ) :
    gridIncrements t a ω = n ↔ ω ∈ incrementProfile a (List.ofFn (fun i => (t i,n i))) := by
  induction k generalizing a with
  | zero => simp [incrementProfile, Subsingleton.elim (gridIncrements t a ω) n]
  | succ k ih =>
    rw [List.ofFn_succ]
    change Fin.cons (increment ω a (t 0)) (gridIncrements (fun i => t i.succ) (a+t 0) ω) = n ↔ _
    conv_lhs => rw [← Fin.cons_self_tail n]
    rw [Fin.cons_inj,ih]
    rfl

theorem profileMass_ofFn {k : ℕ} (r : ℝ) (t : Fin k → ℝ) (n : Fin k → ℕ) :
    profileMass r (List.ofFn (fun i => (t i,n i))) =
      ∏ i, ENNReal.ofReal (Real.exp (-(r*t i)) * (r*t i)^(n i) / ((n i).factorial : ℝ)) := by
  induction k with
  | zero => simp [profileMass]
  | succ k ih => rw [List.ofFn_succ,profileMass,Fin.prod_univ_succ,ih]

/-- The actual finite-dimensional increment law is a product of Poisson laws.
The interval lengths may be zero. This is proved from joint events, not pairwise independence. -/
theorem gridIncrements_map (r : ℝ) (hr : 0 < r) {k : ℕ} (t : Fin k → ℝ)
    (ht : ∀ i, 0 ≤ t i) :
    Measure.map (gridIncrements t 0) (waitingTimeLaw r hr) =
      Measure.pi (fun i => poissonMeasure ⟨r*t i,mul_nonneg hr.le (ht i)⟩) := by
  apply Measure.ext_of_singleton
  intro n
  rw [Measure.map_apply (measurable_gridIncrements t 0) (measurableSet_singleton n)]
  have heq : gridIncrements t 0 ⁻¹' {n} = incrementProfile 0 (List.ofFn (fun i => (t i,n i))) := by
    ext ω
    exact gridIncrements_eq_iff_profile t 0 ω n
  rw [heq, probability_incrementProfile r hr _ (by
    intro p hp
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
    exact ht i), profileMass_ofFn, ← Set.univ_pi_singleton n,Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro i hi
  change _ = (poissonPMF ⟨r*t i,mul_nonneg hr.le (ht i)⟩).toMeasure {n i}
  rw [PMF.toMeasure_apply_singleton _ (n i) (measurableSet_singleton (n i))]
  rfl

/-- Each coordinate of the grid has the Poisson law of its interval length,
including grids with an arbitrary nonnegative initial offset. -/
theorem gridIncrements_marginal (r : ℝ) (hr : 0 < r) {k : ℕ} (t : Fin k → ℝ)
    (ht : ∀ i, 0 ≤ t i) (a : ℝ) (ha : 0 ≤ a) (i : Fin k) :
    Measure.map (fun ω => gridIncrements t a ω i) (waitingTimeLaw r hr) =
      poissonMeasure ⟨r*t i,mul_nonneg hr.le (ht i)⟩ := by
  induction k generalizing a with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact increment_map r hr a (t 0) ha (ht 0)
    · exact ih (fun i => t i.succ) (fun i => ht i.succ) (a+t 0) (add_nonneg ha (ht 0)) j

/-- All the successive increments of a finite grid starting at zero are mutually independent. -/
theorem independent_gridIncrements_zero (r : ℝ) (hr : 0 < r) {k : ℕ}
    (t : Fin k → ℝ) (ht : ∀ i, 0 ≤ t i) :
    iIndepFun (fun i ω => gridIncrements t 0 ω i) (waitingTimeLaw r hr) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i =>
    ((measurable_pi_apply i).comp (measurable_gridIncrements t 0)).aemeasurable)).mpr
  change Measure.map (gridIncrements t 0) (waitingTimeLaw r hr) =
    Measure.pi (fun i => Measure.map (fun ω => gridIncrements t 0 ω i) (waitingTimeLaw r hr))
  rw [gridIncrements_map r hr t ht]
  congr 1
  funext i
  exact (gridIncrements_marginal r hr t ht 0 le_rfl i).symm

/-- Mutual independence holds for every finite grid at every nonnegative starting time.
This is a statement about all finite collections, not just each pair of increments. -/
theorem independent_gridIncrements (r : ℝ) (hr : 0 < r) {k : ℕ}
    (t : Fin k → ℝ) (ht : ∀ i, 0 ≤ t i) (a : ℝ) (ha : 0 ≤ a) :
    iIndepFun (fun i ω => gridIncrements t a ω i) (waitingTimeLaw r hr) := by
  let extended : Fin (k+1) → ℝ := Fin.cons a t
  have hnonneg : ∀ i, 0 ≤ extended i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ha
    · exact ht j
  have hind := independent_gridIncrements_zero r hr extended hnonneg
  have htail := iIndepFun.precomp (Fin.succ_injective k) hind
  simpa only [extended, gridIncrements, Fin.cons_zero, Fin.cons_succ, zero_add] using htail

/-- Full stationary independent-increment law for any finite grid and nonnegative offset. -/
theorem gridIncrements_map_offset (r : ℝ) (hr : 0 < r) {k : ℕ}
    (t : Fin k → ℝ) (ht : ∀ i, 0 ≤ t i) (a : ℝ) (ha : 0 ≤ a) :
    Measure.map (gridIncrements t a) (waitingTimeLaw r hr) =
      Measure.pi (fun i => poissonMeasure ⟨r*t i,mul_nonneg hr.le (ht i)⟩) := by
  have h := (iIndepFun_iff_map_fun_eq_pi_map (fun i =>
    ((measurable_pi_apply i).comp (measurable_gridIncrements t a)).aemeasurable)).mp
      (independent_gridIncrements r hr t ht a ha)
  change Measure.map (gridIncrements t a) (waitingTimeLaw r hr) =
    Measure.pi (fun i => Measure.map (fun ω => gridIncrements t a ω i) (waitingTimeLaw r hr)) at h
  rw [h]
  congr 1
  funext i
  exact gridIncrements_marginal r hr t ht a ha i

/-- A grid given by interval lengths agrees with the usual differences of counts
at its successive endpoint times. -/
theorem gridIncrements_at_times {k : ℕ} (u : Fin (k+1) → ℝ) (ω : ClockSpace) :
    gridIncrements (fun i : Fin k => u i.succ - u i.castSucc) (u 0) ω =
      (fun i => proposalCount ω (u i.succ) - proposalCount ω (u i.castSucc)) := by
  induction k with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    funext i
    have htime : u 0 + (u (Fin.succ 0) - u 0) = u (Fin.succ 0) := by ring
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [gridIncrements, Fin.cons_zero, increment, Fin.castSucc_zero, htime]
    · have h := congrFun (ih (fun i => u i.succ)) j
      simpa only [gridIncrements, Fin.cons_succ, Fin.castSucc_zero, htime, Fin.succ_castSucc] using h

/-- Mutual independence of the conventional count differences on every nondecreasing
finite grid of nonnegative times. Equal adjacent times give deterministic zero increments. -/
theorem independent_increments_at_times (r : ℝ) (hr : 0 < r) {k : ℕ}
    (u : Fin (k+1) → ℝ) (hu : Monotone u) (hu0 : 0 ≤ u 0) :
    iIndepFun (fun i : Fin k => fun ω =>
      proposalCount ω (u i.succ) - proposalCount ω (u i.castSucc)) (waitingTimeLaw r hr) := by
  have ht : ∀ i : Fin k, 0 ≤ u i.succ - u i.castSucc :=
    fun i => sub_nonneg.mpr (hu (Fin.castSucc_le_succ i))
  have h := independent_gridIncrements r hr (fun i : Fin k => u i.succ - u i.castSucc)
    ht (u 0) hu0
  simpa only [gridIncrements_at_times] using h

/-- The conventional increment vector has the full product Poisson law, with parameter
r times the length of each interval. -/
theorem increments_at_times_map (r : ℝ) (hr : 0 < r) {k : ℕ}
    (u : Fin (k+1) → ℝ) (hu : Monotone u) (hu0 : 0 ≤ u 0) :
    Measure.map (fun ω => fun i : Fin k =>
      proposalCount ω (u i.succ) - proposalCount ω (u i.castSucc)) (waitingTimeLaw r hr) =
      Measure.pi (fun i : Fin k => poissonMeasure
        ⟨r*(u i.succ-u i.castSucc), mul_nonneg hr.le (sub_nonneg.mpr (hu (Fin.castSucc_le_succ i)))⟩) := by
  have ht : ∀ i : Fin k, 0 ≤ u i.succ - u i.castSucc :=
    fun i => sub_nonneg.mpr (hu (Fin.castSucc_le_succ i))
  have h := gridIncrements_map_offset r hr (fun i : Fin k => u i.succ-u i.castSucc) ht (u 0) hu0
  have heq : gridIncrements (fun i : Fin k => u i.succ-u i.castSucc) (u 0) =
      fun ω => fun i => proposalCount ω (u i.succ) - proposalCount ω (u i.castSucc) :=
    funext (gridIncrements_at_times u)
  rwa [heq] at h

end CarryingCapacity.PoissonFiniteDimensional
