import Mathlib

/-!
# Skorokhod J1 time-change distance on actual paths

Time changes are increasing homeomorphisms of the entire closed time interval.
Both uniform time and state errors are capped at one. The small-radius
criterion identifies the ordinary J1 time-change topology. Paths retain their
actual pointwise values; separation is proved using right continuity.
-/

noncomputable section
open Set Filter
open scoped Topology ENNReal NNReal

namespace CarryingCapacity.SkorokhodJ1

abbrev Time (T : ℝ≥0) := Icc (0 : ℝ) (T : ℝ)
abbrev TimeChange (T : ℝ≥0) := Time T ≃o Time T

theorem timeChange_continuous {T : ℝ≥0} (e : TimeChange T) : Continuous e :=
  e.toHomeomorph.continuous

theorem timeChange_symm_continuous {T : ℝ≥0} (e : TimeChange T) : Continuous e.symm :=
  e.symm.toHomeomorph.continuous

/-- Càdlàg paths with actual pointwise equality. The strict-left filter is
empty at zero, so its left-limit condition is vacuous there. -/
structure Path (T : ℝ≥0) (E : Type*) [TopologicalSpace E] where
  toFun : Time T → E
  right_continuous : ∀ t, ContinuousWithinAt toFun (Ici t) t
  left_limits : ∀ t, ∃ a, Tendsto toFun (𝓝[<] t) (𝓝 a)

instance {T : ℝ≥0} {E : Type*} [TopologicalSpace E] : CoeFun (Path T E) (fun _ => Time T → E) :=
  ⟨Path.toFun⟩

@[ext] theorem Path.ext {T : ℝ≥0} {E : Type*} [TopologicalSpace E]
    {x y : Path T E} (h : ∀ t, x t = y t) : x = y := by
  cases x
  cases y
  congr
  exact funext h

def cappedEDist {E : Type*} [PseudoEMetricSpace E] (x y : E) : ℝ≥0∞ := min 1 (edist x y)

@[simp] theorem cappedEDist_self {E : Type*} [PseudoEMetricSpace E] (x : E) :
    cappedEDist x x = 0 := by simp [cappedEDist]

theorem cappedEDist_comm {E : Type*} [PseudoEMetricSpace E] (x y : E) :
    cappedEDist x y = cappedEDist y x := by simp only [cappedEDist, edist_comm]

theorem cappedEDist_le_one {E : Type*} [PseudoEMetricSpace E] (x y : E) :
    cappedEDist x y ≤ 1 := min_le_left _ _

theorem cappedEDist_triangle {E : Type*} [PseudoEMetricSpace E] (x y z : E) :
    cappedEDist x z ≤ cappedEDist x y + cappedEDist y z := by
  by_cases hxy : edist x y ≤ 1
  · by_cases hyz : edist y z ≤ 1
    · simpa only [cappedEDist, min_eq_right hxy, min_eq_right hyz] using
        (min_le_right (1 : ℝ≥0∞) (edist x z)).trans (edist_triangle x y z)
    · have hyz' : 1 ≤ edist y z := (lt_of_not_ge hyz).le
      calc
        _ ≤ 1 := cappedEDist_le_one x z
        _ ≤ cappedEDist x y + 1 := le_add_left le_rfl
        _ = _ := by simp only [cappedEDist, min_eq_left hyz']
  · have hxy' : 1 ≤ edist x y := (lt_of_not_ge hxy).le
    calc
      _ ≤ 1 := cappedEDist_le_one x z
      _ ≤ 1 + cappedEDist y z := le_add_right le_rfl
      _ = _ := by simp only [cappedEDist, min_eq_left hxy']

/-- Uniform time and state error for one increasing time change. -/
def discrepancy {T : ℝ≥0} {E : Type*} [PseudoEMetricSpace E]
    (x y : Time T → E) (e : TimeChange T) : ℝ≥0∞ :=
  ⨆ t, max (cappedEDist ((e t : Time T) : ℝ) (t : ℝ)) (cappedEDist (x (e t)) (y t))

theorem discrepancy_le_one {T : ℝ≥0} {E : Type*} [PseudoEMetricSpace E]
    (x y : Time T → E) (e : TimeChange T) : discrepancy x y e ≤ 1 := by
  apply iSup_le
  intro t
  exact max_le (cappedEDist_le_one _ _) (cappedEDist_le_one _ _)

theorem timeError_le_discrepancy {T : ℝ≥0} {E : Type*} [PseudoEMetricSpace E]
    (x y : Time T → E) (e : TimeChange T) (t : Time T) :
    cappedEDist ((e t : Time T) : ℝ) (t : ℝ) ≤ discrepancy x y e := by
  unfold discrepancy
  exact le_iSup_of_le t (le_max_left _ _)

theorem stateError_le_discrepancy {T : ℝ≥0} {E : Type*} [PseudoEMetricSpace E]
    (x y : Time T → E) (e : TimeChange T) (t : Time T) :
    cappedEDist (x (e t)) (y t) ≤ discrepancy x y e := by
  unfold discrepancy
  exact le_iSup_of_le t (le_max_right _ _)

theorem discrepancy_symm {T : ℝ≥0} {E : Type*} [PseudoEMetricSpace E]
    (x y : Time T → E) (e : TimeChange T) : discrepancy y x e.symm = discrepancy x y e := by
  suffices h : ∀ (x y : Time T → E) (e : TimeChange T),
      discrepancy y x e.symm ≤ discrepancy x y e from
    le_antisymm (h x y e) (by simpa using h y x e.symm)
  intro x y e
  apply iSup_le
  intro t
  have h := le_iSup (fun s : Time T =>
    max (cappedEDist ((e s : Time T) : ℝ) (s : ℝ)) (cappedEDist (x (e s)) (y s))) (e.symm t)
  simpa only [discrepancy, OrderIso.apply_symm_apply, cappedEDist_comm] using h

theorem discrepancy_comp {T : ℝ≥0} {E : Type*} [PseudoEMetricSpace E]
    (x y z : Time T → E) (e f : TimeChange T) :
    discrepancy x z (f.trans e) ≤ discrepancy x y e + discrepancy y z f := by
  apply iSup_le
  intro t
  apply max_le
  · apply (cappedEDist_triangle ((e (f t) : Time T) : ℝ) (f t : ℝ) (t : ℝ)).trans
    exact add_le_add (timeError_le_discrepancy x y e (f t)) (timeError_le_discrepancy y z f t)
  · apply (cappedEDist_triangle (x (e (f t))) (y (f t)) (z t)).trans
    exact add_le_add (stateError_le_discrepancy x y e (f t)) (stateError_le_discrepancy y z f t)

/-- Optimized extended distance, before constructing the path metric instance. -/
def j1EDist {T : ℝ≥0} {E : Type*} [PseudoEMetricSpace E] (x y : Time T → E) : ℝ≥0∞ :=
  ⨅ e : TimeChange T, discrepancy x y e

theorem j1EDist_le_discrepancy {T : ℝ≥0} {E : Type*} [PseudoEMetricSpace E]
    (x y : Time T → E) (e : TimeChange T) : j1EDist x y ≤ discrepancy x y e := iInf_le _ e

theorem j1EDist_le_one {T : ℝ≥0} {E : Type*} [PseudoEMetricSpace E]
    (x y : Time T → E) : j1EDist x y ≤ 1 :=
  (j1EDist_le_discrepancy x y (OrderIso.refl _)).trans (discrepancy_le_one _ _ _)

@[simp] theorem j1EDist_self {T : ℝ≥0} {E : Type*} [PseudoEMetricSpace E]
    (x : Time T → E) : j1EDist x x = 0 := by
  apply le_antisymm _ (zero_le _)
  exact (j1EDist_le_discrepancy x x (OrderIso.refl _)).trans (by simp [discrepancy])

theorem j1EDist_comm {T : ℝ≥0} {E : Type*} [PseudoEMetricSpace E]
    (x y : Time T → E) : j1EDist x y = j1EDist y x := by
  suffices h : ∀ (x y : Time T → E), j1EDist y x ≤ j1EDist x y from
    le_antisymm (h y x) (h x y)
  intro x y
  apply le_iInf
  intro e
  exact (j1EDist_le_discrepancy y x e.symm).trans_eq (discrepancy_symm x y e)

theorem j1EDist_triangle {T : ℝ≥0} {E : Type*} [PseudoEMetricSpace E]
    (x y z : Time T → E) : j1EDist x z ≤ j1EDist x y + j1EDist y z := by
  unfold j1EDist
  rw [ENNReal.iInf_add]
  apply le_iInf
  intro e
  rw [ENNReal.add_iInf]
  apply le_iInf
  intro f
  exact (iInf_le _ (f.trans e)).trans (discrepancy_comp x y z e f)

/-- Identity time change proves uniform domination. -/
theorem j1EDist_le_uniform {T : ℝ≥0} {E : Type*} [PseudoEMetricSpace E]
    (x y : Time T → E) : j1EDist x y ≤ ⨆ t, cappedEDist (x t) (y t) := by
  exact (j1EDist_le_discrepancy x y (OrderIso.refl _)).trans (by simp [discrepancy])

theorem timeChange_top {T : ℝ≥0} (e : TimeChange T) :
    e ⟨T, T.coe_nonneg, le_rfl⟩ = ⟨T, T.coe_nonneg, le_rfl⟩ := by
  apply le_antisymm
  · exact (e _).property.2
  · have h : e.symm ⟨T, T.coe_nonneg, le_rfl⟩ ≤ ⟨T, T.coe_nonneg, le_rfl⟩ :=
      (e.symm _).property.2
    simpa using e.monotone h

theorem cappedEDist_eq_zero_iff {E : Type*} [EMetricSpace E] (x y : E) :
    cappedEDist x y = 0 ↔ x = y := by
  constructor
  · intro h
    apply edist_eq_zero.mp
    by_contra hd
    have hp : 0 < min 1 (edist x y) := lt_min zero_lt_one (pos_iff_ne_zero.mpr hd)
    exact (ne_of_gt hp) h
  · intro h
    subst y
    exact cappedEDist_self x

theorem dist_lt_of_cappedEDist_lt {E : Type*} [PseudoMetricSpace E]
    {x y : E} {ε : ℝ} (hε : ε ≤ 1) (h : cappedEDist x y < ENNReal.ofReal ε) :
    dist x y < ε := by
  have h' : edist x y < ENNReal.ofReal ε := by
    rcases min_lt_iff.mp h with h | h
    · exact False.elim ((not_lt_of_ge (by simpa using ENNReal.ofReal_le_ofReal hε)) h)
    · exact h
  exact edist_lt_ofReal.mp h'

/-- A sufficiently small optimized error supplies a genuine increasing
homeomorphism with small errors in the original, uncapped state metric. -/
theorem exists_timeChange_of_j1EDist_lt {T : ℝ≥0} {E : Type*} [PseudoMetricSpace E]
    (x y : Time T → E) {ε : ℝ} (hε : ε ≤ 1)
    (h : j1EDist x y < ENNReal.ofReal ε) :
    ∃ e : TimeChange T,
      (∀ t, dist ((e t : Time T) : ℝ) (t : ℝ) < ε) ∧
      (∀ t, dist (x (e t)) (y t) < ε) := by
  obtain ⟨e, he⟩ := iInf_lt_iff.mp h
  refine ⟨e, ?_, ?_⟩
  · intro t
    exact dist_lt_of_cappedEDist_lt hε ((timeError_le_discrepancy x y e t).trans_lt he)
  · intro t
    exact dist_lt_of_cappedEDist_lt hε ((stateError_le_discrepancy x y e t).trans_lt he)

/-- Zero time-change distance forces pointwise equality of right-continuous
paths. The right endpoint is fixed by every time change. -/
theorem eq_of_j1EDist_eq_zero {T : ℝ≥0} {E : Type*} [MetricSpace E]
    (x y : Time T → E)
    (hx : ∀ t, ContinuousWithinAt x (Ici t) t)
    (hy : ∀ t, ContinuousWithinAt y (Ici t) t)
    (hzero : j1EDist x y = 0) : x = y := by
  funext t
  by_cases htop : (t : ℝ) = T
  · have ht : t = ⟨T, T.coe_nonneg, le_rfl⟩ := Subtype.ext htop
    subst t
    have hb : cappedEDist (x ⟨T, T.coe_nonneg, le_rfl⟩) (y ⟨T, T.coe_nonneg, le_rfl⟩) ≤
        j1EDist x y := by
      apply le_iInf
      intro e
      simpa only [timeChange_top] using
        stateError_le_discrepancy x y e ⟨T, T.coe_nonneg, le_rfl⟩
    rw [hzero] at hb
    exact (cappedEDist_eq_zero_iff _ _).mp (le_antisymm hb (zero_le _))
  · by_contra hne
    have hd : 0 < dist (x t) (y t) := dist_pos.mpr hne
    let ε : ℝ := min (dist (x t) (y t) / 4) (1 / 4)
    have hε : 0 < ε := lt_min (by linarith) (by norm_num)
    have hεd : ε ≤ dist (x t) (y t) / 4 := min_le_left _ _
    have hε1 : ε ≤ 1 / 4 := min_le_right _ _
    obtain ⟨δx, hδx, hxδ⟩ := Metric.continuousWithinAt_iff.mp (hx t) ε hε
    obtain ⟨δy, hδy, hyδ⟩ := Metric.continuousWithinAt_iff.mp (hy t) ε hε
    have htT : (t : ℝ) < T := lt_of_le_of_ne t.property.2 htop
    let r : ℝ := min (min δx δy) ((T : ℝ) - t) / 4
    have hr : 0 < r := div_pos (lt_min (lt_min hδx hδy) (sub_pos.mpr htT)) (by norm_num)
    have hrx : 4 * r ≤ δx := by
      have h := (min_le_left (min δx δy) ((T : ℝ) - t)).trans (min_le_left δx δy)
      dsimp only [r]
      linarith
    have hry : 4 * r ≤ δy := by
      have h := (min_le_left (min δx δy) ((T : ℝ) - t)).trans (min_le_right δx δy)
      dsimp only [r]
      linarith
    have hrT : 4 * r ≤ (T : ℝ) - t := by
      have h := min_le_right (min δx δy) ((T : ℝ) - t)
      dsimp only [r]
      linarith
    let s : Time T := ⟨(t : ℝ) + r, ⟨by linarith [t.property.1], by linarith⟩⟩
    have hsmall : min r ε ≤ 1 := (min_le_right r ε).trans (by linarith)
    have hzero' : j1EDist x y < ENNReal.ofReal (min r ε) := by
      rw [hzero]
      exact ENNReal.ofReal_pos.mpr (lt_min hr hε)
    obtain ⟨e, het, hey⟩ := exists_timeChange_of_j1EDist_lt x y hsmall hzero'
    have hes := het s
    rw [Real.dist_eq] at hes
    have hess : |((e s : Time T) : ℝ) - ((t : ℝ) + r)| < r :=
      hes.trans_le (min_le_left r ε)
    have hest : t ≤ e s := by
      change (t : ℝ) ≤ (e s : Time T)
      have h := (abs_lt.mp hess).1
      linarith
    have hxdist : dist (e s) t < δx := by
      rw [Subtype.dist_eq, Real.dist_eq]
      rw [abs_of_nonneg (show (0 : ℝ) ≤ ((e s : Time T) : ℝ) - (t : ℝ) from sub_nonneg.mpr hest)]
      have h := (abs_lt.mp hess).2
      linarith
    have hsdist : dist s t < δy := by
      rw [Subtype.dist_eq, Real.dist_eq]
      dsimp only [s]
      rw [add_sub_cancel_left, abs_of_pos hr]
      linarith
    have hxs : dist (x (e s)) (x t) < ε := hxδ hest hxdist
    have hys : dist (y s) (y t) < ε := hyδ (show t ≤ s by change (t : ℝ) ≤ (t : ℝ) + r; linarith) hsdist
    have hxy : dist (x (e s)) (y s) < ε := (hey s).trans_le (min_le_right r ε)
    have htri := (dist_triangle (x t) (x (e s)) (y t)).trans
      (add_le_add_left (dist_triangle (x (e s)) (y s) (y t)) _)
    rw [dist_comm (x t) (x (e s))] at htri
    linarith

instance pathEMetricSpace {T : ℝ≥0} {E : Type*} [MetricSpace E] : EMetricSpace (Path T E) where
  edist x y := j1EDist x y
  edist_self x := j1EDist_self x
  edist_comm x y := j1EDist_comm x y
  edist_triangle x y z := j1EDist_triangle x y z
  eq_of_edist_eq_zero {x y} h := Path.ext (congrFun
    (eq_of_j1EDist_eq_zero x y x.right_continuous y.right_continuous h))

/-- The finite J1 metric induces the time-change topology on actual càdlàg
functions, with no quotient or supplied metric axioms. -/
instance pathMetricSpace {T : ℝ≥0} {E : Type*} [MetricSpace E] : MetricSpace (Path T E) :=
  EMetricSpace.toMetricSpace (fun x y =>
    ne_top_of_le_ne_top (by norm_num) (j1EDist_le_one x y))

/-- The path sigma algebra is the Borel sigma algebra of the proved J1
metric. This definition does not assert measurability of random path maps. -/
instance pathMeasurableSpace {T : ℝ≥0} {E : Type*} [MetricSpace E] :
    MeasurableSpace (Path T E) := borel (Path T E)

instance pathBorelSpace {T : ℝ≥0} {E : Type*} [MetricSpace E] :
    BorelSpace (Path T E) := ⟨rfl⟩

theorem edist_path_eq {T : ℝ≥0} {E : Type*} [MetricSpace E] (x y : Path T E) :
    edist x y = j1EDist x y := rfl

theorem dist_path_eq {T : ℝ≥0} {E : Type*} [MetricSpace E] (x y : Path T E) :
    dist x y = (j1EDist x y).toReal := rfl



/-- A uniform bound in the original metric controls J1 directly. -/
theorem j1EDist_le_of_timeChange_bounds {T : ℝ≥0} {E : Type*} [PseudoMetricSpace E]
    (x y : Time T → E) (e : TimeChange T) (ε : ℝ)
    (htime : ∀ t, dist ((e t : Time T) : ℝ) (t : ℝ) ≤ ε)
    (hstate : ∀ t, dist (x (e t)) (y t) ≤ ε) :
    j1EDist x y ≤ ENNReal.ofReal ε := by
  apply (j1EDist_le_discrepancy x y e).trans
  apply iSup_le
  intro t
  apply max_le
  · exact (min_le_right _ _).trans (by
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (htime t))
  · exact (min_le_right _ _).trans (by
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hstate t))

theorem dist_le_of_timeChange_bounds {T : ℝ≥0} {E : Type*} [MetricSpace E]
    (x y : Path T E) (e : TimeChange T) (ε : ℝ) (hε : 0 ≤ ε)
    (htime : ∀ t, dist ((e t : Time T) : ℝ) (t : ℝ) ≤ ε)
    (hstate : ∀ t, dist (x (e t)) (y t) ≤ ε) : dist x y ≤ ε :=
  (edist_le_ofReal hε).mp (j1EDist_le_of_timeChange_bounds x y e ε htime hstate)

/-- Exact J1 convergence criterion in the original uncapped state metric.
This proves that capping the metric at one changes no induced J1 topology. -/
theorem tendsto_iff_timeChanges {T : ℝ≥0} {E : Type*} [MetricSpace E]
    {ι : Type*} (l : Filter ι) (X : ι → Path T E) (x : Path T E) :
    Tendsto X l (𝓝 x) ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∃ e : TimeChange T,
      (∀ t, dist ((e t : Time T) : ℝ) (t : ℝ) < ε) ∧
      (∀ t, dist (X i (e t)) (x t) < ε) := by
  constructor
  · intro h ε hε
    let δ : ℝ := min ε (1 / 2)
    have hδ : 0 < δ := lt_min hε (by norm_num)
    have hδ1 : δ ≤ 1 := (min_le_right ε (1/2)).trans (by norm_num)
    filter_upwards [Metric.tendsto_nhds.mp h δ hδ] with i hi
    have hj : j1EDist (X i) x < ENNReal.ofReal δ := edist_lt_ofReal.mpr hi
    obtain ⟨e, he, hx⟩ := exists_timeChange_of_j1EDist_lt (X i) x hδ1 hj
    exact ⟨e, fun t => (he t).trans_le (min_le_left _ _),
      fun t => (hx t).trans_le (min_le_left _ _)⟩
  · intro h
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [h (ε/2) (by linarith)] with i hi
    obtain ⟨e, he, hx⟩ := hi
    exact (dist_le_of_timeChange_bounds (X i) x e (ε/2) (by linarith)
      (fun t => (he t).le) (fun t => (hx t).le)).trans_lt (by linarith)

/-- Actual uniform convergence implies convergence in the constructed J1
metric, with no finite-step restriction on either path or the limit. -/
theorem tendsto_of_uniform {T : ℝ≥0} {E : Type*} [MetricSpace E]
    {ι : Type*} (l : Filter ι) (X : ι → Path T E) (x : Path T E)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ t, dist (X i t) (x t) < ε) :
    Tendsto X l (𝓝 x) := by
  apply (tendsto_iff_timeChanges l X x).mpr
  intro ε hε
  filter_upwards [h ε hε] with i hi
  exact ⟨OrderIso.refl _, fun _ => by simpa using hε, hi⟩

/-- Every continuous path is a path in this genuine J1 space, in particular
the continuous moment-law curve appearing as the empirical-process limit. -/
def Path.ofContinuous {T : ℝ≥0} {E : Type*} [TopologicalSpace E]
    (f : Time T → E) (hf : Continuous f) : Path T E where
  toFun := f
  right_continuous _ := hf.continuousAt.continuousWithinAt
  left_limits t := ⟨f t, hf.continuousAt.mono_left nhdsWithin_le_nhds⟩

@[simp] theorem Path.ofContinuous_apply {T : ℝ≥0} {E : Type*} [TopologicalSpace E]
    (f : Time T → E) (hf : Continuous f) (t : Time T) :
    Path.ofContinuous f hf t = f t := rfl

/-- The metric distance is dominated by any genuine pointwise uniform bound. -/
theorem dist_le_uniform_bound {T : ℝ≥0} {E : Type*} [MetricSpace E]
    (x y : Path T E) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ t, dist (x t) (y t) ≤ ε) : dist x y ≤ ε :=
  dist_le_of_timeChange_bounds x y (OrderIso.refl _) ε hε (by simpa using fun _ : Time T => hε) h


/-- Direct domination by the original all-time extended uniform distance,
usable for the actual empirical-process probability estimate. -/
theorem edist_le_uniform_edist {T : ℝ≥0} {E : Type*} [MetricSpace E]
    (x y : Path T E) : edist x y ≤ ⨆ t : Time T, edist (x t) (y t) := by
  apply (j1EDist_le_uniform x y).trans
  exact iSup_mono (fun _ => min_le_right _ _)

end CarryingCapacity.SkorokhodJ1
