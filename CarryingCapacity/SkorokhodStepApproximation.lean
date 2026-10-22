import CarryingCapacity.SkorokhodJ1
import CarryingCapacity.FiniteTimeChange
import CarryingCapacity.SkorokhodPathOperations

/-!
# Deterministic grid-step paths

Finite threshold steps are genuine càdlàg paths. A regular grid includes its
terminal sample explicitly, so a jump at the terminal time is retained. The
map from its finite sample vector to the J1 path is Lipschitz, hence measurable.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical Topology ENNReal NNReal

namespace CarryingCapacity.SkorokhodStepApproximation
open SkorokhodJ1

/-- Number of thresholds already reached, including a threshold at this time. -/
def index {m : ℕ} (a : Fin m → ℝ) (t : ℝ) : Fin (m + 1) :=
  ⟨(Finset.univ.filter (fun i => a i ≤ t)).card,
    lt_of_le_of_lt ((Finset.card_filter_le _ _).trans_eq (Finset.card_univ.trans (Fintype.card_fin m)))
      (Nat.lt_succ_self m)⟩

/-- The value approached strictly from the left uses only earlier thresholds. -/
def leftIndex {m : ℕ} (a : Fin m → ℝ) (t : ℝ) : Fin (m + 1) :=
  ⟨(Finset.univ.filter (fun i => a i < t)).card,
    lt_of_le_of_lt ((Finset.card_filter_le _ _).trans_eq (Finset.card_univ.trans (Fintype.card_fin m)))
      (Nat.lt_succ_self m)⟩

theorem index_right_eventually {T : ℝ≥0} {m : ℕ} (a : Fin m → ℝ) (t : Time T) :
    ∀ᶠ s : Time T in 𝓝[≥] t, index a s = index a t := by
  have he : ∀ᶠ s : Time T in 𝓝[≥] t, ∀ i, a i ≤ (s : ℝ) ↔ a i ≤ (t : ℝ) := by
    apply eventually_all.mpr
    intro i
    by_cases hi : a i ≤ (t : ℝ)
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact iff_of_true (hi.trans hs) hi
    · have ht : (t : ℝ) < a i := lt_of_not_ge hi
      have hh := (continuous_subtype_val.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Ici t)))
        (Iio_mem_nhds ht)
      filter_upwards [hh] with s hs
      exact iff_of_false (not_le_of_gt hs) hi
  filter_upwards [he] with s hs
  apply Fin.ext
  dsimp only [index, leftIndex]
  congr 1
  exact Finset.filter_congr (fun i _ => hs i)

theorem index_left_eventually {T : ℝ≥0} {m : ℕ} (a : Fin m → ℝ) (t : Time T) :
    ∀ᶠ s : Time T in 𝓝[<] t, index a s = leftIndex a t := by
  have he : ∀ᶠ s : Time T in 𝓝[<] t, ∀ i, a i ≤ (s : ℝ) ↔ a i < (t : ℝ) := by
    apply eventually_all.mpr
    intro i
    by_cases hi : a i < (t : ℝ)
    · have hh := (continuous_subtype_val.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio t)))
        (Ioi_mem_nhds hi)
      filter_upwards [hh] with s hs
      exact iff_of_true hs.le hi
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact iff_of_false (not_le_of_gt (hs.trans_le (le_of_not_gt hi))) hi
  filter_upwards [he] with s hs
  apply Fin.ext
  dsimp only [index, leftIndex]
  congr 1
  exact Finset.filter_congr (fun i _ => hs i)

/-- Threshold-step interpolation with an arbitrary finite value vector. -/
def thresholdPath {T : ℝ≥0} {E : Type*} [TopologicalSpace E] {m : ℕ}
    (a : Fin m → ℝ) (values : Fin (m + 1) → E) : Path T E where
  toFun t := values (index a t)
  right_continuous t := by
    apply tendsto_const_nhds.congr'
    filter_upwards [index_right_eventually a t] with s hs
    exact congrArg values hs.symm
  left_limits t := by
    refine ⟨values (leftIndex a t), tendsto_const_nhds.congr' ?_⟩
    filter_upwards [index_left_eventually a t] with s hs
    exact congrArg values hs.symm

@[simp] theorem thresholdPath_apply {T : ℝ≥0} {E : Type*} [TopologicalSpace E] {m : ℕ}
    (a : Fin m → ℝ) (values : Fin (m + 1) → E) (t : Time T) :
    thresholdPath a values t = values (index a t) := rfl

/-- The genuine J1 path distance is bounded by the finite sample-vector distance. -/
theorem lipschitz_thresholdPath {T : ℝ≥0} {E : Type*} [MetricSpace E] {m : ℕ}
    (a : Fin m → ℝ) : LipschitzWith 1 (thresholdPath (T := T) (E := E) a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  exact dist_le_uniform_bound _ _ (dist x y) dist_nonneg
    (fun t => dist_le_pi_dist x y (index a t))

theorem measurable_thresholdPath {T : ℝ≥0} {E : Type*} [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {m : ℕ}
    (a : Fin m → ℝ) : Measurable (thresholdPath (T := T) (E := E) a) :=
  (lipschitz_thresholdPath a).continuous.measurable

/-- Regular grid with n+1 cells and both endpoint samples. -/
def gridPoint (T : ℝ≥0) (n : ℕ) (i : Fin (n + 2)) : Time T :=
  ⟨(T : ℝ) * i / (n + 1 : ℕ), by
    have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hi : (i : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    constructor
    · positivity
    · apply (div_le_iff₀ hn).mpr
      exact mul_le_mul_of_nonneg_left hi T.coe_nonneg⟩

/-- The positive grid thresholds include T, ensuring its value is preserved. -/
def gridThreshold (T : ℝ≥0) (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  gridPoint T n i.succ

/-- The step path built solely from the finite regular-grid sample vector. -/
def gridPath {E : Type*} [TopologicalSpace E] (T : ℝ≥0) (n : ℕ)
    (values : Fin (n + 2) → E) : Path T E := thresholdPath (gridThreshold T n) values

/-- The deterministic grid approximation of an arbitrary actual path. -/
def approximation {E : Type*} [TopologicalSpace E] {T : ℝ≥0}
    (x : Time T → E) (n : ℕ) : Path T E := gridPath T n (fun i => x (gridPoint T n i))

theorem measurable_gridPath {E : Type*} [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] (T : ℝ≥0) (n : ℕ) :
    Measurable (gridPath (E := E) T n) := measurable_thresholdPath _

/-- Evaluating finitely many measurable coordinates gives a measurable J1 path. -/
theorem measurable_approximation {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {T : ℝ≥0}
    (X : Ω → Time T → E) (hX : ∀ t, Measurable (fun ω => X ω t)) (n : ℕ) :
    Measurable (fun ω => approximation (X ω) n) :=
  (measurable_gridPath T n).comp (measurable_pi_lambda _ (fun i => hX (gridPoint T n i)))

@[simp] theorem gridPoint_last (T : ℝ≥0) (n : ℕ) :
    gridPoint T n (Fin.last (n + 1)) = ⟨T, T.coe_nonneg, le_rfl⟩ := by
  apply Subtype.ext
  change (T : ℝ) * (n + 1 : ℕ) / (n + 1 : ℕ) = _
  exact mul_div_cancel_right₀ _ (by positivity)

/-- In particular the terminal value is retained exactly, including terminal jumps. -/
theorem approximation_terminal {T : ℝ≥0} {E : Type*} [TopologicalSpace E]
    (x : Time T → E) (n : ℕ) :
    approximation x n ⟨T, T.coe_nonneg, le_rfl⟩ = x ⟨T, T.coe_nonneg, le_rfl⟩ := by
  have hi : index (gridThreshold T n) T = Fin.last (n + 1) := by
    apply Fin.ext
    change (Finset.univ.filter (fun i => gridThreshold T n i ≤ T)).card = n + 1
    have hf : (Finset.univ.filter (fun i => gridThreshold T n i ≤ T)) = Finset.univ := by
      apply Finset.filter_true_of_mem
      intro i _
      exact (gridPoint T n i.succ).property.2
    rw [hf]
    simp
  change x (gridPoint T n (index (gridThreshold T n) T)) = _
  rw [hi, gridPoint_last]


/-- Ordered thresholds identify the prefix length without rounding conventions. -/
theorem index_le_iff {m : ℕ} (a : Fin m → ℝ) (ha : StrictMono a)
    (t : ℝ) (j : Fin m) : (index a t).val ≤ j.val ↔ t < a j := by
  constructor
  · intro h
    by_contra hn
    have hs : Finset.Iic j ⊆ Finset.univ.filter (fun i => a i ≤ t) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (ha.monotone (Finset.mem_Iic.mp hi)).trans (le_of_not_gt hn)⟩
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iic] at hc
    change j.val + 1 ≤ (index a t).val at hc
    omega
  · intro h
    have hs : Finset.univ.filter (fun i => a i ≤ t) ⊆ Finset.Iio j := by
      intro i hi
      exact Finset.mem_Iio.mpr ((ha.lt_iff_lt).mp ((Finset.mem_filter.mp hi).2.trans_lt h))
    have hc := Finset.card_le_card hs
    simpa only [Fin.card_Iio] using hc

theorem threshold_le_iff_lt_index {m : ℕ} (a : Fin m → ℝ) (ha : StrictMono a)
    (t : ℝ) (j : Fin m) : a j ≤ t ↔ j.val < (index a t).val := by
  rw [← not_lt, ← index_le_iff a ha, not_le]

theorem gridPoint_strictMono {T : ℝ≥0} (hT : 0 < (T : ℝ)) (n : ℕ) :
    StrictMono (gridPoint T n) := by
  intro i j hij
  change (T : ℝ) * (i : ℝ) / (n + 1 : ℕ) < (T : ℝ) * (j : ℝ) / (n + 1 : ℕ)
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left (by exact_mod_cast hij) hT) (by positivity)

theorem gridThreshold_strictMono {T : ℝ≥0} (hT : 0 < (T : ℝ)) (n : ℕ) :
    StrictMono (gridThreshold T n) := by
  intro i j hij
  exact gridPoint_strictMono hT n (Fin.succ_lt_succ_iff.mpr hij)

/-- The selected sample is the last grid point no later than the query time. -/
theorem gridPoint_le_iff {T : ℝ≥0} (hT : 0 < (T : ℝ)) (n : ℕ)
    (t : Time T) (k : Fin (n + 2)) :
    gridPoint T n k ≤ t ↔ k.val ≤ (index (gridThreshold T n) t).val := by
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [Fin.val_zero, Nat.zero_le, iff_true]
    simpa [gridPoint] using t.property.1
  · change gridThreshold T n j ≤ (t : ℝ) ↔ j.val + 1 ≤ _
    exact (threshold_le_iff_lt_index _ (gridThreshold_strictMono hT n) t j).trans
      (by omega)

/-- The time used by regular-grid interpolation. -/
def sampleTime (T : ℝ≥0) (n : ℕ) (t : Time T) : Time T :=
  gridPoint T n (index (gridThreshold T n) t)

theorem sampleTime_le {T : ℝ≥0} (hT : 0 < (T : ℝ)) (n : ℕ) (t : Time T) :
    sampleTime T n t ≤ t := (gridPoint_le_iff hT n t _).mpr le_rfl

@[simp] theorem approximation_apply {T : ℝ≥0} {E : Type*} [TopologicalSpace E]
    (x : Time T → E) (n : ℕ) (t : Time T) :
    approximation x n t = x (sampleTime T n t) := rfl

/-- Round a time upward to the nearest regular-grid point. -/
def roundUp (T : ℝ≥0) (n : ℕ) (r : ℝ) : ℝ :=
  (T : ℝ) * Nat.ceil ((n + 1 : ℕ) * r / T) / (n + 1 : ℕ)

def mesh (T : ℝ≥0) (n : ℕ) : ℝ := (T : ℝ) / (n + 1 : ℕ)

theorem roundUp_ge {T : ℝ≥0} (hT : 0 < (T : ℝ)) (n : ℕ) (r : ℝ) : r ≤ roundUp T n r := by
  have h := Nat.le_ceil ((n + 1 : ℕ) * r / (T : ℝ))
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  dsimp only [roundUp]
  apply (le_div_iff₀ hn).mpr
  have hh := (div_le_iff₀ hT).mp h
  nlinarith

theorem roundUp_lt_add_mesh {T : ℝ≥0} (hT : 0 < (T : ℝ)) (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    roundUp T n r < r + mesh T n := by
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (n + 1 : ℕ) * r / T by positivity)
  dsimp only [roundUp, mesh]
  apply (div_lt_iff₀ hn).mpr
  have hh := mul_lt_mul_of_pos_left h hT
  field_simp at hh ⊢
  nlinarith

@[simp] theorem roundUp_zero (T : ℝ≥0) (n : ℕ) : roundUp T n 0 = 0 := by simp [roundUp]

@[simp] theorem roundUp_terminal {T : ℝ≥0} (hT : 0 < (T : ℝ)) (n : ℕ) :
    roundUp T n T = T := by
  dsimp only [roundUp]
  rw [mul_div_cancel_right₀ _ hT.ne', Nat.ceil_natCast]
  exact mul_div_cancel_right₀ _ (by positivity)

/-- A rounded event has arrived exactly when the sampled time has passed the
original event. This is the deterministic event-history bridge. -/
theorem roundUp_le_iff_sampleTime {T : ℝ≥0} (hT : 0 < (T : ℝ)) (n : ℕ)
    (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) (t : Time T) :
    roundUp T n r ≤ (t : ℝ) ↔ r ≤ (sampleTime T n t : ℝ) := by
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hk : Nat.ceil ((n + 1 : ℕ) * r / (T : ℝ)) ≤ n + 1 := by
    rw [Nat.ceil_le]
    apply (div_le_iff₀ hT).mpr
    nlinarith [hr.2]
  let k : Fin (n + 2) := ⟨Nat.ceil ((n + 1 : ℕ) * r / (T : ℝ)), by omega⟩
  change gridPoint T n k ≤ t ↔ _
  rw [gridPoint_le_iff hT n t k]
  change Nat.ceil ((n + 1 : ℕ) * r / (T : ℝ)) ≤ _ ↔ _
  rw [Nat.ceil_le]
  dsimp only [sampleTime, gridPoint]
  rw [div_le_iff₀ hT, le_div_iff₀ hn]
  constructor <;> intro h <;> nlinarith

/-- The deterministic grid mesh vanishes with the number of cells. -/
theorem tendsto_mesh (T : ℝ≥0) : Tendsto (mesh T) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (T : ℝ) / (n + 1 : ℕ)) atTop (𝓝 0)
  simpa [mesh, div_eq_mul_inv] using
    (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (T : ℝ))


/-- Equal membership of every possible change time in the past determines
identical path values, directly from the actual no-event constancy property. -/
theorem eq_of_same_event_history {T : ℝ≥0} {E : Type*}
    (x : Time T → E) (F : Finset ℝ)
    (hconst : ∀ s t : Time T, s ≤ t → (∀ r ∈ F, r ∉ Ioc (s : ℝ) (t : ℝ)) → x s = x t)
    (s t : Time T) (he : ∀ r ∈ F, r ≤ (s : ℝ) ↔ r ≤ (t : ℝ)) : x s = x t := by
  rcases le_total s t with hst | hts
  · apply hconst s t hst
    intro r hr hmem
    exact (not_le_of_gt hmem.1) ((he r hr).mpr hmem.2)
  · symm
    apply hconst t s hts
    intro r hr hmem
    exact (not_le_of_gt hmem.1) ((he r hr).mp hmem.2)

/-- Eventually distinct event times and the two endpoints remain strictly
ordered after upward grid rounding. No separation bound is assumed. -/
theorem eventually_roundUp_strictMono {T : ℝ≥0} (hT : 0 < (T : ℝ))
    (S : Finset ℝ) (hS : ∀ s ∈ S, 0 ≤ s) :
    ∀ᶠ n in atTop, StrictMonoOn (roundUp T n) (S : Set ℝ) := by
  have hg : ∀ᶠ n in atTop, ∀ a ∈ S, ∀ b ∈ S, a < b → mesh T n < b - a := by
    apply S.eventually_all.mpr
    intro a ha
    apply S.eventually_all.mpr
    intro b hb
    by_cases hab : a < b
    · filter_upwards [(tendsto_mesh T).eventually (gt_mem_nhds (sub_pos.mpr hab))] with n hn
      exact fun _ => hn
    · exact Eventually.of_forall (fun _ h => False.elim (hab h))
  filter_upwards [hg] with n hn
  intro a ha b hb hab
  have h₁ := roundUp_lt_add_mesh hT n a (hS a ha)
  have h₂ := roundUp_ge hT n b
  have h₃ := hn a ha b hb hab
  linarith

/-- A finite-activity path has an exact grid-step match after a time change
whose time error is at most one grid mesh. The endpoint value is included. -/
theorem eventually_timeChange_exact {T : ℝ≥0} {E : Type*} [TopologicalSpace E]
    (hT : 0 < (T : ℝ)) (x : Time T → E) (F : Finset ℝ)
    (hF : ∀ r ∈ F, r ∈ Ioc 0 (T : ℝ))
    (hconst : ∀ s t : Time T, s ≤ t → (∀ r ∈ F, r ∉ Ioc (s : ℝ) (t : ℝ)) → x s = x t) :
    ∀ᶠ n in atTop, ∃ e : TimeChange T,
      (∀ t, |(e t : ℝ) - (t : ℝ)| ≤ mesh T n) ∧
      (∀ t, approximation x n (e t) = x t) := by
  let S : Finset ℝ := insert 0 (insert (T : ℝ) F)
  have hS (s : ℝ) (hs : s ∈ S) : s ∈ Icc 0 (T : ℝ) := by
    simp only [S, Finset.mem_insert] at hs
    rcases hs with rfl | rfl | hs
    · exact ⟨le_rfl, T.coe_nonneg⟩
    · exact ⟨T.coe_nonneg, le_rfl⟩
    · exact ⟨(hF s hs).1.le, (hF s hs).2⟩
  filter_upwards [eventually_roundUp_strictMono hT S (fun s hs => (hS s hs).1)] with n hn
  have hδ (s : ℝ) (hs : s ∈ S) : |roundUp T n s - s| ≤ mesh T n := by
    rw [abs_of_nonneg (sub_nonneg.mpr (roundUp_ge hT n s))]
    linarith [roundUp_lt_add_mesh hT n s (hS s hs).1]
  obtain ⟨e, he, hb⟩ := FiniteTimeChange.exists_timeChange_finset T S
    (by simp [S]) (by simp [S]) hS (roundUp T n) hn
    (roundUp_zero T n) (roundUp_terminal hT n) (mesh T n) hδ
  refine ⟨e, hb, ?_⟩
  intro t
  rw [approximation_apply]
  apply eq_of_same_event_history x F hconst
  intro r hr
  have hrS : r ∈ S := by simp [S, hr]
  let rr : Time T := ⟨r, hS r hrS⟩
  have her : (e rr : ℝ) = roundUp T n r := he r hrS
  rw [← roundUp_le_iff_sampleTime hT n r (hS r hrS) (e t), ← her]
  exact e.le_iff_le

/-- The deterministic regular-grid approximations converge in the genuine
J1 metric for every finite-activity path. No approximation premise is used. -/
theorem tendsto_approximation_of_finite_activity {T : ℝ≥0} {E : Type*} [MetricSpace E]
    (x : Path T E) (F : Finset ℝ) (hF : ∀ r ∈ F, r ∈ Ioc 0 (T : ℝ))
    (hconst : ∀ s t : Time T, s ≤ t → (∀ r ∈ F, r ∉ Ioc (s : ℝ) (t : ℝ)) → x s = x t) :
    Tendsto (approximation x) atTop (𝓝 x) := by
  by_cases hT : 0 < (T : ℝ)
  · apply (tendsto_iff_timeChanges atTop (approximation x) x).mpr
    intro ε hε
    filter_upwards [eventually_timeChange_exact hT x F hF hconst,
      (tendsto_mesh T).eventually (gt_mem_nhds hε)] with n hn hmesh
    obtain ⟨e, he, hx⟩ := hn
    refine ⟨e, ?_, ?_⟩
    · intro t
      rw [Real.dist_eq]
      exact (he t).trans_lt hmesh
    · intro t
      rw [hx t, dist_self]
      exact hε
  · have hzero : T = 0 := NNReal.coe_eq_zero.mp (le_antisymm (le_of_not_gt hT) T.coe_nonneg)
    subst T
    have he (n : ℕ) : approximation x n = x := by
      apply SkorokhodJ1.Path.ext
      intro t
      have ht : t = ⟨0, le_rfl, le_rfl⟩ := Subtype.ext (le_antisymm t.property.2 t.property.1)
      subst t
      exact approximation_terminal x n
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).congr'
      (Eventually.of_forall (fun n => (he n).symm))


/-- The actual finite-activity random path is Borel AE measurable in the
genuine J1 space. The fixed fallback is used only on exceptional non-càdlàg
samples. Measurability follows from the proved grid approximation, not from
assuming that coordinate-measurability generates the path-space Borel sets. -/
theorem aemeasurable_realPathOrConst {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) (T : ℝ≥0) (e : E) (X : Ω → ℝ → E)
    (hX : ∀ t, Measurable (fun ω => X ω t))
    (hcadlag : ∀ᵐ ω ∂μ,
      (∀ t, 0 ≤ t → ContinuousWithinAt (X ω) (Ici t) t) ∧
      (∀ t, 0 < t → ∃ a, Tendsto (X ω) (𝓝[<] t) (𝓝 a)))
    (hfinite : ∀ᵐ ω ∂μ, ∃ F : Finset ℝ, (∀ r ∈ F, r ∈ Ioc 0 (T : ℝ)) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        (∀ r ∈ F, r ∉ Ioc s t) → X ω s = X ω t) :
    AEMeasurable (fun ω => realPathOrConst T e (X ω)) μ := by
  apply aemeasurable_of_tendsto_metrizable_ae atTop
    (fun n => (measurable_approximation (fun (ω : Ω) (t : Time T) => X ω t)
      (fun t => hX t) n).aemeasurable)
  filter_upwards [hcadlag, hfinite] with ω hc hf
  obtain ⟨F, hF, hconst⟩ := hf
  have he : (fun t : Time T => X ω t) = (realPathOrConst T e (X ω) : Time T → E) := by
    funext t
    exact (realPathOrConst_apply e (X ω) hc.1 hc.2 t).symm
  rw [he]
  apply tendsto_approximation_of_finite_activity _ F hF
  intro s t hst hno
  rw [realPathOrConst_apply e (X ω) hc.1 hc.2 s,
    realPathOrConst_apply e (X ω) hc.1 hc.2 t]
  exact hconst s t s.property.1 hst t.property.2 hno

end CarryingCapacity.SkorokhodStepApproximation
