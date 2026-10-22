import CarryingCapacity.SkorokhodJ1

/-!
# Actual restrictions and state maps in the Skorokhod path space

Restriction retains every value on the closed interval, including the terminal
value. A fixed constant fallback makes the random-path construction total on
exceptional samples. No measurability of that construction is assumed here.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Classical Topology NNReal ENNReal

namespace CarryingCapacity.SkorokhodJ1

variable {T : ℝ≥0} {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

def IsCadlag (x : Time T → E) : Prop :=
  (∀ t, ContinuousWithinAt x (Ici t) t) ∧
    ∀ t, ∃ a, Tendsto x (𝓝[<] t) (𝓝 a)

theorem Path.isCadlag (x : Path T E) : IsCadlag x :=
  ⟨x.right_continuous, x.left_limits⟩

def Path.const (T : ℝ≥0) (e : E) : Path T E :=
  Path.ofContinuous (fun _ => e) continuous_const

@[simp] theorem Path.const_apply (e : E) (t : Time T) : Path.const T e t = e := rfl

/-- An actual path whenever the function is càdlàg, with a fixed constant
value on the exceptional functions. This definition alone asserts no Borel
measurability. -/
def pathOrConst (T : ℝ≥0) (e : E) (x : Time T → E) : Path T E :=
  if h : IsCadlag x then ⟨x, h.1, h.2⟩ else Path.const T e

theorem pathOrConst_apply (e : E) (x : Time T → E) (hx : IsCadlag x) (t : Time T) :
    pathOrConst T e x t = x t := by
  simp only [pathOrConst, dif_pos hx]

/-- Restriction of a genuine càdlàg real-time path preserves both one-sided
conditions, including the zero and terminal endpoints. -/
theorem isCadlag_restrict (x : ℝ → E)
    (hr : ∀ t, 0 ≤ t → ContinuousWithinAt x (Ici t) t)
    (hl : ∀ t, 0 < t → ∃ a, Tendsto x (𝓝[<] t) (𝓝 a)) :
    IsCadlag (fun t : Time T => x t) := by
  constructor
  · intro t
    exact (hr t t.property.1).comp continuous_subtype_val.continuousWithinAt
      (fun _ hs => hs)
  · intro t
    by_cases ht : 0 < (t : ℝ)
    · obtain ⟨a, ha⟩ := hl t ht
      refine ⟨a, ha.comp ?_⟩
      exact continuous_subtype_val.continuousWithinAt.tendsto_nhdsWithin
        (fun _ hs => hs)
    · refine ⟨x t, ?_⟩
      have he : Iio t = (∅ : Set (Time T)) := by
        apply Set.eq_empty_iff_forall_not_mem.mpr
        intro s hs
        exact (not_lt_of_ge s.property.1) (lt_of_lt_of_le hs (le_of_not_gt ht))
      simp only [he, nhdsWithin_empty]
      exact tendsto_bot

def realPathOrConst (T : ℝ≥0) (e : E) (x : ℝ → E) : Path T E :=
  pathOrConst T e (fun t => x t)

theorem realPathOrConst_apply (e : E) (x : ℝ → E)
    (hr : ∀ t, 0 ≤ t → ContinuousWithinAt x (Ici t) t)
    (hl : ∀ t, 0 < t → ∃ a, Tendsto x (𝓝[<] t) (𝓝 a)) (t : Time T) :
    realPathOrConst T e x t = x t :=
  pathOrConst_apply e _ (isCadlag_restrict x hr hl) t

theorem realPathOrConst_congr (e : E) (x y : ℝ → E)
    (h : EqOn x y (Icc 0 (T : ℝ))) :
    realPathOrConst T e x = realPathOrConst T e y := by
  apply congrArg (pathOrConst T e)
  funext t
  exact h t.property

/-- A continuous state map acts on the actual path values. -/
def Path.map (f : E → F) (hf : Continuous f) (x : Path T E) : Path T F where
  toFun t := f (x t)
  right_continuous t := hf.continuousAt.comp_continuousWithinAt (x.right_continuous t)
  left_limits t := by
    obtain ⟨a, ha⟩ := x.left_limits t
    exact ⟨f a, hf.continuousAt.tendsto.comp ha⟩

@[simp] theorem Path.map_apply (f : E → F) (hf : Continuous f) (x : Path T E)
    (t : Time T) : x.map f hf t = f (x t) := rfl

theorem ae_realPathOrConst_apply {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (e : E) (X : Ω → ℝ → E)
    (hX : ∀ᵐ ω ∂μ,
      (∀ t, 0 ≤ t → ContinuousWithinAt (X ω) (Ici t) t) ∧
      (∀ t, 0 < t → ∃ a, Tendsto (X ω) (𝓝[<] t) (𝓝 a))) :
    ∀ᵐ ω ∂μ, ∀ t : Time T, realPathOrConst T e (X ω) t = X ω t := by
  filter_upwards [hX] with ω hω
  exact realPathOrConst_apply e (X ω) hω.1 hω.2

end CarryingCapacity.SkorokhodJ1

namespace CarryingCapacity.SkorokhodJ1

variable {T : ℝ≥0} {E F : Type*} [MetricSpace E] [MetricSpace F]

/-- A uniformly continuous state transformation preserves genuine J1
convergence using the same increasing time changes. -/
theorem continuous_path_map (f : E → F) (hf : UniformContinuous f) :
    Continuous (fun x : Path T E => x.map f hf.continuous) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (tendsto_iff_timeChanges (𝓝 x) _ _).mpr
  intro ε hε
  obtain ⟨δ, hδ, hfd⟩ := Metric.uniformContinuous_iff.mp hf ε hε
  have hx := (tendsto_iff_timeChanges (𝓝 x) id x).mp tendsto_id
    (min ε δ) (lt_min hε hδ)
  filter_upwards [hx] with y hy
  obtain ⟨e, ht, hs⟩ := hy
  refine ⟨e, fun t => (ht t).trans_le (min_le_left _ _), ?_⟩
  intro t
  exact hfd ((hs t).trans_le (min_le_right _ _))

theorem measurable_path_map (f : E → F) (hf : UniformContinuous f) :
    Measurable (fun x : Path T E => x.map f hf.continuous) :=
  (continuous_path_map f hf).measurable

end CarryingCapacity.SkorokhodJ1
