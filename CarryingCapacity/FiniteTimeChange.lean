import CarryingCapacity.SkorokhodJ1

/-!
# Finite knot alignment by genuine interval time changes

The graph below consists of the affine segments joining two strictly ordered
lists of knots. Including both endpoints makes this graph an increasing
homeomorphism of the entire time interval. Its displacement is bounded by the
largest displacement of a knot. No regularity or approximation of paths is
asserted here.
-/

noncomputable section
open Set
open scoped NNReal

namespace CarryingCapacity.FiniteTimeChange

def blend (a b θ : ℝ) : ℝ := (1 - θ) * a + θ * b

theorem blend_mem {a b θ : ℝ} (hab : a ≤ b) (hθ : θ ∈ Icc (0 : ℝ) 1) :
    blend a b θ ∈ Icc a b := by
  unfold blend
  constructor <;> nlinarith [mul_nonneg hθ.1 (sub_nonneg.mpr hab),
    mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hab)]

theorem blend_strictMono {a b : ℝ} (hab : a < b) : StrictMono (blend a b) := by
  intro x y hxy
  unfold blend
  nlinarith [mul_pos (sub_pos.mpr hab) (sub_pos.mpr hxy)]

@[simp] theorem blend_zero (a b : ℝ) : blend a b 0 = a := by simp [blend]
@[simp] theorem blend_one (a b : ℝ) : blend a b 1 = b := by simp [blend]

theorem exists_segment {n : ℕ} (a : Fin (n + 2) → ℝ) (x : ℝ)
    (hx : x ∈ Icc (a 0) (a (Fin.last (n + 1)))) :
    ∃ i : Fin (n + 1), x ∈ Icc (a i.castSucc) (a i.succ) := by
  induction n with
  | zero => exact ⟨0, hx⟩
  | succ n ih =>
    by_cases h : x ≤ a (Fin.succ 0)
    · exact ⟨0, hx.1, h⟩
    · obtain ⟨i, hi⟩ := ih (fun j => a j.succ) ⟨(lt_of_not_ge h).le, hx.2⟩
      exact ⟨i.succ, by simpa only [Fin.succ_castSucc] using hi⟩

/-- The actual piecewise-affine graph, allowing the two adjacent representations
of a knot. -/
def Graph {n : ℕ} (a b : Fin (n + 2) → ℝ) (x y : ℝ) : Prop :=
  ∃ i : Fin (n + 1), ∃ θ ∈ Icc (0 : ℝ) 1,
    x = blend (a i.castSucc) (a i.succ) θ ∧
    y = blend (b i.castSucc) (b i.succ) θ

theorem Graph.symm {n : ℕ} {a b : Fin (n + 2) → ℝ} {x y : ℝ}
    (h : Graph a b x y) : Graph b a y x := by
  obtain ⟨i, θ, hθ, hx, hy⟩ := h
  exact ⟨i, θ, hθ, hy, hx⟩

theorem graph_total {n : ℕ} (a b : Fin (n + 2) → ℝ) (ha : StrictMono a)
    (x : ℝ) (hx : x ∈ Icc (a 0) (a (Fin.last (n + 1)))) :
    ∃ y, Graph a b x y := by
  obtain ⟨i, hi⟩ := exists_segment a x hx
  have hgap : 0 < a i.succ - a i.castSucc := sub_pos.mpr (ha (by simp))
  let θ := (x - a i.castSucc) / (a i.succ - a i.castSucc)
  have hθ : θ ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hi.1) hgap.le
    · exact (div_le_one hgap).mpr (by linarith [hi.2])
  refine ⟨blend (b i.castSucc) (b i.succ) θ, i, θ, hθ, ?_, rfl⟩
  dsimp [θ, blend]
  field_simp
  ring

theorem graph_mem {n : ℕ} {a b : Fin (n + 2) → ℝ} (hb : StrictMono b)
    {x y : ℝ} (h : Graph a b x y) : y ∈ Icc (b 0) (b (Fin.last (n + 1))) := by
  obtain ⟨i, θ, hθ, hx, rfl⟩ := h
  have hm := blend_mem (hb (by simp : i.castSucc < i.succ)).le hθ
  exact ⟨(hb.monotone (Fin.zero_le _)).trans hm.1,
    hm.2.trans (hb.monotone (Fin.le_last _))⟩

theorem graph_strictMono {n : ℕ} {a b : Fin (n + 2) → ℝ}
    (ha : StrictMono a) (hb : StrictMono b) {x y x' y' : ℝ}
    (h : Graph a b x y) (h' : Graph a b x' y') (hxx : x < x') : y < y' := by
  obtain ⟨i, θ, hθ, rfl, rfl⟩ := h
  obtain ⟨j, φ, hφ, rfl, rfl⟩ := h'
  have hai := ha (by simp : i.castSucc < i.succ)
  have haj := ha (by simp : j.castSucc < j.succ)
  have hbi := hb (by simp : i.castSucc < i.succ)
  have hbj := hb (by simp : j.castSucc < j.succ)
  have hxi := blend_mem hai.le hθ
  have hxj := blend_mem haj.le hφ
  have hyi := blend_mem hbi.le hθ
  have hyj := blend_mem hbj.le hφ
  rcases lt_trichotomy i j with hij | hij | hij
  · have hij' : i.succ ≤ j.castSucc := by
      change i.val + 1 ≤ j.val
      exact hij
    have hab := ha.monotone hij'
    have hbb := hb.monotone hij'
    by_contra hnot
    have hyy := le_of_not_gt hnot
    have hθone : θ = 1 := (blend_strictMono hbi).injective (by
      rw [blend_one]
      linarith [hyi.2, hyj.1])
    have hφzero : φ = 0 := (blend_strictMono hbj).injective (by
      rw [blend_zero]
      linarith [hyi.2, hyj.1])
    have heq : i.succ = j.castSucc := hb.injective (by linarith [hyi.2, hyj.1])
    simp only [hθone, hφzero, blend_zero, blend_one, heq] at hxx
    exact lt_irrefl _ hxx
  · subst j
    exact blend_strictMono hbi ((blend_strictMono hai).lt_iff_lt.mp hxx)
  · have hji : j.succ ≤ i.castSucc := by
      change j.val + 1 ≤ i.val
      exact hij
    have hab := ha.monotone hji
    linarith [hxi.1, hxj.2]

theorem graph_unique {n : ℕ} {a b : Fin (n + 2) → ℝ}
    (ha : StrictMono a) (hb : StrictMono b) {x y z : ℝ}
    (hy : Graph a b x y) (hz : Graph a b x z) : y = z := by
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · exact lt_irrefl x (graph_strictMono hb ha hy.symm hz.symm h)
  · exact lt_irrefl x (graph_strictMono hb ha hz.symm hy.symm h)

theorem graph_knot {n : ℕ} (a b : Fin (n + 2) → ℝ) (k : Fin (n + 2)) :
    Graph a b (a k) (b k) := by
  by_cases h : k = Fin.last (n + 1)
  · subst k
    refine ⟨Fin.last n, 1, by simp, ?_, ?_⟩ <;> simp
  · obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr h
    exact ⟨i, 0, by simp, by simp, by simp⟩

def interpolate {n : ℕ} (a b : Fin (n + 2) → ℝ) (ha : StrictMono a) (hb : StrictMono b)
    (x : Icc (a 0) (a (Fin.last (n + 1)))) : Icc (b 0) (b (Fin.last (n + 1))) :=
  ⟨(graph_total a b ha x x.property).choose,
    graph_mem hb (graph_total a b ha x x.property).choose_spec⟩

theorem interpolate_graph {n : ℕ} (a b : Fin (n + 2) → ℝ)
    (ha : StrictMono a) (hb : StrictMono b) (x : Icc (a 0) (a (Fin.last (n + 1)))) :
    Graph a b x (interpolate a b ha hb x) :=
  (graph_total a b ha x x.property).choose_spec

theorem interpolate_strictMono {n : ℕ} (a b : Fin (n + 2) → ℝ)
    (ha : StrictMono a) (hb : StrictMono b) : StrictMono (interpolate a b ha hb) := by
  intro x y hxy
  exact graph_strictMono ha hb (interpolate_graph a b ha hb x)
    (interpolate_graph a b ha hb y) hxy

theorem interpolate_surjective {n : ℕ} (a b : Fin (n + 2) → ℝ)
    (ha : StrictMono a) (hb : StrictMono b) : Function.Surjective (interpolate a b ha hb) := by
  intro y
  obtain ⟨x, hx⟩ := graph_total b a hb y y.property
  refine ⟨⟨x, graph_mem ha hx⟩, ?_⟩
  apply Subtype.ext
  exact graph_unique ha hb (interpolate_graph a b ha hb _) hx.symm

/-- The piecewise-affine increasing bijection between the two knot intervals. -/
def orderIso {n : ℕ} (a b : Fin (n + 2) → ℝ) (ha : StrictMono a) (hb : StrictMono b) :
    Icc (a 0) (a (Fin.last (n + 1))) ≃o Icc (b 0) (b (Fin.last (n + 1))) where
  toEquiv := Equiv.ofBijective (interpolate a b ha hb)
    ⟨(interpolate_strictMono a b ha hb).injective, interpolate_surjective a b ha hb⟩
  map_rel_iff' := (interpolate_strictMono a b ha hb).le_iff_le

theorem orderIso_graph {n : ℕ} (a b : Fin (n + 2) → ℝ)
    (ha : StrictMono a) (hb : StrictMono b) (x : Icc (a 0) (a (Fin.last (n + 1)))) :
    Graph a b x (orderIso a b ha hb x) := interpolate_graph a b ha hb x

theorem orderIso_knot {n : ℕ} (a b : Fin (n + 2) → ℝ)
    (ha : StrictMono a) (hb : StrictMono b) (k : Fin (n + 2)) :
    (orderIso a b ha hb ⟨a k, ha.monotone (Fin.zero_le k),
      ha.monotone (Fin.le_last k)⟩ : ℝ) = b k :=
  graph_unique ha hb (orderIso_graph a b ha hb _) (graph_knot a b k)

theorem graph_displacement_le {n : ℕ} {a b : Fin (n + 2) → ℝ} {δ x y : ℝ}
    (hδ : ∀ k, |b k - a k| ≤ δ) (h : Graph a b x y) : |y - x| ≤ δ := by
  obtain ⟨i, θ, hθ, rfl, rfl⟩ := h
  have hθ' : 0 ≤ 1 - θ := sub_nonneg.mpr hθ.2
  calc
    _ = |(1 - θ) * (b i.castSucc - a i.castSucc) + θ * (b i.succ - a i.succ)| := by
      congr 1
      unfold blend
      ring
    _ ≤ |(1 - θ) * (b i.castSucc - a i.castSucc)| +
        |θ * (b i.succ - a i.succ)| := abs_add _ _
    _ = (1 - θ) * |b i.castSucc - a i.castSucc| + θ * |b i.succ - a i.succ| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hθ', abs_of_nonneg hθ.1]
    _ ≤ (1 - θ) * δ + θ * δ := add_le_add
      (mul_le_mul_of_nonneg_left (hδ _) hθ') (mul_le_mul_of_nonneg_left (hδ _) hθ.1)
    _ = δ := by ring

theorem orderIso_displacement_le {n : ℕ} (a b : Fin (n + 2) → ℝ)
    (ha : StrictMono a) (hb : StrictMono b) {δ : ℝ}
    (hδ : ∀ k, |b k - a k| ≤ δ) (x : Icc (a 0) (a (Fin.last (n + 1)))) :
    |(orderIso a b ha hb x : ℝ) - x| ≤ δ :=
  graph_displacement_le hδ (orderIso_graph a b ha hb x)

/-- A genuine time change matching all endpoint-inclusive knots, with the
uniform displacement bounded by the displacement of the knots. -/
theorem knot_mem_interval {n : ℕ} (T : ℝ≥0) (a : Fin (n + 2) → ℝ)
    (ha : StrictMono a) (ha0 : a 0 = 0) (haT : a (Fin.last (n + 1)) = T)
    (k : Fin (n + 2)) : a k ∈ Icc (0 : ℝ) (T : ℝ) := by
  rw [← ha0, ← haT]
  exact ⟨ha.monotone (Fin.zero_le k), ha.monotone (Fin.le_last k)⟩

theorem exists_timeChange {n : ℕ} (T : ℝ≥0) (a b : Fin (n + 2) → ℝ)
    (ha : StrictMono a) (hb : StrictMono b)
    (ha0 : a 0 = 0) (hb0 : b 0 = 0)
    (haT : a (Fin.last (n + 1)) = T) (hbT : b (Fin.last (n + 1)) = T)
    (δ : ℝ) (hδ : ∀ k, |b k - a k| ≤ δ) :
    ∃ e : SkorokhodJ1.TimeChange T,
      (∀ k, (e ⟨a k, knot_mem_interval T a ha ha0 haT k⟩ : ℝ) = b k) ∧
      ∀ t, |(e t : ℝ) - t| ≤ δ := by
  have hAs : Icc (a 0) (a (Fin.last (n + 1))) = Icc (0 : ℝ) (T : ℝ) := by rw [ha0, haT]
  have hBs : Icc (b 0) (b (Fin.last (n + 1))) = Icc (0 : ℝ) (T : ℝ) := by rw [hb0, hbT]
  let e := (OrderIso.setCongr _ _ hAs).symm.trans
    ((orderIso a b ha hb).trans (OrderIso.setCongr _ _ hBs))
  refine ⟨e, ?_, ?_⟩
  · intro k
    exact orderIso_knot a b ha hb k
  · intro t
    exact orderIso_displacement_le a b ha hb hδ _

/-- Finite-set interface for aligning jump times. The endpoints are included
in `S`, and the zero-length interval is allowed. -/
theorem exists_timeChange_finset (T : ℝ≥0) (S : Finset ℝ)
    (h0 : 0 ∈ S) (hT : (T : ℝ) ∈ S)
    (hS : ∀ s ∈ S, s ∈ Icc (0 : ℝ) (T : ℝ))
    (g : ℝ → ℝ) (hg : StrictMonoOn g (S : Set ℝ))
    (hg0 : g 0 = 0) (hgT : g T = T)
    (δ : ℝ) (hδ : ∀ s ∈ S, |g s - s| ≤ δ) :
    ∃ e : SkorokhodJ1.TimeChange T,
      (∀ s (hs : s ∈ S), (e ⟨s, hS s hs⟩ : ℝ) = g s) ∧
      ∀ t, |(e t : ℝ) - t| ≤ δ := by
  classical
  have hδ0 : 0 ≤ δ := by simpa [hg0] using hδ 0 h0
  by_cases hzero : T = 0
  · refine ⟨OrderIso.refl _, ?_, ?_⟩
    · intro s hs
      have hs0 : s = 0 := le_antisymm (by simpa [hzero] using (hS s hs).2) (hS s hs).1
      simp [hs0, hg0]
    · intro t
      simpa using hδ0
  have hpos : (0 : ℝ) < T := by exact_mod_cast (pos_iff_ne_zero.mpr hzero)
  have htwo : 2 ≤ S.card := by
    have hpair : ({0, (T : ℝ)} : Finset ℝ) ⊆ S := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact h0
      · exact hT
    have hc := Finset.card_le_card hpair
    simpa [ne_of_lt hpos] using hc
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le htwo
  have hcard : S.card = n + 2 := by omega
  let e := S.orderIsoOfFin hcard
  let a : Fin (n + 2) → ℝ := fun i => e i
  let b : Fin (n + 2) → ℝ := fun i => g (a i)
  have ha : StrictMono a := fun _ _ hij => e.strictMono hij
  have hb : StrictMono b := fun i j hij => hg (e i).property (e j).property (ha hij)
  have ha0 : a 0 = 0 := by
    apply le_antisymm
    · have hh := e.monotone (Fin.zero_le (e.symm ⟨0, h0⟩))
      simpa [a] using hh
    · exact (hS _ (e 0).property).1
  have haT : a (Fin.last (n + 1)) = T := by
    apply le_antisymm
    · exact (hS _ (e (Fin.last (n + 1))).property).2
    · have hh := e.monotone (Fin.le_last (e.symm ⟨(T : ℝ), hT⟩))
      simpa [a] using hh
  have hb0 : b 0 = 0 := by simp only [b, ha0, hg0]
  have hbT : b (Fin.last (n + 1)) = T := by simp only [b, haT, hgT]
  obtain ⟨change, hknots, hdisplace⟩ := exists_timeChange T a b ha hb ha0 hb0 haT hbT δ
    (fun k => hδ _ (e k).property)
  refine ⟨change, ?_, hdisplace⟩
  intro s hs
  let i := e.symm ⟨s, hs⟩
  have hi : a i = s := congrArg Subtype.val (e.apply_symm_apply ⟨s, hs⟩)
  simpa only [b, hi] using hknots i

end CarryingCapacity.FiniteTimeChange
