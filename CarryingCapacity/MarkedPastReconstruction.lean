import CarryingCapacity.MarkedNoiseObservation
import CarryingCapacity.CommonNoiseFiltration
import CarryingCapacity.NullAugmentedIndependence

/-!
# Reconstructing the observed past from past counting measures

Visible events form a strictly ordered prefix in each half-open height strip.
This Borel condition makes their actual counting measures determine the entire
censored array. A measurable inverse therefore uses only counts up to the
given time, without inspecting any future clock or mark.
-/

noncomputable section
open MeasureTheory MeasurableSpace Set Filter
open scoped Classical ENNReal

namespace CarryingCapacity.MarkedPastReconstruction
open CommonNoiseFiltration MarkedNoiseObservation

variable {J : Type*}

/-- The actual measure represented by the visible part of an event array. -/
def visibleMeasure (t : ℝ) (v : EventView J) (j : J) : Measure (ℝ × ℝ) :=
  Measure.sum (fun p : ℕ × ℕ =>
    if (v (j,p)).1 ≤ t then Measure.dirac (v (j,p)) else 0)

theorem measurable_visibleMeasure (t : ℝ) (j : J) :
    Measurable (fun v : EventView J => visibleMeasure t v j) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  simp only [visibleMeasure, Measure.sum_apply _ hS]
  apply Measurable.ennreal_tsum
  intro p
  have hv : Measurable (fun v : EventView J => v (j,p)) := measurable_pi_apply _
  exact (Measure.measurable_coe hS).comp
    ((Measure.measurable_dirac.comp hv).ite
      (measurableSet_le hv.fst measurable_const) (measurable_const : Measurable (fun _ : EventView J => (0 : Measure (ℝ × ℝ)))))

/-- Every hidden entry has the fixed sentinel; visible entries are a strictly
time-ordered prefix within their own half-open strip. -/
def Ordered (t : ℝ) (v : EventView J) : Prop := ∀ j n,
  (∀ k, (v (j,n,k)).1 ≤ t → (v (j,n,k)).2 ∈ Ico (n : ℝ) (n+1)) ∧
  (∀ k, ¬(v (j,n,k)).1 ≤ t → v (j,n,k) = (t+1,0)) ∧
  (∀ k l, k < l → (v (j,n,l)).1 ≤ t → (v (j,n,k)).1 < (v (j,n,l)).1)

theorem measurableSet_ordered [Countable J] (t : ℝ) :
    MeasurableSet {v : EventView J | Ordered t v} := by
  have hm (e : ChronologicalEvents.Event J) : Measurable (fun v : EventView J => v e) :=
    measurable_pi_apply _
  simp only [Ordered, setOf_forall, setOf_and]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro n
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · apply MeasurableSet.iInter
    intro k
    simp only [imp_iff_not_or, setOf_or]
    exact (measurableSet_le (hm (j,n,k)).fst measurable_const).compl.union
      (measurableSet_Ico.preimage (hm (j,n,k)).snd)
  · apply MeasurableSet.iInter
    intro k
    simp only [imp_iff_not_or, not_not, setOf_or]
    exact (measurableSet_le (hm (j,n,k)).fst measurable_const).union
      ((measurableSet_singleton (t+1,0)).preimage (hm (j,n,k)))
  · apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iInter
    intro l
    by_cases hkl : k < l
    · simp only [hkl, iInter_true, imp_iff_not_or, setOf_or]
      exact
        (measurableSet_le (hm (j,n,l)).fst measurable_const).compl.union
          (measurableSet_lt (hm (j,n,k)).fst (hm (j,n,l)).fst)
    · simp [hkl]

theorem singleton_mass_ne_zero_iff (t : ℝ) (v : EventView J) (j : J) (z : ℝ × ℝ) :
    visibleMeasure t v j {z} ≠ 0 ↔ ∃ p, (v (j,p)).1 ≤ t ∧ v (j,p) = z := by
  rw [visibleMeasure, Measure.sum_apply _ (measurableSet_singleton z)]
  simp only [ne_eq, ENNReal.tsum_eq_zero, not_forall]
  apply exists_congr
  intro p
  by_cases hp : (v (j,p)).1 ≤ t
  · simp only [hp, if_pos, true_and]
    by_cases he : v (j,p) = z
    · simp [hp, Measure.dirac_apply', he]
    · simp [hp, Measure.dirac_apply', he]
  · simp [hp]

/-- Matching visible atoms identifies their strip without using event labels. -/
theorem strip_eq_of_point_eq {t : ℝ} {v w : EventView J}
    (hv : Ordered t v) (hw : Ordered t w) (j : J) (n k m l : ℕ)
    (hk : (v (j,n,k)).1 ≤ t) (hl : (w (j,m,l)).1 ≤ t)
    (he : v (j,n,k) = w (j,m,l)) : n = m := by
  have hn := (hv j n).1 k hk
  have hm := (hw j m).1 l hl
  have hh := congrArg Prod.snd he
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hc : (n : ℝ)+1 ≤ m := by exact_mod_cast h
    linarith [hn.1,hn.2,hm.1,hm.2]
  · have hc : (m : ℝ)+1 ≤ n := by exact_mod_cast h
    linarith [hn.1,hn.2,hm.1,hm.2]

/-- Equal visible measures match every visible indexed atom in the same strip. -/
theorem exists_match {t : ℝ} {v w : EventView J}
    (hv : Ordered t v) (hw : Ordered t w)
    (he : ∀ j, visibleMeasure t v j = visibleMeasure t w j)
    (j : J) (n k : ℕ) (hk : (v (j,n,k)).1 ≤ t) :
    ∃ l, (w (j,n,l)).1 ≤ t ∧ w (j,n,l) = v (j,n,k) := by
  have hmass : visibleMeasure t w j {v (j,n,k)} ≠ 0 := by
    rw [← he j]
    exact (singleton_mass_ne_zero_iff t v j _).mpr ⟨(n,k),hk,rfl⟩
  obtain ⟨⟨m,l⟩,hl,heq⟩ := (singleton_mass_ne_zero_iff t w j _).mp hmass
  have hmn := strip_eq_of_point_eq hw hv j m l n k hl hk heq
  subst m
  exact ⟨l,hl,heq⟩

/-- The visible-prefix rank is forced by the actual measures. -/
theorem ordered_eq_of_measures {t : ℝ} {v w : EventView J}
    (hv : Ordered t v) (hw : Ordered t w)
    (he : ∀ j, visibleMeasure t v j = visibleMeasure t w j) : v = w := by
  funext e
  rcases e with ⟨j,n,k⟩
  have hpoint : ∀ k, v (j,n,k) = w (j,n,k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      have hle : ∀ a b : EventView J, Ordered t a → Ordered t b →
          (∀ j, visibleMeasure t a j = visibleMeasure t b j) →
          (∀ l < k, a (j,n,l) = b (j,n,l)) →
          (a (j,n,k)).1 ≤ t → a (j,n,k) = b (j,n,k) := by
        intro a b ha hb hab hprev hk
        obtain ⟨l,hl,hel⟩ := exists_match ha hb hab j n k hk
        have hkl : k ≤ l := by
          by_contra hn
          have hlk := lt_of_not_ge hn
          have hlt := (ha j n).2.2 l k hlk hk
          rw [hprev l hlk] at hlt
          rw [hel] at hlt
          exact (lt_irrefl _ hlt)
        have hlk : l ≤ k := by
          by_contra hn
          have hkl' := lt_of_not_ge hn
          have hbkl := (hb j n).2.2 k l hkl' hl
          have hbk : (b (j,n,k)).1 ≤ t := hbkl.le.trans hl
          obtain ⟨m,hm,hem⟩ := exists_match hb ha (fun j => (hab j).symm) j n k hbk
          have hkm : k ≤ m := by
            by_contra hnm
            have hmk := lt_of_not_ge hnm
            have hlt := (hb j n).2.2 m k hmk hbk
            rw [← hprev m hmk, hem] at hlt
            exact lt_irrefl _ hlt
          have hcontr : (a (j,n,k)).1 ≤ (a (j,n,m)).1 := by
            rcases hkm.eq_or_lt with rfl | hkm
            · exact le_rfl
            · exact ((ha j n).2.2 k m hkm hm).le
          rw [hem, ← hel] at hcontr
          exact (not_le_of_gt hbkl) hcontr
        have : l = k := le_antisymm hlk hkl
        simpa only [this] using hel.symm
      by_cases hk : (v (j,n,k)).1 ≤ t
      · exact hle v w hv hw he ih hk
      · by_cases hk' : (w (j,n,k)).1 ≤ t
        · exact (hle w v hw hv (fun j => (he j).symm)
            (fun l hl => (ih l hl).symm) hk').symm
        · rw [(hv j n).2.1 k hk, (hw j n).2.1 k hk']
  exact hpoint k

def pastSet (t : ℝ) : Set (ℝ × ℝ) := Iic t ×ˢ univ

theorem measurableSet_pastSet (t : ℝ) : MeasurableSet (pastSet t) :=
  measurableSet_Iic.prod MeasurableSet.univ

def pastMeasures (t : ℝ) (M : J → Measure (ℝ × ℝ)) : J → Measure (ℝ × ℝ) :=
  fun j => (M j).restrict (pastSet t)

theorem measurable_pastMeasures (t : ℝ) : Measurable (pastMeasures (J := J) t) := by
  apply measurable_pi_lambda
  intro j
  apply Measure.measurable_of_measurable_coe
  intro S hS
  simp only [pastMeasures, Measure.restrict_apply hS]
  exact (Measure.measurable_coe (hS.inter (measurableSet_pastSet t))).comp (measurable_pi_apply j)

/-- The measure represented by the censored history is exactly restriction in time. -/
theorem visibleMeasure_view (t : ℝ) (ω : MarkedNoise.Sample J) (j : J) :
    visibleMeasure t (view t ω) j = (MarkedNoise.countingMeasure j ω).restrict (pastSet t) := by
  rw [visibleMeasure, MarkedNoise.countingMeasure, Measure.restrict_sum _ (measurableSet_pastSet t)]
  congr 1
  funext p
  by_cases h : (MarkedNoise.point j ω p).1 ≤ t
  · simp [view, censor, points, h, restrict_dirac, pastSet]
  · have hs : ¬t+1 ≤ t := by linarith
    simp [view, censor, points, h, hs, restrict_dirac, pastSet]

theorem view_visible_iff (t : ℝ) (ω : MarkedNoise.Sample J) (e : ChronologicalEvents.Event J) :
    (view t ω e).1 ≤ t ↔ (MarkedNoise.point e.1 ω e.2).1 ≤ t := by
  by_cases h : (MarkedNoise.point e.1 ω e.2).1 ≤ t
  · simp [view, censor, points, h]
  · have hs : ¬t+1 ≤ t := by linarith
    simp [view, censor, points, h, hs]

theorem ordered_view (t : ℝ) (ω : MarkedNoise.Sample J)
    (hω : MarkedNoiseReconstruction.Good ω) : Ordered t (view t ω) := by
  intro j n
  refine ⟨?_,?_,?_⟩
  · intro k hk
    have hv := (view_visible_iff t ω (j,n,k)).mp hk
    simp only [view, censor, points, hv, if_pos]
    change (n:ℝ) + (ω (j,n)).2 k ∈ Ico (n:ℝ) (n+1)
    have hm := (hω (j,n)).2 k
    exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
  · intro k hk
    have hv : ¬(MarkedNoise.point j ω (n,k)).1 ≤ t := by
      simpa only [← view_visible_iff t ω (j,n,k)] using hk
    simp only [view, censor, points, hv, if_false]
  · intro k l hkl hl
    have hvl := (view_visible_iff t ω (j,n,l)).mp hl
    have hlt : (MarkedNoise.point j ω (n,k)).1 < (MarkedNoise.point j ω (n,l)).1 :=
      (hω (j,n)).1 (Nat.add_lt_add_right hkl 1)
    have hvk := hlt.le.trans hvl
    simpa only [view, censor, points, hvl, hvk, if_pos] using hlt

variable (J : Type*)

def Good (t : ℝ) (v : EventView J) : Prop := Ordered t v ∧
  ∀ j n, visibleMeasure t v j (box n) < ∞

theorem measurableSet_good [Countable J] (t : ℝ) :
    MeasurableSet {v : EventView J | Good J t v} := by
  change MeasurableSet ({v : EventView J | Ordered t v} ∩
    {v | ∀ j n, visibleMeasure t v j (box n) < ∞})
  apply (measurableSet_ordered t).inter
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro n
  exact measurableSet_lt
    ((Measure.measurable_coe (measurableSet_box n)).comp (measurable_visibleMeasure t j)) measurable_const

theorem ae_good_view [Countable J] (t : ℝ) :
    ∀ᵐ ω ∂MarkedNoise.law J, Good J t (view t ω) := by
  filter_upwards [MarkedNoiseObservation.ae_good J] with ω hω
  refine ⟨ordered_view t ω hω.1, ?_⟩
  intro j n
  rw [visibleMeasure_view]
  exact (Measure.restrict_le_self _).trans_lt (hω.2 j n)

def observeVisible (t : ℝ) (v : EventView J) : Observation J :=
  observeMeasures J (visibleMeasure t v)

theorem measurable_observeVisible (t : ℝ) : Measurable (observeVisible J t) :=
  (measurable_observeMeasures J).comp (measurable_pi_lambda _ (measurable_visibleMeasure t))

theorem injective_observeVisible (t : ℝ) :
    Set.InjOn (observeVisible J t) {v | Good J t v} := by
  intro v hv w hw he
  apply ordered_eq_of_measures hv.1 hw.1
  intro j
  apply measure_eq_of_observations _ _ (fun n => (hv.2 j n).ne)
  intro n I
  exact congrFun he (j,n,I)

/-- The past decoder is built on the Borel space of valid censored arrays. -/
theorem exists_measurable_decoder [Countable J] (t : ℝ) :
    ∃ d : Observation J → EventView J, Measurable d ∧
      ∀ v, Good J t v → d (observeVisible J t v) = v := by
  let S := {v : EventView J | Good J t v}
  letI : StandardBorelSpace S := (measurableSet_good J t).standardBorel
  let f : S → Observation J := fun v => observeVisible J t v.1
  have hm : Measurable f := (measurable_observeVisible J t).comp measurable_subtype_coe
  have hi : Function.Injective f := by
    intro v w he
    exact Subtype.ext (injective_observeVisible J t v.property w.property he)
  obtain ⟨d,hd,he⟩ := (hm.measurableEmbedding hi).exists_measurable_extend
    (measurable_subtype_coe : Measurable (Subtype.val : S → EventView J))
    (fun _ => ⟨fun _ => (t+1,0)⟩)
  exact ⟨d,hd,fun v hv => congrFun he ⟨v,hv⟩⟩

def decode [Countable J] (t : ℝ) : Observation J → EventView J :=
  (exists_measurable_decoder J t).choose

theorem measurable_decode [Countable J] (t : ℝ) : Measurable (decode J t) :=
  (exists_measurable_decoder J t).choose_spec.1

theorem decode_observeVisible [Countable J] (t : ℝ) (v : EventView J) (hv : Good J t v) :
    decode J t (observeVisible J t v) = v :=
  (exists_measurable_decoder J t).choose_spec.2 v hv

def observePast (t : ℝ) (ω : MarkedNoise.Sample J) : Observation J :=
  observeMeasures J (pastMeasures t (fun j => MarkedNoise.countingMeasure j ω))

theorem observeVisible_view (t : ℝ) (ω : MarkedNoise.Sample J) :
    observeVisible J t (view t ω) = observePast J t ω := by
  have he : visibleMeasure t (view t ω) = pastMeasures t (fun j => MarkedNoise.countingMeasure j ω) :=
    funext (visibleMeasure_view t ω)
  exact congrArg (observeMeasures J) he

/-- Past counts alone recover the entire raw history on one event. -/
theorem ae_decode_observePast [Countable J] (t : ℝ) :
    ∀ᵐ ω ∂MarkedNoise.law J, decode J t (observePast J t ω) = view t ω := by
  filter_upwards [ae_good_view J t] with ω hω
  rw [← observeVisible_view]
  exact decode_observeVisible J t _ hω

/-- The natural sigma algebra of the actual counting measures restricted at time t. -/
def countingHistory (t : ℝ) : MeasurableSpace (MarkedNoise.Sample J) :=
  MeasurableSpace.comap
    (fun ω => pastMeasures t (fun j => MarkedNoise.countingMeasure j ω)) inferInstance

theorem measurable_observePast_at (t : ℝ) :
    Measurable[countingHistory J t] (observePast J t) :=
  (measurable_observeMeasures J).comp (comap_measurable _)

/-- The counting-measure past is contained in the indexed raw history on all samples. -/
theorem countingHistory_le_filtration (t : ℝ) :
    countingHistory J t ≤ CommonNoiseFiltration.filtration J t := by
  have h : Measurable[CommonNoiseFiltration.filtration J t]
      (fun ω : MarkedNoise.Sample J => visibleMeasure t (view t ω)) :=
    (measurable_pi_lambda _ (measurable_visibleMeasure t)).comp (measurable_view_at t)
  have he : (fun ω : MarkedNoise.Sample J => visibleMeasure t (view t ω)) =
      (fun ω => pastMeasures t (fun j => MarkedNoise.countingMeasure j ω)) := by
    funext ω j
    exact visibleMeasure_view t ω j
  rw [he] at h
  exact h.comap_le

/-- Completion of the actual count history reveals every indexed past event,
using the derived past decoder and only ambient null sets. -/
theorem measurable_view_augmented_countingHistory [Countable J] (t : ℝ) :
    Measurable[NullAugmentedIndependence.augmentation (countingHistory J t) (MarkedNoise.law J)]
      (view (J := J) t) := by
  intro S hS
  refine ⟨(fun ω => decode J t (observePast J t ω)) ⁻¹' S,
    ((measurable_decode J t).comp (measurable_observePast_at J t)) hS, ?_⟩
  filter_upwards [ae_decode_observePast J t] with ω hω
  change (view t ω ∈ S) = (decode J t (observePast J t ω) ∈ S)
  rw [hω]

theorem filtration_le_augmented_countingHistory [Countable J] (t : ℝ) :
    CommonNoiseFiltration.filtration J t ≤
      NullAugmentedIndependence.augmentation (countingHistory J t) (MarkedNoise.law J) :=
  (measurable_view_augmented_countingHistory J t).comap_le

/-- The two natural histories agree after augmentation by the same ambient
null sets. This identifies a count-based history, not a process-generated one. -/
theorem augmented_countingHistory_eq [Countable J] (t : ℝ) :
    NullAugmentedIndependence.augmentation (countingHistory J t) (MarkedNoise.law J) =
      NullAugmentedIndependence.augmentation (CommonNoiseFiltration.filtration J t)
        (MarkedNoise.law J) := by
  apply le_antisymm
  · rintro S ⟨B,hB,hSB⟩
    exact ⟨B,countingHistory_le_filtration J t _ hB,hSB⟩
  · rintro S ⟨B,hB,hSB⟩
    obtain ⟨C,hC,hBC⟩ := filtration_le_augmented_countingHistory J t _ hB
    exact ⟨C,hC,hSB.trans hBC⟩

end CarryingCapacity.MarkedPastReconstruction
