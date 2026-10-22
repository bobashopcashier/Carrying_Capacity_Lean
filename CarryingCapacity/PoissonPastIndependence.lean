import CarryingCapacity.PoissonFiniteDimensional
import CarryingCapacity.PoissonMoments

/-!
# Poisson increments and the full past

Independence from finite collections of past counts is obtained from the full
finite-grid law. Directed unions then recover the entire natural filtration.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace CarryingCapacity.PoissonPastIndependence
open CountableJumpProcess FrozenProcess PoissonClockLaw PoissonIncrements
open PoissonFiniteDimensional

/-- Reconstruct the cumulative vector, starting at zero, from adjacent increments. -/
def prefixCounts : {k : ℕ} → (Fin k → ℕ) → Fin (k+1) → ℕ
  | 0, _ => fun _ => 0
  | _+1, d => Fin.cons 0 (fun i => d 0 + prefixCounts (fun j => d j.succ) i)

/-- Telescoping for nondecreasing natural-number vectors. -/
theorem prefixCounts_differences {k : ℕ} (f : Fin (k+1) → ℕ) (hf : Monotone f) :
    prefixCounts (fun i : Fin k => f i.succ - f i.castSucc) = fun i => f i - f 0 := by
  induction k with
  | zero =>
    funext i
    have hi : i = 0 := by apply Fin.ext; omega
    simp [hi,prefixCounts]
  | succ k ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [prefixCounts]
    · have ht := congrFun (ih (fun i => f i.succ) (hf.comp (fun _ _ h => by simpa using h))) j
      have h01 : f 0 ≤ f (Fin.succ 0) := hf (Fin.zero_le _)
      have h1j : f (Fin.succ 0) ≤ f j.succ := hf (by exact Nat.succ_le_succ (Nat.zero_le j.val))
      simp only [prefixCounts,Fin.cons_succ,Fin.succ_castSucc,Fin.castSucc_zero] at ht ⊢
      rw [ht]
      omega

/-- Past counts on a nondecreasing grid ending at s are independent of the next increment. -/
theorem independent_ordered_past (r : ℝ) (hr : 0 < r) {k : ℕ}
    (v : Fin (k+1) → ℝ) (hv : Monotone v) (hv0 : v 0 = 0)
    (s t : ℝ) (hvs : v (Fin.last k) = s) (ht : 0 ≤ t) :
    IndepFun (fun ω i => proposalCount ω (v i)) (fun ω => increment ω s t)
      (waitingTimeLaw r hr) := by
  classical
  let u : Fin (k+2) → ℝ := Fin.snoc v (s+t)
  have hu : Monotone u := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [u,Fin.snoc_castSucc,Fin.succ_last,Fin.snoc_last,hvs] using le_add_of_nonneg_right ht
    · simpa only [u,Fin.snoc_castSucc,Fin.succ_castSucc] using hv (Fin.castSucc_le_succ j)
  have hu0 : 0 ≤ u 0 := by
    change 0 ≤ u (0 : Fin (k+1)).castSucc
    simp only [u,Fin.snoc_castSucc,hv0,le_refl]
  let D : Fin (k+1) → ClockSpace → ℕ :=
    fun i ω => proposalCount ω (u i.succ) - proposalCount ω (u i.castSucc)
  have hD := independent_increments_at_times r hr u hu hu0
  have hDm : ∀ i, Measurable (D i) := fun i =>
    (measurable_proposalCount _).sub (measurable_proposalCount _)
  let S : Finset (Fin (k+1)) := Finset.univ.erase (Fin.last k)
  let T : Finset (Fin (k+1)) := {Fin.last k}
  have hST : Disjoint S T := by simp [S,T]
  have hblocks := hD.indepFun_finset S T hST hDm
  let past : (S → ℕ) → (Fin (k+1) → ℕ) := fun d =>
    prefixCounts (fun i : Fin k => d ⟨i.castSucc,by simp [S]⟩)
  let future : (T → ℕ) → ℕ := fun d => d ⟨Fin.last k,by simp [T]⟩
  have hpast : Measurable past := measurable_of_countable _
  have hfuture : Measurable future := measurable_of_countable _
  have hind := hblocks.comp hpast hfuture
  apply hind.congr
  · filter_upwards [ae_locally_finite r hr,ae_positive r hr] with ω hω hpos
    have hzero : proposalCount ω 0 = 0 := (proposalCount_eq_zero_iff hω.1 hω.2 0).mpr (hpos 0)
    have hp := prefixCounts_differences (fun i => proposalCount ω (v i))
      ((proposalCount_mono hω.2).comp hv)
    simpa only [Function.comp_apply,past,D,u,Fin.succ_castSucc,Fin.snoc_castSucc,hv0,hzero,
      Nat.sub_zero] using hp
  · exact ae_of_all _ (fun ω => by simp [Function.comp_apply,future,D,u,increment,hvs])

/-- The observation times in the closed past interval. -/
abbrev PastTime (s : ℝ) := {u : ℝ // 0 ≤ u ∧ u ≤ s}

/-- Independence from any finite vector of past observations. -/
theorem independent_finite_past (r : ℝ) (hr : 0 < r) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (F : Finset (PastTime s)) :
    IndepFun (fun ω (i : F) => proposalCount ω i.1.1) (fun ω => increment ω s t)
      (waitingTimeLaw r hr) := by
  classical
  let S : Finset ℝ := insert 0 (insert s (F.image Subtype.val))
  have hS : ∀ x ∈ S, 0 ≤ x ∧ x ≤ s := by
    intro x hx
    simp only [S,Finset.mem_insert,Finset.mem_image] at hx
    rcases hx with rfl | rfl | ⟨u,hu,rfl⟩
    · exact ⟨le_rfl,hs⟩
    · exact ⟨hs,le_rfl⟩
    · exact u.property
  have h0S : 0 ∈ S := by simp [S]
  have hsS : s ∈ S := by simp [S]
  obtain ⟨k,hcard⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr ⟨0,h0S⟩)
  let e : Fin (k+1) ≃o S := S.orderIsoOfFin hcard
  let v : Fin (k+1) → ℝ := fun i => (e i).1
  have hv : Monotone v := e.monotone
  have hv0 : v 0 = 0 := by
    have hlo := (hS _ (e 0).property).1
    have hhi : v 0 ≤ 0 := by
      have h := hv (Fin.zero_le (e.symm ⟨0,h0S⟩))
      simpa only [v,e.apply_symm_apply] using h
    exact le_antisymm hhi hlo
  have hvs : v (Fin.last k) = s := by
    have hhi := (hS _ (e (Fin.last k)).property).2
    have hlo : s ≤ v (Fin.last k) := by
      have h := hv (Fin.le_last (e.symm ⟨s,hsS⟩))
      simpa only [v,e.apply_symm_apply] using h
    exact le_antisymm hhi hlo
  have hind := independent_ordered_past r hr v hv hv0 s t hvs ht
  let index : F → Fin (k+1) := fun i => e.symm ⟨i.1.1,by
    simp only [S,Finset.mem_insert,Finset.mem_image]
    exact Or.inr (Or.inr ⟨i.1,i.property,rfl⟩)⟩
  let select : (Fin (k+1) → ℕ) → (F → ℕ) := fun d i => d (index i)
  have hsel : Measurable select := measurable_of_countable _
  have h := hind.comp hsel measurable_id
  convert h using 1
  funext ω i
  congr 1
  simp only [Function.comp_apply,select,index,v,e.apply_symm_apply]

/-- The sigma-algebra generated by the full past count trajectory. -/
def past (s : ℝ) : MeasurableSpace ClockSpace :=
  ⨆ u : PastTime s, MeasurableSpace.comap (fun ω => proposalCount ω u.1) inferInstance

/-- The sigma-algebra generated by a finite collection of past counts. -/
def finitePast (s : ℝ) (F : Finset (PastTime s)) : MeasurableSpace ClockSpace :=
  ⨆ u ∈ F, MeasurableSpace.comap (fun ω => proposalCount ω u.1) inferInstance

theorem past_le (s : ℝ) : past s ≤ (inferInstance : MeasurableSpace ClockSpace) := by
  apply iSup_le
  intro u
  exact (measurable_proposalCount u.1).comap_le

theorem finitePast_le (s : ℝ) (F : Finset (PastTime s)) : finitePast s F ≤ (inferInstance : MeasurableSpace ClockSpace) := by
  apply iSup₂_le
  intro u hu
  exact (measurable_proposalCount u.1).comap_le

theorem finitePast_mono (s : ℝ) : Monotone (finitePast s) := by
  intro F G hFG
  unfold finitePast
  exact iSup₂_le (fun u hu => le_iSup_of_le u (le_iSup_of_le (hFG hu) le_rfl))

theorem iSup_finitePast (s : ℝ) : (⨆ F : Finset (PastTime s), finitePast s F) = past s := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro F
    exact iSup₂_le (fun u hu => le_iSup_of_le u le_rfl)
  · apply iSup_le
    intro u
    exact le_iSup_of_le {u} (le_iSup_of_le u (le_iSup_of_le (by simp : u ∈ ({u} : Finset _)) le_rfl))

theorem finitePast_eq_comap (s : ℝ) (F : Finset (PastTime s)) :
    finitePast s F = MeasurableSpace.comap (fun ω (i : F) => proposalCount ω i.1.1) inferInstance := by
  apply le_antisymm
  · apply iSup₂_le
    intro u hu
    have hm : Measurable[MeasurableSpace.comap
        (fun ω (i : F) => proposalCount ω i.1.1) inferInstance]
        (fun ω (i : F) => proposalCount ω i.1.1) := comap_measurable _
    exact ((measurable_pi_apply ⟨u,hu⟩).comp hm).comap_le
  · letI : MeasurableSpace ClockSpace := finitePast s F
    have hm : Measurable (fun ω (i : F) => proposalCount ω i.1.1) := by
      apply measurable_pi_lambda
      intro u
      exact (comap_measurable (fun ω => proposalCount ω u.1.1)).mono
        (le_iSup_of_le u.1 (le_iSup_of_le u.property le_rfl)) le_rfl
    exact hm.comap_le

/-- A future increment is independent of the entire sigma-algebra generated by past counts.
The extension from finite observations uses a directed union, not pairwise independence. -/
theorem independent_past_increment (r : ℝ) (hr : 0 < r) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Indep (past s) (MeasurableSpace.comap (fun ω => increment ω s t) inferInstance)
      (waitingTimeLaw r hr) := by
  rw [← iSup_finitePast s]
  apply indep_iSup_of_directed_le
  · intro F
    rw [finitePast_eq_comap]
    exact independent_finite_past r hr s t hs ht F
  · exact finitePast_le s
  · exact (measurable_increment s t).comap_le
  · exact (finitePast_mono s).directed_le

/-- The standard natural filtration of the count process on nonnegative times. -/
def naturalFiltration : Filtration ℝ≥0 (inferInstance : MeasurableSpace ClockSpace) :=
  Filtration.natural (fun s : ℝ≥0 => fun ω => proposalCount ω s)
    (fun s => (measurable_proposalCount s).stronglyMeasurable)

theorem naturalFiltration_eq_past (s : ℝ≥0) : naturalFiltration s = past s := by
  unfold naturalFiltration Filtration.natural past
  apply le_antisymm
  · apply iSup₂_le
    intro u hu
    exact le_iSup_of_le ⟨u,u.property,hu⟩ le_rfl
  · apply iSup_le
    intro u
    exact le_iSup_of_le (⟨u.1,u.property.1⟩ : ℝ≥0) (le_iSup_of_le u.property.2 le_rfl)

/-- The next count increment is independent of the standard natural filtration. -/
theorem independent_natural_increment (r : ℝ) (hr : 0 < r) (s t : ℝ≥0) :
    Indep (naturalFiltration s)
      (MeasurableSpace.comap (fun ω => increment ω s t) inferInstance) (waitingTimeLaw r hr) := by
  rw [naturalFiltration_eq_past]
  exact independent_past_increment r hr s t s.property t.property

/-- Conditional expected increment given the entire past is its deterministic Poisson mean. -/
theorem conditional_increment (r : ℝ) (hr : 0 < r) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (waitingTimeLaw r hr)[fun ω => (increment ω s t : ℝ) | past s] =ᵐ[waitingTimeLaw r hr]
      fun _ => r*t := by
  have hf : StronglyMeasurable[MeasurableSpace.comap (fun ω => increment ω s t) inferInstance]
      (fun ω => (increment ω s t : ℝ)) :=
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (comap_measurable (fun ω => increment ω s t))).stronglyMeasurable
  have h := condExp_indep_eq (measurable_increment s t).comap_le (past_le s) hf
    (independent_past_increment r hr s t hs ht).symm
  simpa only [PoissonMoments.integral_increment r hr s t hs ht] using h

/-- Conditional expected increment, stated for mathlib's natural filtration. -/
theorem conditional_increment_natural (r : ℝ) (hr : 0 < r) (s t : ℝ≥0) :
    (waitingTimeLaw r hr)[fun ω => (increment ω s t : ℝ) | naturalFiltration s]
      =ᵐ[waitingTimeLaw r hr] fun _ => r*(t:ℝ) := by
  rw [naturalFiltration_eq_past]
  exact conditional_increment r hr s t s.property t.property

end CarryingCapacity.PoissonPastIndependence
