import CarryingCapacity.TransportMetric

/-!
# Completeness of the adapted transport space

The limit construction proceeds through simultaneous couplings of successive
laws. Ionescu–Tulcea gives a path law; summable transport costs make its paths
eventually constant almost surely and control the terminal moment. The final
`momentLawCompleteSpace` instance proves completeness of the actual transport
metric. No limit law or completeness statement is supplied as an assumption.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Topology

namespace CarryingCapacity
variable {D : ℕ} {κ : MomentScale}

/-- Near-optimal plans exist directly from the actual infimum definition. -/
theorem exists_coupling_cost_lt (μ ν : MomentLaw κ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : Coupling μ ν, c.cost < wasserstein μ ν + ε := by
  have h : sInf (Set.range (fun c : Coupling μ ν => c.cost)) < wasserstein μ ν + ε := by
    change wasserstein μ ν < wasserstein μ ν + ε
    linarith
  rcases (csInf_lt_iff (couplingCosts_bddBelow μ ν) (Set.range_nonempty _)).mp h with
    ⟨r, ⟨c, rfl⟩, hc⟩
  exact ⟨c, hc⟩

/-- A path with summable adapted increments is eventually constant, since
unequal integer states are separated by at least one. -/
theorem eventually_constant_of_summable_adapted_steps (x : ℕ → State D)
    (hs : Summable (fun n => adaptedDistance κ (x n) (x (n + 1)))) :
    ∃ z : State D, ∀ᶠ n in atTop, x n = z := by
  have he := hs.tendsto_atTop_zero
  have hev : ∀ᶠ n in atTop, adaptedDistance κ (x n) (x (n + 1)) < 1 :=
    he.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hstep (n : ℕ) (hn : N ≤ n) : x n = x (n + 1) := by
    by_contra h
    exact (not_lt_of_ge (one_le_adaptedDistance_of_ne _ _ h)) (hN n hn)
  refine ⟨x N, eventually_atTop.mpr ⟨N, ?_⟩⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih => exact (hstep n hn).symm.trans ih

/-- Summable expectations of nonnegative functions give an integrable total
and almost sure pointwise summability. -/
theorem integrable_tsum_and_ae_summable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (F n)) (hn : ∀ n x, 0 ≤ F n x)
    (hi : ∀ n, Integrable (F n) P) (hs : Summable (fun n => ∫ x, F n x ∂P)) :
    Integrable (fun x => ∑' n, F n x) P ∧ ∀ᵐ x ∂P, Summable (fun n => F n x) := by
  have hm' : Measurable (fun x => ∑' n, ENNReal.ofReal (F n x)) :=
    Measurable.ennreal_tsum (fun n => (hm n).ennreal_ofReal)
  have hf : (∫⁻ x, ∑' n, ENNReal.ofReal (F n x) ∂P) ≠ ⊤ := by
    rw [lintegral_tsum (fun n => (hm n).ennreal_ofReal.aemeasurable)]
    simp_rw [← ofReal_integral_eq_lintegral_ofReal (hi _) (Eventually.of_forall (hn _))]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (hn n)) hs]
    exact ENNReal.ofReal_ne_top
  constructor
  · have hh := integrable_toReal_of_lintegral_ne_top hm'.aemeasurable hf
    simpa only [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top),
      ENNReal.toReal_ofReal (hn _ _)] using hh
  · filter_upwards [ae_lt_top' hm'.aemeasurable hf] with x hx
    have hh := ENNReal.summable_toReal hx.ne
    simpa only [ENNReal.toReal_ofReal (hn _ _)] using hh

namespace CouplingChain

abbrev History (D n : ℕ) := Finset.Iic n → State D

def last (n : ℕ) (h : History D n) : State D := h ⟨n, Finset.mem_Iic.mpr le_rfl⟩

def lastPair (n : ℕ) (h : History D (n + 1)) : State D × State D :=
  (h ⟨n, Finset.mem_Iic.mpr (Nat.le_succ n)⟩, last (n + 1) h)

/-- The transition law is the conditional kernel of the chosen coupling. -/
def step (u : ℕ → MomentLaw κ D) (c : ∀ n, Coupling (u n) (u (n + 1))) (n : ℕ) :
    Kernel (History D n) (State D) :=
  (c n).measure.condKernel.comap
    (last n) (measurable_of_countable _)

instance step_markov (u : ℕ → MomentLaw κ D)
    (c : ∀ n, Coupling (u n) (u (n + 1))) (n : ℕ) : IsMarkovKernel (step u c n) := by
  unfold step
  infer_instance

/-- At time zero a one-entry history has the first law of the sequence. -/
def initial (u : ℕ → MomentLaw κ D) : Measure (History D 0) :=
  Measure.map (fun x : State D => fun _ : Finset.Iic 0 => x) (u 0).measure

instance initial_probability (u : ℕ → MomentLaw κ D) : IsProbabilityMeasure (initial u) := by
  letI : IsProbabilityMeasure (u 0).measure := (u 0).probability
  exact isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

/-- A genuine infinite joint law, constructed by Ionescu–Tulcea. -/
def pathMeasure (u : ℕ → MomentLaw κ D) (c : ∀ n, Coupling (u n) (u (n + 1))) :
    Measure (ℕ → State D) := Kernel.traj (X := fun _ : ℕ => State D) (step u c) 0 ∘ₘ initial u

instance pathMeasure_probability (u : ℕ → MomentLaw κ D)
    (c : ∀ n, Coupling (u n) (u (n + 1))) : IsProbabilityMeasure (pathMeasure u c) := by
  unfold pathMeasure
  infer_instance

/-- The finite-history laws of the simultaneous coupling. -/
def prefixMeasure (u : ℕ → MomentLaw κ D) (c : ∀ n, Coupling (u n) (u (n + 1)))
    (n : ℕ) : Measure (History D n) := Kernel.partialTraj (X := fun _ : ℕ => State D) (step u c) 0 n ∘ₘ initial u

instance prefixMeasure_probability (u : ℕ → MomentLaw κ D)
    (c : ∀ n, Coupling (u n) (u (n + 1))) (n : ℕ) :
    IsProbabilityMeasure (prefixMeasure u c n) := by
  unfold prefixMeasure
  infer_instance

/-- Projection of the actual infinite law agrees with finite kernel iteration. -/
theorem pathMeasure_prefix (u : ℕ → MomentLaw κ D)
    (c : ∀ n, Coupling (u n) (u (n + 1))) (n : ℕ) :
    Measure.map (frestrictLe n) (pathMeasure u c) = prefixMeasure u c n := by
  rw [pathMeasure, Measure.map_comp _ _ (measurable_frestrictLe n),
    Kernel.traj_map_frestrictLe]
  rfl

/-- Projecting a one-step history extension gives its previous and new states. -/
theorem partialTraj_pair (u : ℕ → MomentLaw κ D)
    (c : ∀ n, Coupling (u n) (u (n + 1))) (n : ℕ) :
    (Kernel.partialTraj (X := fun _ : ℕ => State D) (step u c) n (n + 1)).map
      (lastPair n) = (Kernel.deterministic (last n) (measurable_of_countable _)) ×ₖ step u c n := by
  rw [Kernel.partialTraj_succ_self, ← Kernel.map_comp_right _
    (measurable_of_countable (IicProdIoc (X := fun _ : ℕ => State D) n (n + 1)))
    (measurable_of_countable (lastPair (D := D) n))]
  have he : lastPair n ∘ IicProdIoc (X := fun _ : ℕ => State D) n (n + 1) =
      Prod.map (last n) (MeasurableEquiv.piSingleton (X := fun _ : ℕ => State D) n).symm := by
    funext p
    apply Prod.ext <;> simp [lastPair, last, IicProdIoc, MeasurableEquiv.piSingleton]
  rw [he, ← Kernel.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _),
    Kernel.id_map (measurable_of_countable _), ← Kernel.map_comp_right _
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ => State D) n).measurable
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ => State D) n).symm.measurable]
  simp

private theorem map_source_compProd (n : ℕ) (M : Measure (History D n)) [SFinite M]
    (k : Kernel (State D) (State D)) [IsMarkovKernel k] :
    Measure.map (Prod.map (last n) id) (M ⊗ₘ k.comap (last n) (measurable_of_countable _)) =
      (Measure.map (last n) M) ⊗ₘ k := by
  ext s hs
  rw [Measure.map_apply (measurable_of_countable _) hs,
    Measure.compProd_apply ((measurable_of_countable _) hs), Measure.compProd_apply hs,
    lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

/-- The pair at the end of an iterated history has the prescribed conditional
law, with its previous-state marginal as input. -/
theorem prefix_pair (u : ℕ → MomentLaw κ D)
    (c : ∀ n, Coupling (u n) (u (n + 1))) (n : ℕ) :
    Measure.map (lastPair n) (prefixMeasure u c (n + 1)) =
      (Measure.map (last n) (prefixMeasure u c n)) ⊗ₘ (c n).measure.condKernel := by
  have hp : prefixMeasure u c (n + 1) =
      Kernel.partialTraj (X := fun _ : ℕ => State D) (step u c) n (n + 1) ∘ₘ
        prefixMeasure u c n := by
    rw [prefixMeasure, Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), ← Measure.comp_assoc]
    rfl
  rw [hp, Measure.map_comp _ _ (measurable_of_countable _), partialTraj_pair,
    ← map_source_compProd]
  change (_ ×ₖ step u c n) ∘ₘ prefixMeasure u c n =
    Measure.map (Prod.map (last n) id) ((prefixMeasure u c n) ⊗ₘ step u c n)
  rw [Measure.compProd_eq_comp_prod, Measure.map_comp _ _ (measurable_of_countable _),
    ← Kernel.map_prod_map _ _ (measurable_of_countable _) measurable_id,
    Kernel.id_map (measurable_of_countable _), Kernel.map_id]

/-- Every finite history has the prescribed law at its last coordinate. -/
theorem prefix_last (u : ℕ → MomentLaw κ D)
    (c : ∀ n, Coupling (u n) (u (n + 1))) (n : ℕ) :
    Measure.map (last n) (prefixMeasure u c n) = (u n).measure := by
  induction n with
  | zero =>
    simp only [prefixMeasure, Kernel.partialTraj_self, Measure.id_comp]
    rw [initial, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    exact Measure.map_id
  | succ n ih =>
    have hd : (u n).measure ⊗ₘ (c n).measure.condKernel = (c n).measure := by
      have hh := (c n).measure.disintegrate (c n).measure.condKernel
      change (Measure.map Prod.fst (c n).measure) ⊗ₘ _ = _ at hh
      rwa [(c n).first_marginal] at hh
    have hh := congrArg (Measure.map Prod.snd) (prefix_pair u c n)
    rw [Measure.map_map measurable_snd (measurable_of_countable _), ih, hd] at hh
    exact hh.trans (c n).second_marginal

/-- Every coordinate of the infinite simultaneous coupling has the right law. -/
theorem pathMeasure_coordinate (u : ℕ → MomentLaw κ D)
    (c : ∀ n, Coupling (u n) (u (n + 1))) (n : ℕ) :
    Measure.map (fun x : ℕ → State D => x n) (pathMeasure u c) = (u n).measure := by
  have hh := congrArg (Measure.map (last n)) (pathMeasure_prefix u c n)
  rw [Measure.map_map (measurable_of_countable (last (D := D) n))
    (measurable_frestrictLe (X := fun _ : ℕ => State D) n), prefix_last] at hh
  exact hh

/-- Consecutive coordinates realize exactly the selected transport plans. -/
theorem pathMeasure_pair (u : ℕ → MomentLaw κ D)
    (c : ∀ n, Coupling (u n) (u (n + 1))) (n : ℕ) :
    Measure.map (fun x : ℕ → State D => (x n, x (n + 1))) (pathMeasure u c) = (c n).measure := by
  have hh := congrArg (Measure.map (lastPair n)) (pathMeasure_prefix u c (n + 1))
  rw [Measure.map_map (measurable_of_countable (lastPair (D := D) n))
    (measurable_frestrictLe (X := fun _ : ℕ => State D) (n + 1)),
    prefix_pair, prefix_last] at hh
  have hd := (c n).measure.disintegrate (c n).measure.condKernel
  change (Measure.map Prod.fst (c n).measure) ⊗ₘ _ = _ at hd
  rw [(c n).first_marginal] at hd
  exact hh.trans hd

/-- The distance traversed at one step of the simultaneous coupling. -/
def jumpDistance (n : ℕ) (x : ℕ → State D) : ℝ := adaptedDistance κ (x n) (x (n + 1))

theorem measurable_jumpDistance (n : ℕ) : Measurable (jumpDistance (κ := κ) (D := D) n) := by
  have hp : Measurable (fun x : ℕ → State D => (x n, x (n + 1))) :=
    (measurable_pi_apply n).prodMk (measurable_pi_apply (n + 1))
  exact (measurable_of_countable (fun p : State D × State D =>
    adaptedDistance κ p.1 p.2)).comp hp

theorem integrable_jumpDistance (u : ℕ → MomentLaw κ D)
    (c : ∀ n, Coupling (u n) (u (n + 1))) (n : ℕ) :
    Integrable (jumpDistance (κ := κ) n) (pathMeasure u c) := by
  have hh : Integrable (fun p : State D × State D => adaptedDistance κ p.1 p.2)
      (Measure.map (fun x : ℕ → State D => (x n,x (n + 1))) (pathMeasure u c)) := by
    rw [pathMeasure_pair]
    exact (c n).integrable_distance
  exact hh.comp_measurable ((measurable_pi_apply n).prodMk (measurable_pi_apply (n + 1)))

theorem integral_jumpDistance (u : ℕ → MomentLaw κ D)
    (c : ∀ n, Coupling (u n) (u (n + 1))) (n : ℕ) :
    (∫ x, jumpDistance (κ := κ) n x ∂pathMeasure u c) = (c n).cost := by
  have hp : Measurable (fun x : ℕ → State D => (x n,x (n + 1))) :=
    (measurable_pi_apply n).prodMk (measurable_pi_apply (n + 1))
  unfold jumpDistance
  rw [← integral_map_of_stronglyMeasurable hp
    (measurable_of_countable (fun p : State D × State D => adaptedDistance κ p.1 p.2)).stronglyMeasurable,
    pathMeasure_pair]
  rfl

/-- The eventual state, with mathlib's fixed fallback on paths without a limit. -/
def limitState (x : ℕ → State D) : State D := limUnder atTop x

theorem measurable_limitState : Measurable (limitState (D := D)) :=
  (StronglyMeasurable.limUnder (l := atTop)
    (fun n : ℕ => (measurable_pi_apply n).stronglyMeasurable)).measurable

theorem eventually_eq_limitState (x : ℕ → State D)
    (hs : Summable (jumpDistance (κ := κ) · x)) :
    ∀ᶠ n in atTop, x n = limitState x := by
  obtain ⟨z, hz⟩ := eventually_constant_of_summable_adapted_steps x hs
  have ht : Tendsto x atTop (𝓝 z) := tendsto_const_nhds.congr' (hz.mono (fun _ h => h.symm))
  simpa [limitState, ht.limUnder_eq] using hz

/-- Tail path length bounds the distance to the eventual state. -/
theorem distance_limit_le_tail (x : ℕ → State D)
    (hs : Summable (jumpDistance (κ := κ) · x)) (n : ℕ) :
    adaptedDistance κ (x n) (limitState x) ≤ ∑' k, jumpDistance (κ := κ) (n + k) x := by
  have hfinite (m : ℕ) : adaptedDistance κ (x n) (x (n + m)) ≤
      ∑ k ∈ Finset.range m, jumpDistance (κ := κ) (n + k) x := by
    induction m with
    | zero => simp
    | succ m ih =>
      calc
        _ ≤ adaptedDistance κ (x n) (x (n + m)) +
            adaptedDistance κ (x (n + m)) (x (n + (m + 1))) :=
          adaptedDistance_triangle κ _ _ _
        _ ≤ (∑ k ∈ Finset.range m, jumpDistance (κ := κ) (n + k) x) +
            jumpDistance (κ := κ) (n + m) x := by
          simpa only [jumpDistance, Nat.add_assoc] using add_le_add_right ih
            (adaptedDistance κ (x (n + m)) (x (n + (m + 1))))
        _ = _ := (Finset.sum_range_succ _ _).symm
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_eq_limitState x hs)
  have hlim : x (n + N) = limitState x := hN _ (Nat.le_add_left N n)
  have hst : Summable (fun k => jumpDistance (κ := κ) (n + k) x) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff n).mpr hs
  calc
    _ = adaptedDistance κ (x n) (x (n + N)) := by rw [hlim]
    _ ≤ ∑ k ∈ Finset.range N, jumpDistance (κ := κ) (n + k) x := hfinite N
    _ ≤ _ := hst.sum_le_tsum _ (fun k _ => adaptedDistance_nonneg κ _ _)

/-- Summable transport-plan costs give summable jumps on almost every path. -/
theorem jumpDistance_summable_ae (u : ℕ → MomentLaw κ D)
    (c : ∀ n, Coupling (u n) (u (n + 1))) (hc : Summable (fun n => (c n).cost)) :
    ∀ᵐ x ∂pathMeasure u c, Summable (jumpDistance (κ := κ) · x) := by
  apply (integrable_tsum_and_ae_summable (pathMeasure u c) _ measurable_jumpDistance
    (fun n x => adaptedDistance_nonneg κ _ _) (integrable_jumpDistance u c) ?_).2
  simpa only [integral_jumpDistance] using hc

theorem integrable_jumpDistance_tsum (u : ℕ → MomentLaw κ D)
    (c : ∀ n, Coupling (u n) (u (n + 1))) (hc : Summable (fun n => (c n).cost)) :
    Integrable (fun x => ∑' n, jumpDistance (κ := κ) n x) (pathMeasure u c) := by
  apply (integrable_tsum_and_ae_summable (pathMeasure u c) _ measurable_jumpDistance
    (fun n x => adaptedDistance_nonneg κ _ _) (integrable_jumpDistance u c) ?_).1
  simpa only [integral_jumpDistance] using hc

/-- Finite initial moment plus integrable total path length controls the limit. -/
theorem integrable_limit_weight (u : ℕ → MomentLaw κ D)
    (c : ∀ n, Coupling (u n) (u (n + 1))) (hc : Summable (fun n => (c n).cost)) :
    Integrable (fun x => momentWeight κ (limitState x)) (pathMeasure u c) := by
  have hi₀ : Integrable (fun x : ℕ → State D => momentWeight κ (x 0)) (pathMeasure u c) := by
    have hh : Integrable (momentWeight κ)
        (Measure.map (fun x : ℕ → State D => x 0) (pathMeasure u c)) := by
      rw [pathMeasure_coordinate]
      exact (u 0).integrable_weight
    exact hh.comp_measurable (measurable_pi_apply 0)
  apply (hi₀.add (integrable_jumpDistance_tsum u c hc)).mono'
    ((measurable_of_countable (momentWeight κ)).comp measurable_limitState).aestronglyMeasurable
  filter_upwards [jumpDistance_summable_ae u c hc] with x hx
  change ‖momentWeight κ (limitState x)‖ ≤ momentWeight κ (x 0) + ∑' n, jumpDistance (κ := κ) n x
  rw [Real.norm_eq_abs, abs_of_nonneg (momentWeight_nonneg κ _)]
  have hd := distance_limit_le_tail x hx 0
  simp only [zero_add] at hd
  have hw := momentWeight_difference_le κ (limitState x) (x 0)
  rw [adaptedDistance_symm κ (limitState x) (x 0)] at hw
  have hh := le_abs_self (momentWeight κ (limitState x) - momentWeight κ (x 0))
  linarith

/-- The limit law is constructed by pushing the path law forward to its limit.
Its finite moment is proved, not postulated. -/
def limitLaw (u : ℕ → MomentLaw κ D) (c : ∀ n, Coupling (u n) (u (n + 1)))
    (hc : Summable (fun n => (c n).cost)) : MomentLaw κ D where
  measure := Measure.map limitState (pathMeasure u c)
  probability := isProbabilityMeasure_map measurable_limitState.aemeasurable
  integrable_weight := (integrable_map_measure
    (measurable_of_countable (momentWeight κ)).aestronglyMeasurable
    measurable_limitState.aemeasurable).mpr (integrable_limit_weight u c hc)

/-- Coordinate and terminal-state projections provide a coupling to the limit. -/
def limitCoupling (u : ℕ → MomentLaw κ D) (c : ∀ n, Coupling (u n) (u (n + 1)))
    (hc : Summable (fun n => (c n).cost)) (n : ℕ) : Coupling (u n) (limitLaw u c hc) where
  measure := Measure.map (fun x : ℕ → State D => (x n, limitState x)) (pathMeasure u c)
  first_marginal := by
    rw [Measure.map_map measurable_fst ((measurable_pi_apply n).prodMk measurable_limitState)]
    exact pathMeasure_coordinate u c n
  second_marginal := by
    rw [Measure.map_map measurable_snd ((measurable_pi_apply n).prodMk measurable_limitState)]
    rfl

/-- The selected coordinate-to-limit coupling has at most the remaining expected
path length as its cost. -/
theorem limitCoupling_cost_le (u : ℕ → MomentLaw κ D)
    (c : ∀ n, Coupling (u n) (u (n + 1))) (hc : Summable (fun n => (c n).cost)) (n : ℕ) :
    (limitCoupling u c hc n).cost ≤ ∑' k, (c (n + k)).cost := by
  have hp : Measurable (fun x : ℕ → State D => (x n, limitState x)) :=
    (measurable_pi_apply n).prodMk measurable_limitState
  have hi : Integrable (fun x : ℕ → State D => adaptedDistance κ (x n) (limitState x))
      (pathMeasure u c) := (limitCoupling u c hc n).integrable_distance.comp_measurable hp
  have hct : Summable (fun k => (c (n + k)).cost) := by
    exact ((summable_nat_add_iff n).mpr hc).congr (fun k => by rw [Nat.add_comm])
  have hsi : Summable (fun k => ∫ x, jumpDistance (κ := κ) (n + k) x ∂pathMeasure u c) := by
    simpa only [integral_jumpDistance] using hct
  have hit := (integrable_tsum_and_ae_summable (pathMeasure u c)
    (fun k x => jumpDistance (κ := κ) (n + k) x)
    (fun k => measurable_jumpDistance (n + k))
    (fun k x => adaptedDistance_nonneg κ _ _)
    (fun k => integrable_jumpDistance u c (n + k)) hsi).1
  have hnorm : Summable (fun k => ∫ x, ‖jumpDistance (κ := κ) (n + k) x‖ ∂pathMeasure u c) := by
    simpa only [jumpDistance, Real.norm_of_nonneg (adaptedDistance_nonneg κ _ _)] using hsi
  change (∫ p : State D × State D, adaptedDistance κ p.1 p.2
    ∂Measure.map (fun x : ℕ → State D => (x n, limitState x)) (pathMeasure u c)) ≤ _
  rw [integral_map_of_stronglyMeasurable hp
    (measurable_of_countable (fun p : State D × State D => adaptedDistance κ p.1 p.2)).stronglyMeasurable]
  calc
    _ ≤ ∫ x, ∑' k, jumpDistance (κ := κ) (n + k) x ∂pathMeasure u c := by
      apply integral_mono_ae hi hit
      filter_upwards [jumpDistance_summable_ae u c hc] with x hx
      exact distance_limit_le_tail x hx n
    _ = ∑' k, (c (n + k)).cost := by
      have hh := (integral_tsum_of_summable_integral_norm
        (fun k => integrable_jumpDistance u c (n + k)) hnorm).symm
      simpa only [integral_jumpDistance] using hh

/-- A summable-cost chain of actual couplings converges in the transport metric
to the constructed finite-moment law. -/
theorem tendsto_limitLaw (u : ℕ → MomentLaw κ D)
    (c : ∀ n, Coupling (u n) (u (n + 1))) (hc : Summable (fun n => (c n).cost)) :
    Tendsto u atTop (𝓝 (limitLaw u c hc)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun n => wasserstein_nonneg _ _)
    (fun n => (wasserstein_le_cost (limitCoupling u c hc n)).trans (limitCoupling_cost_le u c hc n))
  convert tendsto_sum_nat_add (fun n => (c n).cost) using 1
  ext n
  exact tsum_congr (fun k => by rw [Nat.add_comm])

end CouplingChain

/-- Completeness follows by constructing simultaneous near-optimal couplings
for a geometrically controlled sequence and taking its pathwise eventual limit. -/
instance momentLawCompleteSpace : CompleteSpace (MomentLaw κ D) := by
  apply Metric.complete_of_convergent_controlled_sequences (fun n => (1 / 2 : ℝ)^n)
    (fun _ => by positivity)
  intro u hu
  have hex : ∀ n, ∃ c : Coupling (u n) (u (n + 1)), c.cost < 2 * (1 / 2 : ℝ)^n := by
    intro n
    obtain ⟨c, hc⟩ := exists_coupling_cost_lt (u n) (u (n + 1)) ((1 / 2 : ℝ)^n) (by positivity)
    have hw := hu n n (n + 1) le_rfl (Nat.le_succ n)
    change wasserstein (u n) (u (n + 1)) < (1 / 2 : ℝ)^n at hw
    exact ⟨c, by linarith⟩
  choose c hc using hex
  have hsum : Summable (fun n => (c n).cost) := by
    apply Summable.of_nonneg_of_le (fun n => (c n).cost_nonneg) (fun n => (hc n).le)
    exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left 2
  exact ⟨CouplingChain.limitLaw u c hsum, CouplingChain.tendsto_limitLaw u c hsum⟩

end CarryingCapacity
