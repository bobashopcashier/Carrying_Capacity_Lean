import CarryingCapacity.ParticleNoiseProjection
import CarryingCapacity.ExchangeableMatching
import CarryingCapacity.CommonInitialNoise

/-!
# Relabeling complete particle inputs

A permutation acts simultaneously on the entire paired initial array and on
every strip of each particle's marked noise. The noise law is invariant by
the actual infinite product construction. An exchangeable paired initial law
therefore makes this simultaneous transformation measure preserving on the
original initial/noise product space. All counting-measure identities are
pointwise, including samples outside the probability-one regularity events.
-/

noncomputable section
open MeasureTheory
open scoped Classical

namespace CarryingCapacity.ParticleRelabeling
open Symmetrization ExchangeableMatching

variable {N : ℕ} {J : Type*}

/-- A particle permutation leaves the jump direction unchanged. -/
def labelEquiv (e : Equiv.Perm (Fin N)) : Equiv.Perm (Fin N × J) :=
  Equiv.prodCongr e (Equiv.refl J)

@[simp] theorem labelEquiv_apply (e : Equiv.Perm (Fin N)) (j : Fin N × J) :
    labelEquiv e j = (e j.1, j.2) := rfl

/-- The relabeled particle `i` uses the complete original noise of particle
`e i`, with every jump label and vertical strip retained. -/
def noiseRelabel (e : Equiv.Perm (Fin N))
    (ω : MarkedNoise.Sample (Fin N × J)) : MarkedNoise.Sample (Fin N × J) :=
  fun p => ω (labelEquiv e p.1, p.2)

@[simp] theorem noiseRelabel_apply (e : Equiv.Perm (Fin N))
    (ω : MarkedNoise.Sample (Fin N × J)) (i : Fin N) (j : J) (n : ℕ) :
    noiseRelabel e ω ((i,j),n) = ω ((e i,j),n) := rfl

theorem measurable_noiseRelabel (e : Equiv.Perm (Fin N)) :
    Measurable (noiseRelabel (J := J) e) :=
  measurable_pi_lambda _ (fun p => measurable_pi_apply (labelEquiv e p.1, p.2))

/-- Invariance of the full infinite clock/mark product, not merely selected
count distributions or pairwise noise marginals. -/
theorem noiseRelabel_map (e : Equiv.Perm (Fin N)) :
    (MarkedNoise.law (Fin N × J)).map (noiseRelabel e) = MarkedNoise.law (Fin N × J) := by
  let indexEquiv : Equiv.Perm ((Fin N × J) × ℕ) :=
    Equiv.prodCongr (labelEquiv e) (Equiv.refl ℕ)
  have he : noiseRelabel (J := J) e =
      MeasurableEquiv.piCongrLeft (fun _ : (Fin N × J) × ℕ => MarkedNoise.StripSample)
        indexEquiv.symm := by
    funext ω p
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply,
      noiseRelabel, indexEquiv]
    rfl
  rw [he]
  exact Measure.infinitePi_map_piCongrLeft
    (μ := fun _ : (Fin N × J) × ℕ => MarkedNoise.stripLaw) indexEquiv.symm

/-- Actual noise relabeling is measure preserving. -/
theorem noiseRelabel_preserving (e : Equiv.Perm (Fin N)) :
    MeasurePreserving (noiseRelabel (J := J) e)
      (MarkedNoise.law (Fin N × J)) (MarkedNoise.law (Fin N × J)) :=
  ⟨measurable_noiseRelabel e, noiseRelabel_map e⟩

@[simp] theorem point_noiseRelabel (e : Equiv.Perm (Fin N)) (j : Fin N × J)
    (ω : MarkedNoise.Sample (Fin N × J)) (k : ℕ × ℕ) :
    MarkedNoise.point j (noiseRelabel e ω) k = MarkedNoise.point (labelEquiv e j) ω k := rfl

/-- The complete actual counting measure is relabeled exactly on every sample. -/
@[simp] theorem countingMeasure_noiseRelabel (e : Equiv.Perm (Fin N)) (j : Fin N × J)
    (ω : MarkedNoise.Sample (Fin N × J)) :
    MarkedNoise.countingMeasure j (noiseRelabel e ω) =
      MarkedNoise.countingMeasure (labelEquiv e j) ω := rfl

/-- Whole-particle projection commutes pointwise with relabeling. -/
@[simp] theorem project_noiseRelabel (e : Equiv.Perm (Fin N)) (i : Fin N)
    (ω : MarkedNoise.Sample (Fin N × J)) :
    ParticleNoiseProjection.project i (noiseRelabel e ω) =
      ParticleNoiseProjection.project (e i) ω := rfl

@[simp] theorem noiseRelabel_refl (ω : MarkedNoise.Sample (Fin N × J)) :
    noiseRelabel (Equiv.refl (Fin N)) ω = ω := rfl

theorem noiseRelabel_trans (e f : Equiv.Perm (Fin N))
    (ω : MarkedNoise.Sample (Fin N × J)) :
    noiseRelabel e (noiseRelabel f ω) = noiseRelabel (e.trans f) ω := rfl

section PairedRecord
variable {α β : Type*}

/-- Simultaneous relabeling retains the complete paired initial record and
acts on the complete original noise. -/
def sampleRelabel (e : Equiv.Perm (Fin N))
    (p : CommonInitialNoise.Sample (Fin N → α × β) (Fin N × J)) :
    CommonInitialNoise.Sample (Fin N → α × β) (Fin N × J) :=
  (relabel e p.1, noiseRelabel e p.2)

@[simp] theorem sampleRelabel_fst (e : Equiv.Perm (Fin N))
    (p : CommonInitialNoise.Sample (Fin N → α × β) (Fin N × J)) :
    (sampleRelabel e p).1 = relabel e p.1 := rfl

@[simp] theorem sampleRelabel_snd (e : Equiv.Perm (Fin N))
    (p : CommonInitialNoise.Sample (Fin N → α × β) (Fin N × J)) :
    (sampleRelabel e p).2 = noiseRelabel e p.2 := rfl

/-- The entire left initial array has the same permutation orientation as
the particle noise. -/
@[simp] theorem initialLeft_sampleRelabel (e : Equiv.Perm (Fin N))
    (p : CommonInitialNoise.Sample (Fin N → α × β) (Fin N × J)) :
    (fun i => ((sampleRelabel e p).1 i).1) = relabel e (fun i => (p.1 i).1) := rfl

/-- Both members of every initial pair use the same permutation. -/
@[simp] theorem initialRight_sampleRelabel (e : Equiv.Perm (Fin N))
    (p : CommonInitialNoise.Sample (Fin N → α × β) (Fin N × J)) :
    (fun i => ((sampleRelabel e p).1 i).2) = relabel e (fun i => (p.1 i).2) := rfl

@[simp] theorem sampleRelabel_refl
    (p : CommonInitialNoise.Sample (Fin N → α × β) (Fin N × J)) :
    sampleRelabel (Equiv.refl (Fin N)) p = p := rfl

theorem sampleRelabel_trans (e f : Equiv.Perm (Fin N))
    (p : CommonInitialNoise.Sample (Fin N → α × β) (Fin N × J)) :
    sampleRelabel e (sampleRelabel f p) = sampleRelabel (e.trans f) p := rfl

variable [MeasurableSpace α] [MeasurableSpace β]

theorem measurable_sampleRelabel (e : Equiv.Perm (Fin N)) :
    Measurable (sampleRelabel (α := α) (β := β) (J := J) e) :=
  ((measurable_relabel e).comp measurable_fst).prodMk
    ((measurable_noiseRelabel e).comp measurable_snd)

/-- Exchangeability of the full paired initial vector and the actual product
noise construction imply invariance of the complete input law. -/
theorem sampleRelabel_preserving (e : Equiv.Perm (Fin N))
    (γ : Measure (Fin N → α × β)) [IsProbabilityMeasure γ] (hγ : ExchangeableLaw γ) :
    MeasurePreserving (sampleRelabel (J := J) e)
      (CommonInitialNoise.law γ (Fin N × J)) (CommonInitialNoise.law γ (Fin N × J)) := by
  have hi : MeasurePreserving (relabel e) γ γ := ⟨measurable_relabel e, hγ e⟩
  exact hi.prod (noiseRelabel_preserving (J := J) e)

/-- Exact full-law pushforward for the initialized sample transformation. -/
theorem sampleRelabel_map (e : Equiv.Perm (Fin N))
    (γ : Measure (Fin N → α × β)) [IsProbabilityMeasure γ] (hγ : ExchangeableLaw γ) :
    (CommonInitialNoise.law γ (Fin N × J)).map (sampleRelabel e) =
      CommonInitialNoise.law γ (Fin N × J) :=
  (sampleRelabel_preserving (J := J) e γ hγ).map_eq

end PairedRecord
end CarryingCapacity.ParticleRelabeling
