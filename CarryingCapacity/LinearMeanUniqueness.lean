import CarryingCapacity.LinearMeanLipschitz
import CarryingCapacity.LinearMeanEquation
import Mathlib.Analysis.ODE.Gronwall

/-!
# Global uniqueness of the nonnegative closed mean ODE

Continuity supplies bounds on each finite time interval. The actual vector
field is Lipschitz on the corresponding nonnegative box, and the ODE Gronwall
theorem gives uniqueness. No global Lipschitz or candidate moment bound is
assumed. The actual all-time nonlinear mean supplies global existence.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology NNReal

namespace CarryingCapacity.LinearMeanUniqueness
open LinearCarryingCapacity LinearMeanGenerator LinearMeanLipschitz

variable {D : ℕ} (c : Coefficients D)

/-- A solution on the nonnegative time axis, including its right derivative at zero. -/
def IsSolution (z₀ : Fin D → ℝ) (m : ℝ → Fin D → ℝ) : Prop :=
  ContinuousOn m (Ici 0) ∧ m 0 = z₀ ∧
    ∀ t, 0 ≤ t → ∀ i, 0 ≤ m t i ∧
      HasDerivWithinAt (fun s => m s i) (vectorField c (m t) i) (Ici 0) t

/-- Every continuous nonnegative trajectory has a common finite coordinate
bound on each compact time interval. This is derived, not a solution premise. -/
theorem exists_box {m : ℝ → Fin D → ℝ} {T : ℝ}
    (hm : ContinuousOn m (Icc 0 T)) (hn : ∀ t ∈ Icc 0 T, ∀ i, 0 ≤ m t i) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc 0 T, m t ∈ nonnegativeBox B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hm
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro t ht i
  refine ⟨hn t ht i, ?_⟩
  calc
    m t i ≤ |m t i| := le_abs_self _
    _ ≤ ‖m t‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (m t) i
    _ ≤ B := hB t ht
    _ ≤ max 0 B := le_max_right _ _

/-- Any two nonnegative solutions with the same initial vector agree at all
nonnegative times, regardless of their arbitrary values at negative times. -/
theorem solution_unique {z₀ : Fin D → ℝ} {f g : ℝ → Fin D → ℝ}
    (hf : IsSolution c z₀ f) (hg : IsSolution c z₀ g) : EqOn f g (Ici 0) := by
  intro T hT
  have hfcont := hf.1.mono (show Icc 0 T ⊆ Ici 0 from fun _ h => h.1)
  have hgcont := hg.1.mono (show Icc 0 T ⊆ Ici 0 from fun _ h => h.1)
  obtain ⟨Bf, hBf, hfb⟩ := exists_box hfcont (fun t ht i => (hf.2.2 t ht.1 i).1)
  obtain ⟨Bg, hBg, hgb⟩ := exists_box hgcont (fun t ht i => (hg.2.2 t ht.1 i).1)
  let B := max Bf Bg
  have hB : 0 ≤ B := hBf.trans (le_max_left _ _)
  obtain ⟨K, hK⟩ := exists_lipschitzOn_box c B hB
  have hfs : ∀ t ∈ Ico 0 T, f t ∈ nonnegativeBox B := by
    intro t ht i
    exact ⟨(hfb t ⟨ht.1, ht.2.le⟩ i).1,
      (hfb t ⟨ht.1, ht.2.le⟩ i).2.trans (le_max_left _ _)⟩
  have hgs : ∀ t ∈ Ico 0 T, g t ∈ nonnegativeBox B := by
    intro t ht i
    exact ⟨(hgb t ⟨ht.1, ht.2.le⟩ i).1,
      (hgb t ⟨ht.1, ht.2.le⟩ i).2.trans (le_max_right _ _)⟩
  have hfd : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt f (vectorField c (f t)) (Ici t) t := by
    intro t ht
    exact hasDerivWithinAt_pi.mpr (fun i =>
      ((hf.2.2 t ht.1 i).2).mono (Ici_subset_Ici.mpr ht.1))
  have hgd : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt g (vectorField c (g t)) (Ici t) t := by
    intro t ht
    exact hasDerivWithinAt_pi.mpr (fun i =>
      ((hg.2.2 t ht.1 i).2).mono (Ici_subset_Ici.mpr ht.1))
  exact ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => vectorField c) (s := fun _ => nonnegativeBox B)
    (fun _ _ => hK) hfcont hfd hfs hgcont hgd hgs (hf.2.1.trans hg.2.1.symm)
    ⟨hT, le_rfl⟩

variable (r : ℝ) (hr : 1 < r) (ν : MomentLaw MomentScale.linear D)
  (hMoment : Integrable (fun x : State D => 1 + populationSize x ^ r) ν.measure)

/-- The actual nonlinear law's mean is a global solution of the exact model ODE. -/
theorem mean_isSolution : IsSolution c (CoordinateMoments.vector ν)
    (LinearMeanEquation.mean c r hr ν hMoment) := by
  refine ⟨LinearMeanEquation.continuousOn_mean c r hr ν hMoment,
    LinearMeanEquation.mean_zero c r hr ν hMoment, ?_⟩
  intro t ht i
  exact ⟨LinearMeanEquation.mean_nonnegative c r hr ν hMoment t i,
    LinearMeanEquation.hasDerivWithinAt_mean c r hr ν hMoment i t ht⟩

include hr hMoment in
/-- Proposition 7.5's global existence and uniqueness, with uniqueness on the
actual nonnegative time domain and no extra boundedness assumption. -/
theorem exists_solution_unique_on_nonnegative :
    ∃ m : ℝ → Fin D → ℝ, IsSolution c (CoordinateMoments.vector ν) m ∧
      ∀ n, IsSolution c (CoordinateMoments.vector ν) n → EqOn n m (Ici 0) := by
  refine ⟨LinearMeanEquation.mean c r hr ν hMoment,
    mean_isSolution c r hr ν hMoment, ?_⟩
  intro n hn
  exact solution_unique c hn (mean_isSolution c r hr ν hMoment)

end CarryingCapacity.LinearMeanUniqueness
