module

public import DepthPaper.RevisedClosedIFTContinuity
public import DepthPaper.RevisedClosedIFTDerivative
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! Finite-order relative regularity of the unique implicit root. Boundary
derivatives are proved first; induction applies smooth inversion to the
actual implicit derivative, without invoking an extension theorem. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper.RevisedClosedIFT
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 64
universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem contDiffWithinAt_implicitDerivative {D : Set E} {θ : E}
    {L : E→(E×F→L[ℝ]F)} {k : ℕ∞ω}
    (hL : ContDiffWithinAt ℝ k L D θ) (hinv : (partialY (L θ)).IsInvertible) :
    ContDiffWithinAt ℝ k (fun u=>implicitDerivative (L u)) D θ := by
  have hA : ContDiffWithinAt ℝ k (fun u=>partialY (L u)) D θ :=
    hL.clm_comp contDiffWithinAt_const
  have hB : ContDiffWithinAt ℝ k (fun u=>partialX (L u)) D θ :=
    hL.clm_comp contDiffWithinAt_const
  have hAi := hinv.contDiffAt_map_inverse.comp_contDiffWithinAt θ hA
  exact hAi.neg.clm_comp hB

theorem contDiffOn_unique_implicit_root {D : Set E} {K : Set F} {Φ : E×F→F} {y : E→F}
    (hD : UniqueDiffOn ℝ D) (hDK : UniqueDiffOn ℝ (D×ˢK))
    (hK : IsCompact K) (k : ℕ) (hΦ : ContDiffOn ℝ k Φ (D×ˢK))
    (hyK : ∀θ∈D,y θ∈K) (hzero : ∀θ∈D,Φ (θ,y θ)=0)
    (hunique : ∀θ∈D,∀z∈K,Φ (θ,z)=0 → z=y θ)
    (hinv : ∀θ∈D,(partialY (fderivWithin ℝ Φ (D×ˢK) (θ,y θ))).IsInvertible) :
    ContDiffOn ℝ k y D := by
  have hcont : ContinuousOn y D := continuousOn_unique_zero hK hΦ.continuousOn hyK hzero hunique
  induction k with
  | zero => exact contDiffOn_zero.mpr hcont
  | succ k ih =>
    have hφsucc : ContDiffOn ℝ ((k : ℕ∞ω)+1) Φ (D×ˢK) := by
      simpa only [Nat.cast_add,Nat.cast_one] using hΦ
    have hφjet := (contDiffOn_succ_iff_fderivWithin hDK).mp hφsucc
    have hy : ContDiffOn ℝ k y D := ih (hΦ.of_le (by exact_mod_cast Nat.le_succ k))
    let L : E→(E×F→L[ℝ]F) := fun θ=>fderivWithin ℝ Φ (D×ˢK) (θ,y θ)
    have hL : ContDiffOn ℝ k L D := hφjet.2.2.comp (contDiffOn_id.prodMk hy)
      (fun θ hθ=>⟨hθ,hyK θ hθ⟩)
    have hjet : ContDiffOn ℝ k (fun θ=>implicitDerivative (L θ)) D :=
      fun θ hθ=>contDiffWithinAt_implicitDerivative (hL θ hθ) (hinv θ hθ)
    have hder (θ : E) (hθ : θ∈D) :
        HasFDerivWithinAt y (implicitDerivative (L θ)) D θ :=
      hasFDerivWithinAt_implicit_root hθ hyK (hcont θ hθ) hzero
        ((hφjet.1 (θ,y θ) ⟨hθ,hyK θ hθ⟩).hasFDerivWithinAt) (hinv θ hθ)
    have hresult := (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
      (n:=(k : ℕ∞ω)) hD).mpr
      ⟨by intro h;exact False.elim (by simpa using h),_,hjet,hder⟩
    simpa only [Nat.cast_add,Nat.cast_one] using hresult

end DepthPaper.RevisedClosedIFT
