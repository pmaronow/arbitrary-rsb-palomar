module

public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Calculus.TangentCone.Real

@[expose] public section

/-! The manuscript's closed-domain finite C^k convention: genuine interior
derivatives admit continuous boundary jets. No ambient extension is assumed.
On the closure of an open convex domain this is equivalent to Mathlib's
relative C^k predicate. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper.RevisedClosedIFT
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 64
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

def ClosedInteriorCk : (k : ℕ) → {F : Type u} →
    [NormedAddCommGroup F] → [NormedSpace ℝ F] → (E→F) → Set E → Prop
  | 0, _, _, _, f, S => ContinuousOn f S
  | k+1, _, _, _, f, S => ContinuousOn f S ∧
      ∃A : E→(E→L[ℝ]_),ClosedInteriorCk k A S ∧
        ∀x∈interior S,HasFDerivAt f (A x) x

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem ClosedInteriorCk.continuousOn {k : ℕ} {f : E→F} {S : Set E}
    (hf : ClosedInteriorCk k f S) : ContinuousOn f S := by
  cases k with
  | zero => exact hf
  | succ k => exact hf.1

theorem closedInteriorCk_contDiffOn_closure {U : Set E}
    (hU : IsOpen U) (hc : Convex ℝ U) (hne : U.Nonempty) (k : ℕ) (f : E→F)
    (hf : ClosedInteriorCk k f (closure U)) : ContDiffOn ℝ k f (closure U) := by
  have hreg : interior (closure U)=U := by
    simpa only [hU.interior_eq] using hc.interior_closure_eq_interior_of_nonempty_interior
      (by simpa only [hU.interior_eq] using hne)
  have hu : UniqueDiffOn ℝ (closure U) := uniqueDiffOn_convex hc.closure
    (by rw [hreg];exact hne)
  induction k generalizing F with
  | zero => exact contDiffOn_zero.mpr hf
  | succ k ih =>
    obtain ⟨hcont,A,hA,hder⟩ := hf
    have hAc := hA.continuousOn
    have hAu := ih A hA
    have hdiff : DifferentiableOn ℝ f U := by
      intro x hx
      exact (hder x (hreg.symm ▸ hx)).differentiableAt.differentiableWithinAt
    have hall (x : E) (hx : x∈closure U) : HasFDerivWithinAt f (A x) (closure U) x := by
      apply hasFDerivWithinAt_closure_of_tendsto_fderiv hdiff hc hU
      · intro y hy
        exact (hcont y hy).mono subset_closure
      · have hlim : Tendsto A (𝓝[U] x) (𝓝 (A x)) := by
          exact (hAc x hx).mono subset_closure
        apply hlim.congr'
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact (hder y (hreg.symm ▸ hy)).fderiv.symm
    have hresult := (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n:=(k:ℕ∞ω)) hu).mpr
      ⟨by intro h;exact False.elim (by simpa using h),A,hAu,hall⟩
    simpa only [Nat.cast_add,Nat.cast_one] using hresult

theorem contDiffOn_closedInteriorCk {S : Set E} (hu : UniqueDiffOn ℝ S)
    (k : ℕ) (f : E→F) (hf : ContDiffOn ℝ k f S) : ClosedInteriorCk k f S := by
  induction k generalizing F with
  | zero => exact hf.continuousOn
  | succ k ih =>
    have hs := (contDiffOn_succ_iff_fderivWithin (n:=(k:ℕ∞ω)) hu).mp
      (by simpa only [Nat.cast_add,Nat.cast_one] using hf)
    refine ⟨hf.continuousOn,fderivWithin ℝ f S,ih _ hs.2.2,?_⟩
    intro x hx
    exact ((hs.1 x (interior_subset hx)).hasFDerivWithinAt).hasFDerivAt
      (mem_interior_iff_mem_nhds.mp hx)

theorem closedInteriorCk_iff_contDiffOn_closure {U : Set E}
    (hU : IsOpen U) (hc : Convex ℝ U) (hne : U.Nonempty) (k : ℕ) (f : E→F) :
    ClosedInteriorCk k f (closure U) ↔ ContDiffOn ℝ k f (closure U) := by
  have hu : UniqueDiffOn ℝ (closure U) := uniqueDiffOn_convex hc.closure
    (hne.mono (by intro x hx;exact interior_mono subset_closure (hU.interior_eq.symm ▸ hx)))
  exact ⟨closedInteriorCk_contDiffOn_closure hU hc hne k f,
    contDiffOn_closedInteriorCk hu k f⟩

end DepthPaper.RevisedClosedIFT
