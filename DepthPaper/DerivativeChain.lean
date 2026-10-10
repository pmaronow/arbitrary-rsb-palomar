module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section


/-! Smoothness from a genuine chain of ordinary scalar derivatives on an open set. -/
noncomputable section
open Set
open scoped ContDiff
namespace DepthPaper

 theorem contDiffOn_of_derivative_chain {s:Set ℝ} (hs:IsOpen s) (G:ℕ→ℝ→ℝ)
     (hG:∀j,∀x∈s,HasDerivAt (G j) (G (j+1) x) x) (j:ℕ):
     ContDiffOn ℝ ∞ (G j) s:=by
   have hn:∀n:ℕ,∀j:ℕ,ContDiffOn ℝ n (G j) s:=by
     intro n
     induction n with
     | zero=>
       intro j
       change ContDiffOn ℝ 0 (G j) s
       rw [contDiffOn_zero]
       exact fun x hx=>(hG j x hx).continuousAt.continuousWithinAt
     | succ n ih=>
       intro j
       rw [show ((n+1:ℕ):ℕ∞ω)=(n:ℕ∞ω)+1 by simp,
         contDiffOn_succ_iff_deriv_of_isOpen hs]
       refine ⟨(fun x hx=>(hG j x hx).differentiableAt.differentiableWithinAt),?_,?_⟩
       · intro hnω
         simp at hnω
       · exact (ih (j+1)).congr (fun x hx=>(hG j x hx).deriv)
   exact contDiffOn_infty.mpr (fun n=>hn n j)

end DepthPaper
