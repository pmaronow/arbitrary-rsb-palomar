module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap

@[expose] public section


/-! Actual ordered coordinate derivatives on a two-dimensional parameter
space. Their identification with multilinear derivatives does not require
commuting partial derivatives or assuming a Schwarz theorem. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 64

def parameterAxis (i : Fin 2) : ℝ×ℝ := if i=0 then (1,0) else (0,1)

def coordinateWordJet {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ×ℝ→F) : List (Fin 2)→ℝ×ℝ→F
  | [],p=>f p
  | i::w,p=>fderiv ℝ (coordinateWordJet f w) p (parameterAxis i)

theorem contDiffOn_coordinateWordJet {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ×ℝ→F} {U : Set (ℝ×ℝ)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (w : List (Fin 2)) :
    ContDiffOn ℝ ∞ (coordinateWordJet f w) U := by
  induction w with
  | nil => exact hf
  | cons i w ih =>
    exact (ih.fderiv_of_isOpen hU (by simp : (∞:ℕ∞ω)+1≤∞)).clm_apply contDiffOn_const

theorem iteratedFDeriv_axes_eq_coordinateWordJet {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ×ℝ→F} {U : Set (ℝ×ℝ)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (n : ℕ) (v : Fin n→Fin 2)
    {p : ℝ×ℝ} (hp : p∈U) :
    iteratedFDeriv ℝ n f p (fun i=>parameterAxis (v i))=
      coordinateWordJet f (List.ofFn v) p := by
  induction n generalizing p with
  | zero => simp [coordinateWordJet,iteratedFDeriv_zero_apply]
  | succ n ih =>
    have hd:=(hf p hp).contDiffAt (hU.mem_nhds hp)
      |>.differentiableAt_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n : (n:ℕ∞ω)<∞)
    rw [hd.iteratedFDeriv_succ_apply_left']
    rw [List.ofFn_succ,coordinateWordJet]
    have he:(fun q=>iteratedFDeriv ℝ n f q (fun i=>parameterAxis (v i.succ)))
        =ᶠ[𝓝 p]coordinateWordJet f (List.ofFn (fun i=>v i.succ)) := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact ih (fun i=>v i.succ) hq
    change (fderiv ℝ (fun q=>iteratedFDeriv ℝ n f q
      (fun i=>parameterAxis (v i.succ))) p) (parameterAxis (v 0))=_
    rw [he.fderiv_eq]

end DepthPaper
