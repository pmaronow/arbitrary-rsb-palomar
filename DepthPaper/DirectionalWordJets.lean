module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap

@[expose] public section


/-! Ordered genuine directional derivatives on arbitrary real Banach
spaces. This identifies coordinate partials with evaluations of the total
Fréchet derivative without adding a mixed-partial commutation premise. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 700000

def directionalWordJet {E F I:Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (dirs:I→E) (f:E→F) : List I→E→F
  | [],p=>f p
  | i::w,p=>fderiv ℝ (directionalWordJet dirs f w) p (dirs i)

theorem contDiffOn_directionalWordJet {E F I:Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (dirs:I→E) {f:E→F} {U:Set E} (hU:IsOpen U)
    (hf:ContDiffOn ℝ ∞ f U) (w:List I) :
    ContDiffOn ℝ ∞ (directionalWordJet dirs f w) U := by
  induction w with
  | nil=>exact hf
  | cons i w ih=>
    exact (ih.fderiv_of_isOpen hU (by simp : (∞:ℕ∞ω)+1≤∞)).clm_apply contDiffOn_const

theorem iteratedFDeriv_dirs_eq_directionalWordJet {E F I:Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (dirs:I→E) {f:E→F} {U:Set E} (hU:IsOpen U)
    (hf:ContDiffOn ℝ ∞ f U) (n:ℕ) (v:Fin n→I) {p:E} (hp:p∈U) :
    iteratedFDeriv ℝ n f p (fun i=>dirs (v i))=
      directionalWordJet dirs f (List.ofFn v) p := by
  induction n generalizing p with
  | zero=>simp [directionalWordJet,iteratedFDeriv_zero_apply]
  | succ n ih=>
    have hd:=(hf p hp).contDiffAt (hU.mem_nhds hp)
      |>.differentiableAt_iteratedFDeriv
        (by exact_mod_cast ENat.natCast_lt_top n : (n:ℕ∞ω)<∞)
    rw [hd.iteratedFDeriv_succ_apply_left',List.ofFn_succ,directionalWordJet]
    have he:(fun q=>iteratedFDeriv ℝ n f q (fun i=>dirs (v i.succ)))
        =ᶠ[𝓝 p]directionalWordJet dirs f (List.ofFn (fun i=>v i.succ)) := by
      filter_upwards [hU.mem_nhds hp] with q hq
      exact ih (fun i=>v i.succ) hq
    change (fderiv ℝ (fun q=>iteratedFDeriv ℝ n f q
      (fun i=>dirs (v i.succ))) p) (dirs (v 0))=_
    rw [he.fderiv_eq]

def cutoffAxis (i:Fin 3) : ℝ×(ℝ×ℝ) :=
  if i=0 then (1,(0,0)) else if i=1 then (0,(1,0)) else (0,(0,1))

theorem norm_cutoffAxis (i:Fin 3) : ‖cutoffAxis i‖=1 := by
  fin_cases i <;> norm_num [cutoffAxis,Prod.norm_def]

end DepthPaper
