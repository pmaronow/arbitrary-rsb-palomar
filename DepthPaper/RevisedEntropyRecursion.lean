module

public import DepthPaper.RevisedEntropyDiffusion
public import DepthPaper.RevisedEntropyBounds
public import FRSB.ConstantMassBackwardKernel

@[expose] public section

/-! The terminal derivative of the actual finite Cole–Hopf recursion, as a
Banach derivative, and its exact normalized transition-kernel interpretation.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ContDiff

namespace DepthPaper
open ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

def revisedColeHopfRecursionDerivative (L : ℕ) (d : Fin L → ℝ × ℝ)
    (g k : TerminalSpace) : TerminalSpace :=
  fderiv ℝ (fun h : TerminalSpace => coleHopfRecursion L (d, h)) g k

theorem revisedColeHopfRecursionDerivative_zero (g k : TerminalSpace) :
    revisedColeHopfRecursionDerivative 0 Fin.elim0 g k = k := by
  simp only [revisedColeHopfRecursionDerivative, coleHopfRecursion, fderiv_fun_id,
    ContinuousLinearMap.id_apply]

theorem revisedColeHopfRecursionDerivative_succ
    (L : ℕ) (d : Fin (L + 1) → ℝ × ℝ) (hv : ∀ i, 0 < (d i).2)
    (g k : TerminalSpace) :
    revisedColeHopfRecursionDerivative (L + 1) d g k =
      revisedColeHopfTerminalDerivative (d 0).1 (d 0).2
        (coleHopfRecursion L (fun i => d i.succ, g))
        (revisedColeHopfRecursionDerivative L (fun i => d i.succ) g k) := by
  let F : TerminalSpace → TerminalSpace := fun h => coleHopfRecursion L (fun i => d i.succ, h)
  let G : TerminalSpace → TerminalSpace := fun h => coleHopfTerminal (d 0, h)
  have hF : DifferentiableAt ℝ F g := by
    exact ((contDiffAt_coleHopfRecursion L (fun i => d i.succ, g)
      (fun i => hv i.succ)).comp g (by fun_prop)).differentiableAt (by simp)
  have hG : DifferentiableAt ℝ G (F g) := by
    exact ((contDiffAt_coleHopfTerminal (d 0, F g) (hv 0)).comp (F g)
      (by fun_prop)).differentiableAt (by simp)
  change fderiv ℝ (G ∘ F) g k = _
  rw [fderiv_comp g hG hF]
  rfl

theorem terminalValue_revisedColeHopfTerminalDerivative_kernel
    (a V : ℝ) (hV : 0 < V) (g k : TerminalSpace) (x : ℝ) :
    terminalValue (revisedColeHopfTerminalDerivative a V g k) x =
      ∫ y, terminalValue k y ∂FRSB.constantMassKernel a V.toNNReal (terminalValue g) x := by
  rw [terminalValue_revisedColeHopfTerminalDerivative a V hV g k x]
  have he := FRSB.backwardHeatQuotient_exp_eq_kernel_integral a V.toNNReal
    (terminalValue g) (contDiff_terminalValue g).continuous
    (hasLinearGrowth_terminalValue g) (terminalValue k)
    (contDiff_terminalValue k).continuous.measurable x
  rw [FRSB.backwardHeatQuotient, FRSB.gaussianHeatFlow, FRSB.gaussianHeatFlow,
    Real.toNNReal_coe] at he
  rw [← he]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun z => mul_comm _ _

theorem norm_revisedColeHopfTerminalDerivative_value_le
    (a V : ℝ) (hV : 0 < V) (g k : TerminalSpace) (C : ℝ)
    (hk : ∀ x, ‖terminalValue k x‖ ≤ C) (x : ℝ) :
    ‖terminalValue (revisedColeHopfTerminalDerivative a V g k) x‖ ≤ C := by
  rw [terminalValue_revisedColeHopfTerminalDerivative_kernel a V hV g k x]
  exact FRSB.norm_integral_constantMassKernel_le a V.toNNReal (terminalValue g)
    (contDiff_terminalValue g).continuous (hasLinearGrowth_terminalValue g) x
    (terminalValue k) C hk

theorem norm_revisedColeHopfRecursionDerivative_value_le
    (L : ℕ) (d : Fin L → ℝ × ℝ) (hv : ∀ i, 0 < (d i).2)
    (g k : TerminalSpace) (C : ℝ) (hk : ∀ x, ‖terminalValue k x‖ ≤ C) (x : ℝ) :
    ‖terminalValue (revisedColeHopfRecursionDerivative L d g k) x‖ ≤ C := by
  induction L generalizing g k x with
  | zero =>
    have hd : d = Fin.elim0 := by funext i; exact Fin.elim0 i
    subst d
    rw [revisedColeHopfRecursionDerivative_zero]
    exact hk x
  | succ L ih =>
    rw [revisedColeHopfRecursionDerivative_succ L d hv g k]
    exact norm_revisedColeHopfTerminalDerivative_value_le (d 0).1 (d 0).2 (hv 0)
      (coleHopfRecursion L (fun i => d i.succ, g))
      (revisedColeHopfRecursionDerivative L (fun i => d i.succ) g k) C
      (fun y => ih (fun i => d i.succ) (fun i => hv i.succ) g k hk y) x

end DepthPaper
