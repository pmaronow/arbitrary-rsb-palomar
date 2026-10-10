module

public import DepthPaper.ColeHopfBoundaryContinuity
public import DepthPaper.ColeHopfRecursion

@[expose] public section


/-! Every finite recursion is continuous in the actual terminal Banach norm
on closed variance ranges, including zero-variance partial steps. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace DepthPaper
set_option maxSynthPendingDepth 64

theorem continuous_coleHopfTerminal : Continuous coleHopfTerminal :=
  continuous_snd.add continuous_centeredColeHopfTerminal

@[simp] theorem coleHopfTerminal_zero_variance (a : ℝ) (g : TerminalSpace) :
    coleHopfTerminal ((a,0),g) = g := by
  simp [coleHopfTerminal,centeredColeHopfTerminal]

theorem terminalValue_coleHopfTerminal_nonneg (p : ColeHopfParameter)
    (hv : 0 ≤ p.1.2) (x : ℝ) : terminalValue (coleHopfTerminal p) x =
      ColeHopfFoundation.ProbabilityTheory.coleHopf p.1.1 p.1.2.toNNReal (terminalValue p.2) x := by
  rw [coleHopfTerminal,terminalValue_add,terminalValue_centeredColeHopfTerminal_nonneg p hv]
  ring

theorem norm_terminalJet_coleHopfTerminal_nonneg (p : ColeHopfParameter) (hv : 0 ≤ p.1.2) :
    ‖terminalJet (coleHopfTerminal p) 0‖ ≤ ‖terminalJet p.2 0‖ := by
  rcases eq_or_lt_of_le hv with he | hp
  · have h0 : p = ((p.1.1,0),p.2) := by ext <;> simp_all
    rw [h0,coleHopfTerminal_zero_variance]
  · exact norm_terminalJet_coleHopfTerminal_le p hp

theorem continuous_coleHopfRecursion (L : ℕ) : Continuous (coleHopfRecursion L) := by
  induction L with
  | zero => exact continuous_snd
  | succ L ih =>
    have htail : Continuous (fun q : ColeHopfRecursionParameter (L+1) =>
        ((fun i : Fin L => q.1 i.succ),q.2)) := by fun_prop
    have hfirst : Continuous (fun q : ColeHopfRecursionParameter (L+1) => q.1 0) := by fun_prop
    exact continuous_coleHopfTerminal.comp (hfirst.prodMk (ih.comp htail))

theorem norm_terminalJet_coleHopfRecursion_nonneg (L : ℕ) (p : ColeHopfRecursionParameter L)
    (hv : ∀i,0 ≤ (p.1 i).2) :
    ‖terminalJet (coleHopfRecursion L p) 0‖ ≤ ‖terminalJet p.2 0‖ := by
  induction L with
  | zero => exact le_rfl
  | succ L ih =>
    exact (norm_terminalJet_coleHopfTerminal_nonneg
      (p.1 0,coleHopfRecursion L (fun i => p.1 i.succ,p.2)) (hv 0)).trans
      (ih (fun i => p.1 i.succ,p.2) (fun i => hv i.succ))

end DepthPaper
