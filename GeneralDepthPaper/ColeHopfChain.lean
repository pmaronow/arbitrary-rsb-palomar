module

public import GeneralDepthPaper.ColeHopfRecursion

@[expose] public section


/-! Identification of an actual chain of Gaussian Cole–Hopf evolutions with
the literal finite recursion in TerminalSpace. -/
noncomputable section
open scoped Topology BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
open ColeHopfFoundation.ProbabilityTheory

theorem coleHopf_chain_eq_recursion (L:ℕ) (d:Fin L→ℝ×ℝ) (g:TerminalSpace)
    (u:Fin (L+1)→ℝ→ℝ) (hv:∀i,0<(d i).2)
    (hterminal:∀x,u (Fin.last L) x=terminalValue g x)
    (hstep:∀(i:Fin L)(x:ℝ),u i.castSucc x=
      coleHopf (d i).1 (d i).2.toNNReal (u i.succ) x) (x:ℝ) :
    u 0 x=terminalValue (coleHopfRecursion L (d,g)) x := by
  induction L generalizing g x with
  | zero => exact hterminal x
  | succ L ih =>
    have ht : ∀y,u (0:Fin (L+1)).succ y=
        terminalValue (coleHopfRecursion L (fun i=>d i.succ,g)) y := by
      intro y
      apply ih (fun i=>d i.succ) g (fun i:Fin (L+1)=>u i.succ) (fun i=>hv i.succ)
      · simpa only [Fin.succ_last] using hterminal
      · intro i z
        simpa only [Fin.succ_castSucc] using hstep i.succ z
    have H := hstep 0 x
    simp only [Fin.castSucc_zero] at H
    rw [show u (0:Fin (L+1)).succ=(fun y=>terminalValue (coleHopfRecursion L (fun i=>d i.succ,g)) y)
      from funext ht] at H
    rw [coleHopfRecursion,terminalValue_coleHopfTerminal _ (hv 0)]
    exact H

end GeneralDepthPaper
