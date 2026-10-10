module

public import GeneralDepthPaper.ColeHopfTerminal

@[expose] public section


/-! Actual finite Gaussian Cole–Hopf recursion in the complete terminal-data
space. Every finite depth is covered, with arbitrary real masses and positive
step variances, and the first-derivative norm is preserved. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
open ColeHopfFoundation.ProbabilityTheory

def coleHopfTerminal (p : ColeHopfParameter) : TerminalSpace := p.2+centeredColeHopfTerminal p

theorem terminalValue_coleHopfTerminal (p : ColeHopfParameter) (hv : 0<p.1.2) (x:ℝ) :
    terminalValue (coleHopfTerminal p) x=coleHopf p.1.1 p.1.2.toNNReal (terminalValue p.2) x := by
  rw [coleHopfTerminal,terminalValue_add,terminalValue_centeredColeHopfTerminal p hv]
  ring

theorem terminalJet_coleHopfTerminal (p : ColeHopfParameter) (hv : 0<p.1.2) :
    terminalJet (coleHopfTerminal p) 0=terminalGaussianJetOne p := by
  change terminalJet p.2 0+(centeredColeHopfTerminal p).1.2 0=_
  rw [centeredColeHopfTerminal_raw p hv]
  simp [centeredColeHopfJets]

theorem norm_terminalJet_coleHopfTerminal_le (p : ColeHopfParameter) (hv : 0<p.1.2) :
    ‖terminalJet (coleHopfTerminal p) 0‖≤‖terminalJet p.2 0‖ := by
  rw [terminalJet_coleHopfTerminal p hv]
  exact norm_terminalGaussianJetOne_le p hv

theorem contDiffAt_coleHopfTerminal (p : ColeHopfParameter) (hv : 0<p.1.2) :
    ContDiffAt ℝ ∞ coleHopfTerminal p :=
  contDiffAt_snd.add (contDiffAt_centeredColeHopfTerminal p hv)

abbrev ColeHopfRecursionParameter (L:ℕ) := (Fin L→ℝ×ℝ)×TerminalSpace

def coleHopfRecursion : (L:ℕ)→ColeHopfRecursionParameter L→TerminalSpace
  | 0,p=>p.2
  | L+1,p=>coleHopfTerminal (p.1 0,coleHopfRecursion L (fun i=>p.1 i.succ,p.2))

theorem contDiffAt_coleHopfRecursion (L:ℕ) (p:ColeHopfRecursionParameter L)
    (hv:∀i,0<(p.1 i).2) : ContDiffAt ℝ ∞ (coleHopfRecursion L) p := by
  induction L with
  | zero => exact contDiffAt_snd
  | succ L ih =>
    have htail : ContDiffAt ℝ ∞ (fun q:ColeHopfRecursionParameter (L+1)=>
        ((fun i:Fin L=>q.1 i.succ),q.2)) p := by fun_prop
    have hrec := (ih (fun i=>p.1 i.succ,p.2) (fun i=>hv i.succ)).comp p htail
    have hfirst : ContDiffAt ℝ ∞ (fun q:ColeHopfRecursionParameter (L+1)=>q.1 0) p := by fun_prop
    exact (contDiffAt_coleHopfTerminal (p.1 0,coleHopfRecursion L (fun i=>p.1 i.succ,p.2)) (hv 0)).comp
      p (hfirst.prodMk hrec)

theorem norm_terminalJet_coleHopfRecursion_le (L:ℕ) (p:ColeHopfRecursionParameter L)
    (hv:∀i,0<(p.1 i).2) : ‖terminalJet (coleHopfRecursion L p) 0‖≤‖terminalJet p.2 0‖ := by
  induction L with
  | zero => exact le_rfl
  | succ L ih =>
    exact (norm_terminalJet_coleHopfTerminal_le
      (p.1 0,coleHopfRecursion L (fun i=>p.1 i.succ,p.2)) (hv 0)).trans
      (ih (fun i=>p.1 i.succ,p.2) (fun i=>hv i.succ))

end GeneralDepthPaper
