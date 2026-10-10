module

public import GeneralDepthPaper.CutoffTerminalMassRegularity
public import GeneralDepthPaper.TerminalFixedDilation

@[expose] public section


/-! Actual Banach-space smoothness of ψ_m and χ_{m,V}. Fixed field
dilation transports the one-sided physical mass estimates to a genuine
open neighborhood of mass one. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal
namespace GeneralDepthPaper
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 64

theorem contDiffAt_scaledLogCoshTerminal {m : ℝ} (hm : m∈Ioo (0:ℝ) 2) :
    ContDiffAt ℝ ∞ scaledLogCoshTerminal m := by
  have hε : 0 < m/4 := by linarith [hm.1]
  have hε1 : m/4<1 := by linarith [hm.2]
  have hpoint : m/2∈Icc (m/4) 1 := by constructor <;> linarith [hm.1,hm.2]
  have hlocal := (contDiffOn_scaledLogCoshTerminal_closed_mass hε hε1 (m/2) hpoint).contDiffAt
    (Icc_mem_nhds (by linarith [hm.1] : m/4 < m/2) (by linarith [hm.2] : m/2 < 1))
  have harg : ContDiffAt ℝ ∞ (fun r:ℝ=>r/2) m := by fun_prop
  have hd := terminalDoubleFieldCLM.contDiff.contDiffAt.comp m (hlocal.comp m harg)
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hm] with r hr
  exact (terminalDoubleFieldCLM_scaledLogCosh r hr.1.ne').symm

def cutoffErrorTerminal (m V : ℝ) : TerminalSpace :=
  cutoffTerminal m V-scaledLogCoshTerminal m

theorem contDiffAt_cutoffErrorTerminal {m V : ℝ}
    (hm : m∈Ioo (0:ℝ) 2) (hV : 0<V) :
    ContDiffAt ℝ ∞ (fun p:ℝ×ℝ=>cutoffErrorTerminal p.1 p.2) (m,V) :=
  (contDiffAt_cutoffTerminal hm.1.ne' hV).sub
    ((contDiffAt_scaledLogCoshTerminal hm).comp (m,V) contDiffAt_fst)

end GeneralDepthPaper
