module

public import GeneralDepthPaper.TerminalJetParameterBounds
public import GeneralDepthPaper.TerminalBoundedLift
public import GeneralDepthPaper.ColeHopfRecursion

@[expose] public section


/-! Actual uniform all-order derivative bounds in the complete terminal-data
space, including the removable zero-mass branch. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64

theorem boundedSmoothOn_centeredColeHopfJets (A Vlo Vhi B : ℝ)
    (hA : 0≤A) (hVlo : 0<Vlo) (hV : Vlo≤Vhi) (hB : 0≤B) :
    BoundedSmoothOn centeredColeHopfJets (coleHopfBall A Vlo Vhi B) := by
  apply BoundedSmoothOn.pi
  intro i
  have hterm (j:Fin 3) :=
    (boundedSmoothOn_coleHopf_terminal A Vlo Vhi B hA hVlo).compCLM (terminalJetCLM j)
  fin_cases i
  · exact (boundedSmoothOn_terminalGaussianJetOne A Vlo Vhi B hA hVlo hV hB).sub (hterm 0)
  · exact (boundedSmoothOn_terminalGaussianJetTwo A Vlo Vhi B hA hVlo hV hB).sub (hterm 1)
  · exact (boundedSmoothOn_terminalGaussianJetThree A Vlo Vhi B hA hVlo hV hB).sub (hterm 2)

theorem boundedSmoothOn_centeredColeHopfTerminal (A Vlo Vhi B : ℝ)
    (hA : 0≤A) (hVlo : 0<Vlo) (hV : Vlo≤Vhi) (hB : 0≤B) :
    BoundedSmoothOn centeredColeHopfTerminal (coleHopfBall A Vlo Vhi B) := by
  have hv := (boundedSmoothOn_centeredColeHopfValue A Vlo Vhi B hA hVlo hV hB).compCLM
    (BoundedContinuousFunction.evalCLM ℝ (0:ℝ))
  have hraw := hv.prodMk (boundedSmoothOn_centeredColeHopfJets A Vlo Vhi B hA hVlo hV hB)
  have hambient : BoundedSmoothOn (fun p:ColeHopfParameter=>(centeredColeHopfTerminal p:TerminalJetData))
      (coleHopfBall A Vlo Vhi B) := by
    apply hraw.congr_of_eventuallyEq
    intro p hp
    have hpos : ∀ᶠq:ColeHopfParameter in 𝓝 p,0<q.1.2 :=
      (continuous_snd.comp continuous_fst).continuousAt (Ioi_mem_nhds (hVlo.trans_le hp.2.1))
    filter_upwards [hpos] with q hq
    exact (centeredColeHopfTerminal_raw q hq).symm
  exact hambient.submodule terminalJetSubmodule isClosed_terminalJetSubmodule _ _

theorem boundedSmoothOn_coleHopfTerminal (A Vlo Vhi B : ℝ)
    (hA : 0≤A) (hVlo : 0<Vlo) (hV : Vlo≤Vhi) (hB : 0≤B) :
    BoundedSmoothOn coleHopfTerminal (coleHopfBall A Vlo Vhi B) :=
  (boundedSmoothOn_coleHopf_terminal A Vlo Vhi B hA hVlo).add
    (boundedSmoothOn_centeredColeHopfTerminal A Vlo Vhi B hA hVlo hV hB)

end GeneralDepthPaper
