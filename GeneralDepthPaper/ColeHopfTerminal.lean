module

public import GeneralDepthPaper.TerminalJetUniform
public import GeneralDepthPaper.ClosedSubmoduleRegularity
public import GeneralDepthPaper.TerminalReconstruction

@[expose] public section


/-! The centered Cole–Hopf map is an actual jointly smooth map into the
manuscript's complete terminal-data Banach space, at every real mass (including
zero) and every positive variance. Its reconstructed function is precisely
`T(a,V,g) - g`. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
open ColeHopfFoundation.ProbabilityTheory

def centeredColeHopfJets (p : ColeHopfParameter) : Fin 3→ℝ →ᵇ ℝ :=
  ![terminalGaussianJetOne p-terminalJet p.2 0,
    terminalGaussianJetTwo p-terminalJet p.2 1,
    terminalGaussianJetThree p-terminalJet p.2 2]

theorem centeredColeHopfJets_compatible (p : ColeHopfParameter) (hv : 0<p.1.2) :
    (∀x,HasDerivAt (centeredColeHopfJets p 0) (centeredColeHopfJets p 1 x) x) ∧
    (∀x,HasDerivAt (centeredColeHopfJets p 1) (centeredColeHopfJets p 2 x) x) ∧
    UniformContinuous (centeredColeHopfJets p 2) := by
  refine ⟨fun x=>?_,fun x=>?_,?_⟩
  · simpa only [centeredColeHopfJets,Matrix.cons_val_zero,Matrix.cons_val_one,
      BoundedContinuousFunction.coe_sub,Pi.sub_apply] using
      (hasDerivAt_terminalGaussianJetOne p hv x).sub (hasDerivAt_terminalJet_zero p.2 x)
  · simpa [centeredColeHopfJets] using
      (hasDerivAt_terminalGaussianJetTwo p hv x).sub (hasDerivAt_terminalJet_one p.2 x)
  · convert! (uniformContinuous_terminalGaussianJetThree p hv).sub (uniformContinuous_terminalJet p.2 2) using 1

def centeredColeHopfTerminal (p : ColeHopfParameter) : TerminalSpace :=
  if hv:0<p.1.2 then
    terminalSpaceOfJets (centeredColeHopfValue p) (centeredColeHopfJets p)
      (centeredColeHopfJets_compatible p hv).1
      (centeredColeHopfJets_compatible p hv).2.1
      (centeredColeHopfJets_compatible p hv).2.2
  else 0

theorem centeredColeHopfTerminal_raw (p : ColeHopfParameter) (hv : 0<p.1.2) :
    (centeredColeHopfTerminal p : TerminalJetData)=
      (centeredColeHopfValue p 0,centeredColeHopfJets p) := by
  simp only [centeredColeHopfTerminal,dif_pos hv,terminalSpaceOfJets]

theorem terminalValue_centeredColeHopfTerminal (p : ColeHopfParameter) (hv : 0<p.1.2) (x : ℝ) :
    terminalValue (centeredColeHopfTerminal p) x=
      coleHopf p.1.1 p.1.2.toNNReal (terminalValue p.2) x-terminalValue p.2 x := by
  rw [centeredColeHopfTerminal,dif_pos hv]
  rw [terminalValue_terminalSpaceOfJets]
  · exact centeredColeHopfValue_apply p hv x
  · intro y
    exact hasDerivAt_centeredColeHopfValue_spatial p hv y

theorem contDiffAt_centeredColeHopfJets (p : ColeHopfParameter) (hv : 0<p.1.2) :
    ContDiffAt ℝ ∞ centeredColeHopfJets p := by
  rw [contDiffAt_pi]
  intro i
  have hJ (j:Fin 3) : ContDiffAt ℝ ∞ (fun q:ColeHopfParameter=>terminalJet q.2 j) p :=
    (terminalJetCLM j).contDiff.contDiffAt.comp p contDiffAt_snd
  fin_cases i
  · exact (analyticAt_terminalGaussianJetOne p hv).contDiffAt.sub (hJ 0)
  · exact (analyticAt_terminalGaussianJetTwo p hv).contDiffAt.sub (hJ 1)
  · exact (analyticAt_terminalGaussianJetThree p hv).contDiffAt.sub (hJ 2)

theorem contDiffAt_centeredColeHopfTerminal (p : ColeHopfParameter) (hv : 0<p.1.2) :
    ContDiffAt ℝ ∞ centeredColeHopfTerminal p := by
  apply contDiffAt_submodule_of_coe terminalJetSubmodule isClosed_terminalJetSubmodule
  have hval : ContDiffAt ℝ ∞ (fun q:ColeHopfParameter=>centeredColeHopfValue q 0) p :=
    ((BoundedContinuousFunction.evalCLM ℝ (0:ℝ)).contDiff.contDiffAt.comp p
      (contDiffAt_centeredColeHopfValue p hv)).of_le le_top
  have hraw := hval.prodMk (contDiffAt_centeredColeHopfJets p hv)
  apply hraw.congr_of_eventuallyEq
  have hpos : ∀ᶠq:ColeHopfParameter in 𝓝 p,0<q.1.2 :=
    ((continuous_snd.comp continuous_fst).continuousAt (lt_mem_nhds hv))
  filter_upwards [hpos] with q hq
  exact centeredColeHopfTerminal_raw q hq

end GeneralDepthPaper
