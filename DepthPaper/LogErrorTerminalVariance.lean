module

public import DepthPaper.LogErrorBCFVarianceJets
public import DepthPaper.LogErrorTerminalMass

@[expose] public section


/-! Actual variance derivatives in the closed compatible terminal-data
space. Compatibility of every derivative follows from closedness and
genuine sup-norm difference quotients. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal BoundedContinuousFunction
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def LogDeficitExpr.varianceTerminalRaw (e : LogDeficitExpr MassResidualNormalizerExpr)
    (ε : ℝ) (hε : 0<ε) (m : ℝ) (hm : m∈Icc ε 1) (U : ℝ) (k : ℕ) (V : ℝ) : TerminalJetData :=
  ((LogDeficitExpr.massDV^[k] e).varianceBCF ε hε m hm U V 0,
    fun i:Fin 3=>(LogDeficitExpr.massDV^[k]
      (LogDeficitExpr.massDx^[((i:ℕ)+1)] e)).varianceBCF ε hε m hm U V)

theorem LogDeficitExpr.varianceTerminalRaw_zero_mem
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {m : ℝ} (hm : m∈Icc ε 1) {U V : ℝ}
    (hV : V∈Icc (1:ℝ) U) :
    e.varianceTerminalRaw ε hε m hm U 0 V∈terminalJetSubmodule := by
  convert e.massTerminalRaw_zero_mem hε hV.1 hm using 1
  simp only [varianceTerminalRaw,massTerminalRaw,Function.iterate_zero_apply,
    varianceBCF,dif_pos hV]

theorem LogDeficitExpr.hasDerivWithinAt_varianceTerminalRaw
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {m : ℝ} (hm : m∈Icc ε 1) {U V : ℝ}
    (hU : 1≤U) (k : ℕ) (hV : V∈Icc (1:ℝ) U) :
    HasDerivWithinAt (e.varianceTerminalRaw ε hε m hm U k)
      (e.varianceTerminalRaw ε hε m hm U (k+1) V) (Icc (1:ℝ) U) V := by
  have hv := (BoundedContinuousFunction.evalCLM ℝ (0:ℝ) : (ℝ→ᵇℝ)→L[ℝ]ℝ).hasFDerivAt.comp_hasDerivWithinAt V
    ((LogDeficitExpr.massDV^[k] e).hasDerivWithinAt_varianceBCF hε hm hU hV)
  have hj : HasDerivWithinAt
      (fun W=>fun i:Fin 3=>(LogDeficitExpr.massDV^[k]
        (LogDeficitExpr.massDx^[((i:ℕ)+1)] e)).varianceBCF ε hε m hm U W)
      (fun i:Fin 3=>(LogDeficitExpr.massDV^[k+1]
        (LogDeficitExpr.massDx^[((i:ℕ)+1)] e)).varianceBCF ε hε m hm U V)
      (Icc (1:ℝ) U) V := by
    apply hasDerivWithinAt_pi.mpr
    intro i
    simpa only [Function.iterate_succ_apply'] using
      (LogDeficitExpr.massDV^[k] (LogDeficitExpr.massDx^[((i:ℕ)+1)] e)).hasDerivWithinAt_varianceBCF hε hm hU hV
  convert! hv.prodMk hj using 1 <;>
    simp [varianceTerminalRaw,Function.iterate_succ_apply']

def LogDeficitExpr.varianceTerminalJet (e : LogDeficitExpr MassResidualNormalizerExpr)
    (ε : ℝ) (hε : 0<ε) (m : ℝ) (hm : m∈Icc ε 1) (U : ℝ) (k : ℕ) (V : ℝ) : TerminalSpace :=
  closedSubmoduleChain terminalJetSubmodule (e.varianceTerminalRaw ε hε m hm U) k V

theorem LogDeficitExpr.varianceTerminalJet_coe
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {m : ℝ} (hm : m∈Icc ε 1) {U V : ℝ}
    (hU : 1<U) (k : ℕ) (hV : V∈Icc (1:ℝ) U) :
    (e.varianceTerminalJet ε hε m hm U k V:TerminalJetData)=
      e.varianceTerminalRaw ε hε m hm U k V := by
  have he := derivative_chain_mem_closed_submodule terminalJetSubmodule
    isClosed_terminalJetSubmodule (uniqueDiffOn_Icc hU)
    (e.varianceTerminalRaw ε hε m hm U)
    (fun k V hV=>e.hasDerivWithinAt_varianceTerminalRaw hε hm hU.le k hV)
    (fun V hV=>e.varianceTerminalRaw_zero_mem hε hm hV) k V hV
  simp only [varianceTerminalJet,closedSubmoduleChain,dif_pos he]

theorem LogDeficitExpr.contDiffOn_varianceTerminalJet
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {m : ℝ} (hm : m∈Icc ε 1) {U : ℝ} (hU : 1<U) (k : ℕ) :
    ContDiffOn ℝ ∞ (e.varianceTerminalJet ε hε m hm U k) (Icc (1:ℝ) U) :=
  contDiffOn_closed_submodule_chain terminalJetSubmodule isClosed_terminalJetSubmodule
    (uniqueDiffOn_Icc hU) (e.varianceTerminalRaw ε hε m hm U)
    (fun k V hV=>e.hasDerivWithinAt_varianceTerminalRaw hε hm hU.le k hV)
    (fun V hV=>e.varianceTerminalRaw_zero_mem hε hm hV) k

end DepthPaper
