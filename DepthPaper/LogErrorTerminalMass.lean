module

public import DepthPaper.LogErrorBCFMassJets
public import DepthPaper.ClosedSubmoduleWithin
public import DepthPaper.LogCoshTerminal

@[expose] public section


/-! Actual logarithmic-error mass jets in the compatible terminal Banach
space. Every jet is obtained by a sup-norm derivative; endpoint derivatives
are within the physical closed mass interval. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal BoundedContinuousFunction
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem LogDeficitExpr.hasDerivAt_massBCF_spatial
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {V : ℝ} (hV : 1≤V)
    {m : ℝ} (hm : m∈Icc ε 1) (x : ℝ) :
    HasDerivAt (e.massBCF ε hε V hV m)
      (e.massDx.massBCF ε hε V hV m x) x := by
  have he : (e.massBCF ε hε V hV m:ℝ→ℝ)=e.physicalEval m V :=
    funext (e.massBCF_apply hε hV hm)
  rw [he,e.massDx.massBCF_apply hε hV hm]
  exact e.hasDerivAt_physicalEval_space
    ⟨hε.trans_le hm.1,hm.2.trans_lt (by norm_num)⟩ (zero_lt_one.trans_le hV) x

theorem LogDeficitExpr.uniformContinuous_massBCF
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {V : ℝ} (hV : 1≤V)
    {m : ℝ} (hm : m∈Icc ε 1) :
    UniformContinuous (e.massBCF ε hε V hV m:ℝ→ℝ) := by
  apply LipschitzWith.uniformContinuous
  apply lipschitzWith_of_nnnorm_deriv_le (C:=‖e.massDx.massBCF ε hε V hV m‖₊)
    (fun x=>(e.hasDerivAt_massBCF_spatial hε hV hm x).differentiableAt)
  intro x
  rw [(e.hasDerivAt_massBCF_spatial hε hV hm x).deriv]
  exact BoundedContinuousFunction.nnnorm_coe_le_nnnorm _ _

def LogDeficitExpr.massTerminalRaw (e : LogDeficitExpr MassResidualNormalizerExpr)
    (ε : ℝ) (hε : 0<ε) (V : ℝ) (hV : 1≤V) (j : ℕ) (m : ℝ) : TerminalJetData :=
  ((LogDeficitExpr.dm^[j] e).massBCF ε hε V hV m 0,
    fun i:Fin 3=>(LogDeficitExpr.dm^[j]
      (LogDeficitExpr.massDx^[((i:ℕ)+1)] e)).massBCF ε hε V hV m)

theorem LogDeficitExpr.massTerminalRaw_zero_mem
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {V : ℝ} (hV : 1≤V)
    {m : ℝ} (hm : m∈Icc ε 1) :
    e.massTerminalRaw ε hε V hV 0 m∈terminalJetSubmodule := by
  refine ⟨fun x=>?_,fun x=>?_,?_⟩
  · simpa only [massTerminalRaw,Function.iterate_zero_apply,
      Fin.val_zero,Fin.val_one,Function.iterate_succ_apply'] using
      e.massDx.hasDerivAt_massBCF_spatial hε hV hm x
  · convert! e.massDx.massDx.hasDerivAt_massBCF_spatial hε hV hm x using 1 <;>
      simp [massTerminalRaw,Function.iterate_succ_apply']
  · exact (LogDeficitExpr.massDx^[3] e).uniformContinuous_massBCF hε hV hm

theorem LogDeficitExpr.hasDerivWithinAt_massTerminalRaw
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {V : ℝ} (hV : 1≤V)
    (j : ℕ) {m : ℝ} (hm : m∈Icc ε 1) :
    HasDerivWithinAt (e.massTerminalRaw ε hε V hV j)
      (e.massTerminalRaw ε hε V hV (j+1) m) (Icc ε 1) m := by
  have hv := (BoundedContinuousFunction.evalCLM ℝ (0:ℝ) : (ℝ→ᵇℝ)→L[ℝ]ℝ).hasFDerivAt.comp_hasDerivWithinAt m
    ((LogDeficitExpr.dm^[j] e).hasDerivWithinAt_massBCF hε hV hm)
  have hj : HasDerivWithinAt
      (fun r=>fun i:Fin 3=>(LogDeficitExpr.dm^[j]
        (LogDeficitExpr.massDx^[((i:ℕ)+1)] e)).massBCF ε hε V hV r)
      (fun i:Fin 3=>(LogDeficitExpr.dm^[j+1]
        (LogDeficitExpr.massDx^[((i:ℕ)+1)] e)).massBCF ε hε V hV m)
      (Icc ε 1) m := by
    apply hasDerivWithinAt_pi.mpr
    intro i
    simpa only [Function.iterate_succ_apply'] using
      (LogDeficitExpr.dm^[j] (LogDeficitExpr.massDx^[((i:ℕ)+1)] e)).hasDerivWithinAt_massBCF hε hV hm
  convert! hv.prodMk hj using 1 <;>
    simp [massTerminalRaw,Function.iterate_succ_apply']

def LogDeficitExpr.massTerminalJet (e : LogDeficitExpr MassResidualNormalizerExpr)
    (ε : ℝ) (hε : 0<ε) (V : ℝ) (hV : 1≤V) (j : ℕ) (m : ℝ) : TerminalSpace :=
  closedSubmoduleChain terminalJetSubmodule (e.massTerminalRaw ε hε V hV) j m

theorem LogDeficitExpr.massTerminalJet_coe
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) {V : ℝ} (hV : 1≤V)
    (j : ℕ) {m : ℝ} (hm : m∈Icc ε 1) :
    (e.massTerminalJet ε hε V hV j m:TerminalJetData)=
      e.massTerminalRaw ε hε V hV j m := by
  have he := derivative_chain_mem_closed_submodule terminalJetSubmodule
    isClosed_terminalJetSubmodule (uniqueDiffOn_Icc hε1)
    (e.massTerminalRaw ε hε V hV)
    (fun j m hm=>e.hasDerivWithinAt_massTerminalRaw hε hV j hm)
    (fun m hm=>e.massTerminalRaw_zero_mem hε hV hm) j m hm
  simp only [massTerminalJet,closedSubmoduleChain,dif_pos he]

theorem LogDeficitExpr.contDiffOn_massTerminalJet
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) {V : ℝ} (hV : 1≤V) (j : ℕ) :
    ContDiffOn ℝ ∞ (e.massTerminalJet ε hε V hV j) (Icc ε 1) :=
  contDiffOn_closed_submodule_chain terminalJetSubmodule isClosed_terminalJetSubmodule
    (uniqueDiffOn_Icc hε1) (e.massTerminalRaw ε hε V hV)
    (fun j m hm=>e.hasDerivWithinAt_massTerminalRaw hε hV j hm)
    (fun m hm=>e.massTerminalRaw_zero_mem hε hV hm) j

end DepthPaper
