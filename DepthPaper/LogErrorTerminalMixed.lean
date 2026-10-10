module

public import DepthPaper.LogErrorTerminalVariance
public import DepthPaper.LogErrorTerminalMassBounds

@[expose] public section


/-! Compatible mixed mass/variance terminal jets of the actual logarithmic
error. All compatibility is derived from actual sup-norm derivatives, and
the bounds are uniform in the spatial variable and the physical mass. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal BoundedContinuousFunction BigOperators
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def LogDeficitExpr.parameterTerminalRaw (e : LogDeficitExpr MassResidualNormalizerExpr)
    (ε : ℝ) (hε : 0<ε) (V : ℝ) (hV : 1≤V) (j k : ℕ) (m : ℝ) : TerminalJetData :=
  ((LogDeficitExpr.dm^[j] (LogDeficitExpr.massDV^[k] e)).massBCF ε hε V hV m 0,
    fun i:Fin 3=>(LogDeficitExpr.dm^[j] (LogDeficitExpr.massDV^[k]
      (LogDeficitExpr.massDx^[((i:ℕ)+1)] e))).massBCF ε hε V hV m)

theorem LogDeficitExpr.parameterTerminalRaw_zero_mem
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {V : ℝ} (hV : 1≤V) (k : ℕ)
    {m : ℝ} (hm : m∈Icc ε 1) :
    e.parameterTerminalRaw ε hε V hV 0 k m∈terminalJetSubmodule := by
  have hU : 1<V+1 := by linarith
  have hi : V∈Icc (1:ℝ) (V+1) := ⟨hV,by linarith⟩
  have hh := (e.varianceTerminalJet ε hε m hm (V+1) k V).property
  rw [e.varianceTerminalJet_coe hε hm hU k hi] at hh
  convert hh using 1
  simp only [parameterTerminalRaw,varianceTerminalRaw,Function.iterate_zero_apply,
    varianceBCF,dif_pos hi]

theorem LogDeficitExpr.hasDerivWithinAt_parameterTerminalRaw
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {V : ℝ} (hV : 1≤V) (j k : ℕ)
    {m : ℝ} (hm : m∈Icc ε 1) :
    HasDerivWithinAt (fun r=>e.parameterTerminalRaw ε hε V hV j k r)
      (e.parameterTerminalRaw ε hε V hV (j+1) k m) (Icc ε 1) m := by
  have hv := (BoundedContinuousFunction.evalCLM ℝ (0:ℝ) : (ℝ→ᵇℝ)→L[ℝ]ℝ).hasFDerivAt.comp_hasDerivWithinAt m
    ((LogDeficitExpr.dm^[j] (LogDeficitExpr.massDV^[k] e)).hasDerivWithinAt_massBCF hε hV hm)
  have hj : HasDerivWithinAt
      (fun r=>fun i:Fin 3=>(LogDeficitExpr.dm^[j] (LogDeficitExpr.massDV^[k]
        (LogDeficitExpr.massDx^[((i:ℕ)+1)] e))).massBCF ε hε V hV r)
      (fun i:Fin 3=>(LogDeficitExpr.dm^[j+1] (LogDeficitExpr.massDV^[k]
        (LogDeficitExpr.massDx^[((i:ℕ)+1)] e))).massBCF ε hε V hV m)
      (Icc ε 1) m := by
    apply hasDerivWithinAt_pi.mpr
    intro i
    simpa only [Function.iterate_succ_apply'] using
      (LogDeficitExpr.dm^[j] (LogDeficitExpr.massDV^[k]
        (LogDeficitExpr.massDx^[((i:ℕ)+1)] e))).hasDerivWithinAt_massBCF hε hV hm
  convert! hv.prodMk hj using 1 <;>
    simp [parameterTerminalRaw,Function.iterate_succ_apply']

def LogDeficitExpr.parameterTerminalJet (e : LogDeficitExpr MassResidualNormalizerExpr)
    (ε : ℝ) (hε : 0<ε) (V : ℝ) (hV : 1≤V) (j k : ℕ) (m : ℝ) : TerminalSpace :=
  closedSubmoduleChain terminalJetSubmodule
    (fun i r=>e.parameterTerminalRaw ε hε V hV i k r) j m

theorem LogDeficitExpr.parameterTerminalJet_coe
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) {V : ℝ} (hV : 1≤V) (j k : ℕ)
    {m : ℝ} (hm : m∈Icc ε 1) :
    (e.parameterTerminalJet ε hε V hV j k m:TerminalJetData)=
      e.parameterTerminalRaw ε hε V hV j k m := by
  have he := derivative_chain_mem_closed_submodule terminalJetSubmodule
    isClosed_terminalJetSubmodule (uniqueDiffOn_Icc hε1)
    (fun i r=>e.parameterTerminalRaw ε hε V hV i k r)
    (fun i m hm=>e.hasDerivWithinAt_parameterTerminalRaw hε hV i k hm)
    (fun m hm=>e.parameterTerminalRaw_zero_mem hε hV k hm) j m hm
  simp only [parameterTerminalJet,closedSubmoduleChain,dif_pos he]

theorem LogDeficitExpr.contDiffOn_parameterTerminalJet
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) {V : ℝ} (hV : 1≤V) (j k : ℕ) :
    ContDiffOn ℝ ∞ (e.parameterTerminalJet ε hε V hV j k) (Icc ε 1) :=
  contDiffOn_closed_submodule_chain terminalJetSubmodule isClosed_terminalJetSubmodule
    (uniqueDiffOn_Icc hε1) (fun i r=>e.parameterTerminalRaw ε hε V hV i k r)
    (fun i m hm=>e.hasDerivWithinAt_parameterTerminalRaw hε hV i k hm)
    (fun m hm=>e.parameterTerminalRaw_zero_mem hε hV k hm) j

end DepthPaper
