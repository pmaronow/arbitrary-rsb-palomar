module

public import GeneralDepthPaper.LogErrorTerminalMass
public import GeneralDepthPaper.CutoffTerminal
public import GeneralDepthPaper.ScaledLogCoshTerminal

@[expose] public section


/-! The actual terminal error and ψ_m have Banach-space mass regularity,
including genuine one-sided jets at m=1. No scalar-jet regularity is used
as a substitute for sup-norm parameter regularity. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem terminalValue_sub (g h : TerminalSpace) (x : ℝ) :
    terminalValue (g-h) x=terminalValue g x-terminalValue h x :=
  (terminalEvalCLM x).map_sub g h

theorem LogDeficitExpr.terminalValue_massTerminalJet_zero
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) {V : ℝ} (hV : 1≤V)
    {m : ℝ} (hm : m∈Icc ε 1) (x : ℝ) :
    terminalValue (e.massTerminalJet ε hε V hV 0 m) x=e.physicalEval m V x := by
  unfold terminalValue
  rw [e.massTerminalJet_coe hε hε1 hV 0 hm]
  change e.massBCF ε hε V hV m 0+
    (∫y in (0:ℝ)..x,e.massDx.massBCF ε hε V hV m y)=e.physicalEval m V x
  rw [e.massBCF_apply hε hV hm 0,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _=>by
        rw [e.massDx.massBCF_apply hε hV hm]
        exact e.hasDerivAt_physicalEval_space
          ⟨hε.trans_le hm.1,hm.2.trans_lt (by norm_num)⟩ (zero_lt_one.trans_le hV) y)
      ((e.massDx.massBCF ε hε V hV m).continuous.intervalIntegrable (0:ℝ) x)]
  ring

theorem cutoffTerminal_sub_scaledLogCosh_eq_massTerminalJet
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) {V : ℝ} (hV : 1≤V)
    {m : ℝ} (hm : m∈Icc ε 1) :
    cutoffTerminal m V-scaledLogCoshTerminal m=
      errorMassBaseExpr.massTerminalJet ε hε V hV 0 m := by
  apply terminalValue_injective
  funext x
  have hm0 : 0 < m := hε.trans_le hm.1
  have hV0 : 0≤V := (zero_lt_one.trans_le hV).le
  have hχ:=terminalValue_cutoffTerminal_error m ⟨hm0,hm.2⟩ V.toNNReal x
  rw [Real.coe_toNNReal V hV0] at hχ
  rw [terminalValue_sub,hχ,terminalValue_scaledLogCoshTerminal m hm0.ne',
    LogDeficitExpr.terminalValue_massTerminalJet_zero _ hε hε1 hV hm,
    errorMassBaseExpr_eval,
    largeVarianceError_real_eq_logarithmicError
      ⟨hm0,hm.2.trans_lt (by norm_num)⟩ hV0 x]
  rw [div_eq_mul_inv]
  ring

theorem contDiffOn_scaledLogCoshTerminal_closed_mass
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) :
    ContDiffOn ℝ ∞ scaledLogCoshTerminal (Icc ε 1) := by
  let E : ℝ→TerminalSpace:=errorMassBaseExpr.massTerminalJet ε hε 1 (by norm_num) 0
  have hE : ContDiffOn ℝ ∞ E (Icc ε 1) :=
    errorMassBaseExpr.contDiffOn_massTerminalJet hε hε1 (by norm_num) 0
  have hχ : ContDiffOn ℝ ∞ (fun m=>cutoffTerminal m 1) (Icc ε 1) := by
    intro m hm
    have hd:=contDiffAt_cutoffTerminal (m:=m) (V:=1) (hε.trans_le hm.1).ne' (by norm_num)
    have ha : ContDiffAt ℝ ∞ (fun r:ℝ=>(r,(1:ℝ))) m := by fun_prop
    exact (hd.comp m ha).contDiffWithinAt
  apply (hχ.sub hE).congr
  intro m hm
  have he:=cutoffTerminal_sub_scaledLogCosh_eq_massTerminalJet hε hε1 (V:=1) (by norm_num) hm
  change scaledLogCoshTerminal m=cutoffTerminal m 1-E m
  dsimp only [E]
  rw [←he]
  abel

end GeneralDepthPaper
