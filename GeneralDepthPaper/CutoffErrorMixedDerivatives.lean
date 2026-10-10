module

public import GeneralDepthPaper.CutoffTerminalSmooth
public import GeneralDepthPaper.LogErrorTerminalMixedBounds

@[expose] public section


/-! The bounded differential-algebra jets are identified with actual
Banach-space mixed derivatives of χ−ψ. Variance derivatives are ordinary;
mass derivatives at the physical endpoint are genuine within derivatives. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

theorem LogDeficitExpr.varianceTerminalJet_eq_parameterTerminalJet
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) {m : ℝ} (hm : m∈Icc ε 1)
    {U V : ℝ} (hU : 1<U) (hV : V∈Icc (1:ℝ) U) (k : ℕ) :
    e.varianceTerminalJet ε hε m hm U k V=
      e.parameterTerminalJet ε hε V hV.1 0 k m := by
  apply Subtype.ext
  rw [e.varianceTerminalJet_coe hε hm hU k hV,
    e.parameterTerminalJet_coe hε hε1 hV.1 0 k hm]
  simp only [varianceTerminalRaw,parameterTerminalRaw,Function.iterate_zero_apply,
    varianceBCF,dif_pos hV]

theorem cutoffErrorTerminal_eq_varianceTerminalJet_zero
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) {m : ℝ} (hm : m∈Icc ε 1)
    {U V : ℝ} (hU : 1<U) (hV : V∈Icc (1:ℝ) U) :
    cutoffErrorTerminal m V=errorMassBaseExpr.varianceTerminalJet ε hε m hm U 0 V := by
  rw [cutoffErrorTerminal,cutoffTerminal_sub_scaledLogCosh_eq_massTerminalJet hε hε1 hV.1 hm]
  apply Subtype.ext
  rw [LogDeficitExpr.massTerminalJet_coe _ hε hε1 hV.1 0 hm,
    LogDeficitExpr.varianceTerminalJet_coe _ hε hm hU 0 hV]
  simp only [LogDeficitExpr.massTerminalRaw,LogDeficitExpr.varianceTerminalRaw,
    Function.iterate_zero_apply,LogDeficitExpr.varianceBCF,dif_pos hV]

theorem LogDeficitExpr.hasDerivWithinAt_varianceTerminalJet
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {m : ℝ} (hm : m∈Icc ε 1) {U V : ℝ}
    (hU : 1<U) (hV : V∈Icc (1:ℝ) U) (k : ℕ) :
    HasDerivWithinAt (e.varianceTerminalJet ε hε m hm U k)
      (e.varianceTerminalJet ε hε m hm U (k+1) V) (Icc (1:ℝ) U) V :=
  hasDerivWithinAt_closed_submodule_chain terminalJetSubmodule isClosed_terminalJetSubmodule
    (uniqueDiffOn_Icc hU) (e.varianceTerminalRaw ε hε m hm U)
    (fun i W hW=>e.hasDerivWithinAt_varianceTerminalRaw hε hm hU.le i hW)
    (fun W hW=>e.varianceTerminalRaw_zero_mem hε hm hW) k hV

theorem iteratedDeriv_cutoffErrorTerminal_variance
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) {m : ℝ} (hm : m∈Icc ε 1)
    {V : ℝ} (hV : 1<V) (k : ℕ) :
    iteratedDeriv k (fun W=>cutoffErrorTerminal m W) V=
      errorMassBaseExpr.parameterTerminalJet ε hε V hV.le 0 k m := by
  let U:=V+1
  have hU:1<U:=by dsimp only [U];linarith
  have hv:V∈Ioo (1:ℝ) U:=⟨hV,by dsimp only [U];linarith⟩
  let G:=fun i W=>errorMassBaseExpr.varianceTerminalJet ε hε m hm U i W
  have hd:∀i,∀W∈Ioo (1:ℝ) U,HasDerivWithinAt (G i) (G (i+1) W) (Ioo (1:ℝ) U) W := by
    intro i W hW
    exact (LogDeficitExpr.hasDerivWithinAt_varianceTerminalJet _ hε hm hU
      ⟨hW.1.le,hW.2.le⟩ i).mono Ioo_subset_Icc_self
  have he:EqOn (fun W=>cutoffErrorTerminal m W) (G 0) (Ioo (1:ℝ) U) :=
    fun W hW=>cutoffErrorTerminal_eq_varianceTerminalJet_zero hε hε1 hm hU ⟨hW.1.le,hW.2.le⟩
  rw [←iteratedDerivWithin_of_isOpen isOpen_Ioo hv]
  rw [iteratedDerivWithin_congr he hv,
    iteratedDerivWithin_of_within_derivative_chain (uniqueDiffOn_Ioo 1 U) G hd k hv]
  exact LogDeficitExpr.varianceTerminalJet_eq_parameterTerminalJet _ hε hε1 hm hU
    ⟨hV.le,hv.2.le⟩ k

theorem LogDeficitExpr.hasDerivWithinAt_parameterTerminalJet
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) {V : ℝ} (hV : 1≤V) (j k : ℕ)
    {m : ℝ} (hm : m∈Icc ε 1) :
    HasDerivWithinAt (e.parameterTerminalJet ε hε V hV j k)
      (e.parameterTerminalJet ε hε V hV (j+1) k m) (Icc ε 1) m :=
  hasDerivWithinAt_closed_submodule_chain terminalJetSubmodule isClosed_terminalJetSubmodule
    (uniqueDiffOn_Icc hε1) (fun i r=>e.parameterTerminalRaw ε hε V hV i k r)
    (fun i r hr=>e.hasDerivWithinAt_parameterTerminalRaw hε hV i k hr)
    (fun r hr=>e.parameterTerminalRaw_zero_mem hε hV k hr) j hm

theorem iteratedDerivWithin_cutoffErrorTerminal_mass_variance
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) {m : ℝ} (hm : m∈Icc ε 1)
    {V : ℝ} (hV : 1<V) (j k : ℕ) :
    iteratedDerivWithin j (fun r=>iteratedDeriv k (fun W=>cutoffErrorTerminal r W) V)
      (Icc ε 1) m=errorMassBaseExpr.parameterTerminalJet ε hε V hV.le j k m := by
  let G:=fun i r=>errorMassBaseExpr.parameterTerminalJet ε hε V hV.le i k r
  have he:EqOn (fun r=>iteratedDeriv k (fun W=>cutoffErrorTerminal r W) V)
      (G 0) (Icc ε 1) := fun r hr=>iteratedDeriv_cutoffErrorTerminal_variance hε hε1 hr hV k
  rw [iteratedDerivWithin_congr he hm]
  exact iteratedDerivWithin_of_within_derivative_chain (uniqueDiffOn_Icc hε1) G
    (fun i r hr=>LogDeficitExpr.hasDerivWithinAt_parameterTerminalJet _ hε hε1 hV.le i k hr) j hm

theorem cutoffErrorTerminal_mixed_sumNorm_bound
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) (j k : ℕ) :
    ∃C:ℝ,0<C ∧ ∃D:ℕ,∀V>1,∀m∈Icc ε 1,
      terminalSumNorm (iteratedDerivWithin j
        (fun r=>iteratedDeriv k (fun W=>cutoffErrorTerminal r W) V) (Icc ε 1) m)≤
          C*V^D*Real.exp (-(ε^2)*V/2) := by
  obtain ⟨C,hC,D,hb⟩:=errorMassBaseExpr.parameterTerminalJet_sumNorm_exponential_bound
    (Or.inr trivial) hε hε1 j k
  refine ⟨C,hC,D,?_⟩
  intro V hV m hm
  rw [iteratedDerivWithin_cutoffErrorTerminal_mass_variance hε hε1 hm hV j k]
  exact hb V hV.le m hm

end GeneralDepthPaper
