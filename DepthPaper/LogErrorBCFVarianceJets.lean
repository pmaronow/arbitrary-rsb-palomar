module

public import DepthPaper.LogErrorBCFMassJets

@[expose] public section


/-! Actual sup-norm variance jets on every bounded physical variance
interval. The pointwise heat derivatives are lifted by a uniform mean-value
estimate using the next genuine logarithmic differential expression. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal BoundedContinuousFunction
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def LogDeficitExpr.varianceBCF (e : LogDeficitExpr MassResidualNormalizerExpr)
    (ε : ℝ) (hε : 0<ε) (m : ℝ) (hm : m∈Icc ε 1) (U : ℝ) (V : ℝ) : ℝ→ᵇℝ :=
  if hV:V∈Icc (1:ℝ) U then e.massBCF ε hε V hV.1 m else 0

theorem LogDeficitExpr.varianceBCF_apply
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {m : ℝ} (hm : m∈Icc ε 1) {U V : ℝ}
    (hV : V∈Icc (1:ℝ) U) (x : ℝ) :
    e.varianceBCF ε hε m hm U V x=e.physicalEval m V x := by
  rw [varianceBCF,dif_pos hV,e.massBCF_apply hε hV.1 hm]

theorem LogDeficitExpr.varianceBCF_pointwise_derivative
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {m : ℝ} (hm : m∈Icc ε 1) {U V : ℝ}
    (hV : V∈Icc (1:ℝ) U) (x : ℝ) :
    HasDerivWithinAt (fun W=>e.varianceBCF ε hε m hm U W x)
      (e.massDV.varianceBCF ε hε m hm U V x) (Icc (1:ℝ) U) V := by
  rw [e.massDV.varianceBCF_apply hε hm hV]
  apply (e.hasDerivAt_physicalEval_variance
    ⟨hε.trans_le hm.1,hm.2.trans_lt (by norm_num)⟩
    (zero_lt_one.trans_le hV.1) x).hasDerivWithinAt.congr
  · intro W hW
    exact e.varianceBCF_apply hε hm hW x
  · exact e.varianceBCF_apply hε hm hV x

theorem LogDeficitExpr.varianceBCF_lipschitz
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {m : ℝ} (hm : m∈Icc ε 1) {U : ℝ} (hU : 1≤U) :
    ∃K:ℝ≥0,LipschitzOnWith K (e.varianceBCF ε hε m hm U) (Icc (1:ℝ) U) := by
  obtain ⟨C,hC,d,hb⟩:=e.massDV.polynomial_bound hε
  have hK : 0≤C*U^d := by positivity
  refine ⟨(C*U^d).toNNReal,?_⟩
  apply lipschitzOnWith_bcf_of_pointwise _ _ _ (convex_Icc 1 U)
  · intro V hV x
    exact e.varianceBCF_pointwise_derivative hε hm hV x
  · intro V hV x
    rw [e.massDV.varianceBCF_apply hε hm hV,Real.coe_toNNReal _ hK]
    exact (hb m hm V hV.1 x).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [hV.1]) hV.2 d) hC.le)

theorem LogDeficitExpr.continuousOn_varianceBCF
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {m : ℝ} (hm : m∈Icc ε 1) {U : ℝ} (hU : 1≤U) :
    ContinuousOn (e.varianceBCF ε hε m hm U) (Icc (1:ℝ) U) :=
  (e.varianceBCF_lipschitz hε hm hU).choose_spec.continuousOn

theorem LogDeficitExpr.hasDerivWithinAt_varianceBCF
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {m : ℝ} (hm : m∈Icc ε 1) {U V : ℝ}
    (hU : 1≤U) (hV : V∈Icc (1:ℝ) U) :
    HasDerivWithinAt (e.varianceBCF ε hε m hm U)
      (e.massDV.varianceBCF ε hε m hm U V) (Icc (1:ℝ) U) V := by
  apply hasDerivWithinAt_bcf_of_pointwise _ _ _ (convex_Icc 1 U) hV
  · intro W hW x
    exact e.varianceBCF_pointwise_derivative hε hm hW x
  · exact e.massDV.continuousOn_varianceBCF hε hm hU V hV

theorem LogDeficitExpr.contDiffOn_varianceBCF
    (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {m : ℝ} (hm : m∈Icc ε 1) {U : ℝ} (hU : 1<U) :
    ContDiffOn ℝ ∞ (e.varianceBCF ε hε m hm U) (Icc (1:ℝ) U) := by
  apply contDiffOn_of_within_derivative_chain (uniqueDiffOn_Icc hU)
    (fun k V=>(LogDeficitExpr.massDV^[k] e).varianceBCF ε hε m hm U V) _ 0
  intro k V hV
  simpa only [Function.iterate_succ_apply'] using
    (LogDeficitExpr.massDV^[k] e).hasDerivWithinAt_varianceBCF hε hm hU.le hV

end DepthPaper
