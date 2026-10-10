module

public import DepthPaper.BCFParameterDerivative
public import DepthPaper.SourceLogarithmicErrorBounds

@[expose] public section


/-! The actual logarithmic differential algebra lifted to the sup-norm
Banach space. Mass derivatives at the upper endpoint are genuine within
derivatives on the closed physical mass interval. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal BoundedContinuousFunction
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem LogDeficitExpr.mass_section_bounded
    (e : LogDeficitExpr MassResidualNormalizerExpr) {ε : ℝ} (hε : 0<ε)
    {V : ℝ} (hV : 1≤V) {m : ℝ} (hm : m∈Icc ε 1) :
    ∃K:ℝ,0≤K ∧ ∀x,‖e.physicalEval m V x‖≤K := by
  obtain ⟨C,hC,d,hb⟩:=e.polynomial_bound hε
  exact ⟨C*V^d,by positivity,fun x=>hb m hm V hV x⟩

def LogDeficitExpr.massBCF (e : LogDeficitExpr MassResidualNormalizerExpr)
    (ε : ℝ) (hε : 0<ε) (V : ℝ) (hV : 1≤V) (m : ℝ) : ℝ→ᵇℝ :=
  if hm:m∈Icc ε 1 then
    BoundedContinuousFunction.ofNormedAddCommGroup (e.physicalEval m V)
      (continuous_iff_continuousAt.mpr fun x=>
        (e.hasDerivAt_physicalEval_space
          ⟨hε.trans_le hm.1,hm.2.trans_lt (by norm_num)⟩ (zero_lt_one.trans_le hV) x).continuousAt)
      (Classical.choose (e.mass_section_bounded hε hV hm))
      (Classical.choose_spec (e.mass_section_bounded hε hV hm)).2
  else 0

theorem LogDeficitExpr.massBCF_apply (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {V : ℝ} (hV : 1≤V) {m : ℝ} (hm : m∈Icc ε 1) (x : ℝ) :
    e.massBCF ε hε V hV m x=e.physicalEval m V x := by
  rw [massBCF,dif_pos hm]
  rfl

theorem LogDeficitExpr.massBCF_pointwise_derivative (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {V : ℝ} (hV : 1≤V) {m : ℝ} (hm : m∈Icc ε 1) (x : ℝ) :
    HasDerivWithinAt (fun r=>e.massBCF ε hε V hV r x)
      (e.dm.massBCF ε hε V hV m x) (Icc ε 1) m := by
  rw [massBCF_apply _ hε hV hm]
  apply (e.hasDerivAt_physicalEval_mass
    ⟨hε.trans_le hm.1,hm.2.trans_lt (by norm_num)⟩ (zero_lt_one.trans_le hV) x).hasDerivWithinAt.congr
  · intro r hr
    exact e.massBCF_apply hε hV hr x
  · exact e.massBCF_apply hε hV hm x

theorem LogDeficitExpr.massBCF_lipschitz (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {V : ℝ} (hV : 1≤V) :
    ∃K:ℝ≥0,LipschitzOnWith K (e.massBCF ε hε V hV) (Icc ε 1) := by
  obtain ⟨C,hC,d,hb⟩:=e.dm.polynomial_bound hε
  have hK : 0≤C*V^d := by positivity
  refine ⟨(C*V^d).toNNReal,?_⟩
  apply lipschitzOnWith_bcf_of_pointwise _ _ _ (convex_Icc ε 1)
  · intro m hm x
    exact e.massBCF_pointwise_derivative hε hV hm x
  · intro m hm x
    rw [massBCF_apply _ hε hV hm,Real.coe_toNNReal _ hK]
    exact hb m hm V hV x

theorem LogDeficitExpr.continuousOn_massBCF (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {V : ℝ} (hV : 1≤V) :
    ContinuousOn (e.massBCF ε hε V hV) (Icc ε 1) :=
  (e.massBCF_lipschitz hε hV).choose_spec.continuousOn

theorem LogDeficitExpr.hasDerivWithinAt_massBCF (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) {V : ℝ} (hV : 1≤V) {m : ℝ} (hm : m∈Icc ε 1) :
    HasDerivWithinAt (e.massBCF ε hε V hV) (e.dm.massBCF ε hε V hV m) (Icc ε 1) m := by
  apply hasDerivWithinAt_bcf_of_pointwise _ _ _ (convex_Icc ε 1) hm
  · intro r hr x
    exact e.massBCF_pointwise_derivative hε hV hr x
  · exact e.dm.continuousOn_massBCF hε hV m hm

theorem LogDeficitExpr.contDiffOn_massBCF (e : LogDeficitExpr MassResidualNormalizerExpr)
    {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) {V : ℝ} (hV : 1≤V) :
    ContDiffOn ℝ ∞ (e.massBCF ε hε V hV) (Icc ε 1) := by
  apply contDiffOn_of_within_derivative_chain (uniqueDiffOn_Icc hε1)
    (fun j m=>(LogDeficitExpr.dm^[j] e).massBCF ε hε V hV m) _ 0
  intro j m hm
  simpa only [Function.iterate_succ_apply'] using
    (LogDeficitExpr.dm^[j] e).hasDerivWithinAt_massBCF hε hV hm

end DepthPaper
