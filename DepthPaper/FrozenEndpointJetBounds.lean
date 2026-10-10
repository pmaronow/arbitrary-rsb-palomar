module

public import DepthPaper.ReducedEndpointFunctional
public import DepthPaper.EndpointTermBounds

@[expose] public section


/-! Actual full and frozen-endpoint jets of the correction to the
limiting objective. Affine freezing is a contraction in the product norm. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 64

theorem norm_iteratedFDeriv_affine_contraction_at
    {E F G:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L:E→L[ℝ] F) (hL:‖L‖ ≤ 1) (b:F) {f:F→G} {x:E}
    (hf:ContDiffAt ℝ ∞ f (b+L x)) (j:ℕ) :
    ‖iteratedFDeriv ℝ j (fun y=>f (b+L y)) x‖ ≤ ‖iteratedFDeriv ℝ j f (b+L x)‖ := by
  have hshift:ContDiffAt ℝ ∞ (fun y=>f (b+y)) (L x) :=
    hf.comp _ (contDiffAt_const.add contDiffAt_id)
  have H := norm_iteratedFDeriv_comp_CLM_contraction L hL hshift j
  rw [iteratedFDeriv_comp_add_left] at H
  exact H

theorem norm_freeze_endpoint_jet_le {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f:E×ℝ→ℝ} {theta:E} (Q:ℝ) (hf:ContDiffAt ℝ ∞ f (theta,Q)) (j:ℕ) :
    ‖iteratedFDeriv ℝ j (fun u=>f (u,Q)) theta‖ ≤ ‖iteratedFDeriv ℝ j f (theta,Q)‖ := by
  have hL:‖ContinuousLinearMap.inl ℝ E ℝ‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simp only [ContinuousLinearMap.inl_apply,Prod.norm_def,norm_zero,one_mul]
    exact max_le le_rfl (norm_nonneg _)
  have H := norm_iteratedFDeriv_affine_contraction_at (ContinuousLinearMap.inl ℝ E ℝ) hL
    (0,Q) (x:=theta) (by simpa only [ContinuousLinearMap.inl_apply,Prod.mk_add_mk,
      zero_add,add_zero] using hf) j
  simpa only [ContinuousLinearMap.inl_apply,Prod.mk_add_mk,zero_add,add_zero] using H

def endpointCorrectionChart (Ξ : AdmissibleCovariance) {r:ℕ} (p:ℕ) (qc:ℝ)
    (w:HighDegreeLowerParameter r×ℝ) : ℝ :=
  endpointTermExpression Ξ p (cutoffParameterAssembly w)+
    lowerRecursionErrorRaw Ξ p qc (cutoffParameterAssembly w)

theorem endpointFunctionalChart_eq_limiting_add_correction (Ξ:AdmissibleCovariance) {r:ℕ}
    (p:ℕ) (qc:ℝ) (w:HighDegreeLowerParameter r×ℝ) :
    endpointFunctionalChart Ξ p qc w=limitingObjectiveCore Ξ w.1+endpointCorrectionChart Ξ p qc w := by
  unfold endpointFunctionalChart endpointFunctionalExtension endpointCorrectionChart
  change limitingObjectiveCore Ξ w.1+endpointTermExpression Ξ p (cutoffParameterAssembly w)+
    lowerRecursionErrorRaw Ξ p qc (cutoffParameterAssembly w)=_
  ring

theorem contDiffAt_endpointCorrectionChart (Ξ:AdmissibleCovariance) {r:ℕ}
    (p:ℕ) (qc:ℝ) {w:HighDegreeLowerParameter r×ℝ}
    (hw:cutoffParameterAssembly w∈cutoffInputSmoothDomain Ξ p qc) :
    ContDiffAt ℝ ∞ (endpointCorrectionChart Ξ p qc) w :=
  ((contDiff_endpointTermExpression Ξ p).contDiffAt.comp w
    cutoffParameterAssembly.contDiff.contDiffAt).add
      (((contDiffOn_lowerRecursionErrorRaw Ξ p qc).contDiffAt
        ((isOpen_cutoffInputSmoothDomain Ξ p qc).mem_nhds hw)).comp w
          cutoffParameterAssembly.contDiff.contDiffAt)

theorem endpointCorrectionChart_full_jet_bound (Ξ:AdmissibleCovariance) {r:ℕ}
    (p:ℕ) (qc:ℝ) {w:HighDegreeLowerParameter r×ℝ}
    (hw:cutoffParameterAssembly w∈cutoffInputSmoothDomain Ξ p qc) (j:ℕ) {B R:ℝ}
    (hE:‖iteratedFDeriv ℝ j (endpointTermExpression Ξ p) (cutoffParameterAssembly w)‖ ≤ B)
    (hR:‖iteratedFDeriv ℝ j (lowerRecursionErrorRaw Ξ p qc) (cutoffParameterAssembly w)‖ ≤ R) :
    ‖iteratedFDeriv ℝ j (endpointCorrectionChart Ξ p qc) w‖ ≤ B+R := by
  have hRaw := (contDiffOn_lowerRecursionErrorRaw Ξ p qc).contDiffAt
    ((isOpen_cutoffInputSmoothDomain Ξ p qc).mem_nhds hw)
  have hEi : ContDiffAt ℝ ∞ (endpointTermExpression Ξ p) (cutoffParameterAssembly w) :=
    (contDiff_endpointTermExpression Ξ p).contDiffAt
  have hEw := hEi.comp w cutoffParameterAssembly.contDiff.contDiffAt
  have hRw := hRaw.comp w cutoffParameterAssembly.contDiff.contDiffAt
  change ContDiffAt ℝ ∞ (fun u=>endpointTermExpression Ξ p (cutoffParameterAssembly u)) w at hEw
  change ContDiffAt ℝ ∞ (fun u=>lowerRecursionErrorRaw Ξ p qc (cutoffParameterAssembly u)) w at hRw
  change ‖iteratedFDeriv ℝ j (fun u=>endpointTermExpression Ξ p (cutoffParameterAssembly u)+
    lowerRecursionErrorRaw Ξ p qc (cutoffParameterAssembly u)) w‖ ≤ _
  rw [fun_iteratedFDeriv_add_apply
    (hEw.of_le (by simp)) (hRw.of_le (by simp))]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_iteratedFDeriv_comp_CLM_contraction cutoffParameterAssembly
      norm_cutoffParameterAssembly_le hEi j).trans hE)
    ((norm_iteratedFDeriv_comp_CLM_contraction cutoffParameterAssembly
      norm_cutoffParameterAssembly_le hRaw j).trans hR))

theorem endpointCorrectionChart_pure_jet_bound (Ξ:AdmissibleCovariance) {r:ℕ}
    (p:ℕ) (qc:ℝ) (Q:ℝ) {theta:HighDegreeLowerParameter r}
    (hw:cutoffParameterAssembly (theta,Q)∈cutoffInputSmoothDomain Ξ p qc) (j:ℕ) {B R:ℝ}
    (hE:‖iteratedFDeriv ℝ j (fun u:HighDegreeLowerParameter r=>
      endpointTermExpression Ξ p (u.1,(u.2.1,(u.2.2,Q)))) theta‖ ≤ B)
    (hR:‖iteratedFDeriv ℝ j (lowerRecursionErrorRaw Ξ p qc)
      (cutoffParameterAssembly (theta,Q))‖ ≤ R) :
    ‖iteratedFDeriv ℝ j (fun u=>endpointCorrectionChart Ξ p qc (u,Q)) theta‖ ≤ B+R := by
  have hRaw := (contDiffOn_lowerRecursionErrorRaw Ξ p qc).contDiffAt
    ((isOpen_cutoffInputSmoothDomain Ξ p qc).mem_nhds hw)
  have hRc := hRaw.comp (theta,Q) cutoffParameterAssembly.contDiff.contDiffAt
  have hRi := hRc.comp theta (contDiffAt_id.prodMk contDiffAt_const)
  have hEi := (contDiff_endpointTermExpression Ξ p).contDiffAt.comp theta
    (show ContDiffAt ℝ ∞ (fun u:HighDegreeLowerParameter r=>cutoffParameterAssembly (u,Q)) theta by
      fun_prop)
  change ContDiffAt ℝ ∞ (fun u:HighDegreeLowerParameter r=>endpointTermExpression Ξ p
    (cutoffParameterAssembly (u,Q))) theta at hEi
  change ContDiffAt ℝ ∞ (fun u:HighDegreeLowerParameter r=>lowerRecursionErrorRaw Ξ p qc
    (cutoffParameterAssembly (u,Q))) theta at hRi
  change ‖iteratedFDeriv ℝ j (fun u=>endpointTermExpression Ξ p (cutoffParameterAssembly (u,Q))+
    lowerRecursionErrorRaw Ξ p qc (cutoffParameterAssembly (u,Q))) theta‖ ≤ _
  rw [fun_iteratedFDeriv_add_apply
    (hEi.of_le (by simp)) (hRi.of_le (by simp))]
  exact (norm_add_le _ _).trans (add_le_add hE
    ((norm_freeze_endpoint_jet_le Q hRc j).trans
      ((norm_iteratedFDeriv_comp_CLM_contraction cutoffParameterAssembly
        norm_cutoffParameterAssembly_le hRaw j).trans hR)))

end DepthPaper
