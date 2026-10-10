module

public import DepthPaper.ReducedEndpointEnvelope
public import DepthPaper.AtomicGradient
public import DepthPaper.TwoLevelMassResponse

@[expose] public section


/-! The actual endpoint chart has the actual atomic and total-mass jets.
The total-mass identity includes mass one via the inward measure variation. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

theorem contDiffAt_endpointFunctionalChart_actual (Ξ : AdmissibleCovariance) {r:ℕ}
    (p:ℕ) (hp:4≤p) (he:Even p) (hn:p∉Ξ.degrees) (qc:ℝ)
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (m lam:ℝ)
    (hm:m∈Ioc (0:ℝ) 1) (hlam:0<lam) (Q:Overlap)
    (hc:atomicLocation z (Fin.last r)<qc) (hcQ:qc<(Q:ℝ)) (_hQ1:(Q:ℝ)<1) :
    ContDiffAt ℝ ∞ (endpointFunctionalChart Ξ p qc) ((z,(m,lam)),(Q:ℝ)) := by
  have hc0:0<qc := (atomicLocation_mem_unit hz (Fin.last r)).1.trans_lt hc
  have hW:0<endpointVarianceExpression Ξ p qc (lam,(Q:ℝ)) := by
    rw [←endpointVariance_eq_expression Ξ p hp he hn lam hlam qc Q]
    exact sub_pos.mpr ((Ξ.addHighDegree p hp he hn lam hlam).first_strictMonoOn
      hc0.le (hc0.trans hcQ).le hcQ)
  have hx:(z,(m,(lam,(Q:ℝ))))∈cutoffInputSmoothDomain Ξ p qc :=
    cutoffInputSmoothDomain_mem Ξ p _ hz hc
      ⟨hm.1,hm.2.trans_lt (by norm_num)⟩ hlam.le hW
  have houter:ContDiffAt ℝ ∞ (endpointFunctionalExtension Ξ p qc : CutoffInputParameter r→ℝ)
      (z,(m,(lam,(Q:ℝ)))) := contDiffAt_endpointFunctionalExtension Ξ p qc hz hx
  exact houter.comp ((z,(m,lam)),(Q:ℝ)) cutoffParameterAssembly.contDiff.contDiffAt

theorem endpointFunctionalChart_lower_direction (Ξ:AdmissibleCovariance) {r:ℕ}
    (p:ℕ) (hp:4≤p) (he:Even p) (hn:p∉Ξ.degrees) (qc:ℝ)
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (m lam:ℝ)
    (hm:m∈Ioc (0:ℝ) 1) (hlam:0<lam) (Q:Overlap)
    (hc:atomicLocation z (Fin.last r)<qc) (hcQ:qc<(Q:ℝ)) (hQ1:(Q:ℝ)<1)
    (v:AtomicPoint r) :
    fderiv ℝ (endpointFunctionalChart Ξ p qc) ((z,(m,lam)),(Q:ℝ)) ((v,(0,0)),0)=
      fderiv ℝ (partialAtomicFunctionalExtension (Ξ.addHighDegree p hp he hn lam hlam) r m Q) z v := by
  let Ψ:=Ξ.addHighDegree p hp he hn lam hlam
  have hch:=(contDiffAt_endpointFunctionalChart_actual Ξ p hp he hn qc z hz m lam hm hlam Q
    hc hcQ hQ1).differentiableAt (by simp)
  have hpF:=(contDiffAt_partialAtomicFunctionalExtension Ψ z hz m hm Q
    ⟨hc.trans hcQ,hQ1⟩).differentiableAt (by simp)
  have heq:(fun y:AtomicPoint r=>endpointFunctionalChart Ξ p qc ((y,(m,lam)),(Q:ℝ)))=ᶠ[𝓝 z]
      partialAtomicFunctionalExtension Ψ r m Q := by
    have hnear:∀ᶠy in 𝓝 z,atomicLocation y (Fin.last r)<qc :=
      (isOpen_lt (continuous_atomicLocation (Fin.last r)) continuous_const).mem_nhds hc
    filter_upwards [(isOpen_atomic_domain r).mem_nhds hz,hnear] with y hy hyc
    change endpointFunctionalExtension Ξ p qc (y,(m,(lam,(Q:ℝ))))=_
    rw [endpointFunctionalExtension_eq_actual Ξ p hp he hn y hy m hm lam hlam Q hyc hcQ.le]
    simp only [partialAtomicFunctionalExtension,partialAtomicMeasureExtension_eq y hy,
      twoLevelFunctional,twoLevelMeasure,Ψ]
  have hi:HasFDerivAt (fun y:AtomicPoint r=>((y,(m,lam)),(Q:ℝ)))
      (((ContinuousLinearMap.id ℝ (AtomicPoint r)).prod 0).prod 0) z :=
    ((hasFDerivAt_id z).prodMk (hasFDerivAt_const (m,lam) z)).prodMk
      (hasFDerivAt_const (Q:ℝ) z)
  have hd:=hch.hasFDerivAt.comp z hi
  have hd':=hpF.hasFDerivAt.congr_of_eventuallyEq heq
  have H:=congrArg (fun L:AtomicPoint r→L[ℝ]ℝ=>L v) (hd.unique hd')
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,zero_apply] at H
  exact H

theorem endpointFunctionalChart_mass_direction (Ξ:AdmissibleCovariance) {r:ℕ}
    (p:ℕ) (hp:4≤p) (he:Even p) (hn:p∉Ξ.degrees) (qc:ℝ)
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (m lam:ℝ)
    (hm:m∈Ioc (0:ℝ) 1) (hlam:0<lam) (Q:Overlap)
    (hc:atomicLocation z (Fin.last r)<qc) (hcQ:qc<(Q:ℝ)) (hQ1:(Q:ℝ)<1) :
    fderiv ℝ (endpointFunctionalChart Ξ p qc) ((z,(m,lam)),(Q:ℝ)) ((0,(1,0)),0)=
      firstVariation (Ξ.addHighDegree p hp he hn lam hlam) (twoLevelMeasure z hz m Q) Q-
        ∫q:Overlap,firstVariation (Ξ.addHighDegree p hp he hn lam hlam)
          (twoLevelMeasure z hz m Q) q ∂(atomicMeasure z hz : Measure Overlap) := by
  let Ψ:=Ξ.addHighDegree p hp he hn lam hlam
  have hch:=(contDiffAt_endpointFunctionalChart_actual Ξ p hp he hn qc z hz m lam hm hlam Q
    hc hcQ hQ1).differentiableAt (by simp)
  have hi:HasDerivAt (fun s:ℝ=>((z,(s,lam)),(Q:ℝ))) ((0,(1,0)),0) m :=
    ((hasDerivAt_const m z).prodMk ((hasDerivAt_id m).prodMk
      (hasDerivAt_const m lam))).prodMk (hasDerivAt_const m (Q:ℝ))
  apply smooth_twoLevel_mass_response Ψ z hz m hm Q _ _
    (hch.hasFDerivAt.comp_hasDerivAt m hi)
  intro s hs
  exact endpointFunctionalExtension_eq_actual Ξ p hp he hn z hz s hs lam hlam Q hc hcQ.le

end DepthPaper
