module

public import DepthPaper.EndpointFunctionalHessian
public import DepthPaper.StationaryScalarHessian

@[expose] public section


/-! The full endpoint chart's pure endpoint Hessian is genuinely
positive at the constructed root whenever its atom has positive mass. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 64

theorem endpointFunctionalChart_pureQ_stationary (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (hp : 4≤p) (he : Even p) (hn : p∉Ξ.degrees)
    (qc cQ CQ : ℝ) (hCQ : cQ<CQ) (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (m : ℝ) (hm : m∈Ioo (0:ℝ) 2) (lam : ℝ) (hlam : 0<lam)
    (hc : atomicLocation z (Fin.last r)<qc)
    (hdom : (z,(m,lam))∈distinguishedEndpointDomain Ξ p qc cQ CQ)
    (hunit : distinguishedEndpoint Ξ p qc cQ CQ (z,(m,lam))∈Ioo qc 1) :
    fderiv ℝ (endpointFunctionalChart Ξ p qc)
      ((z,(m,lam)),distinguishedEndpoint Ξ p qc cQ CQ (z,(m,lam))) (0,1)=0 := by
  let eta : HighDegreeLowerParameter r:=(z,(m,lam))
  let q:=distinguishedEndpoint Ξ p qc cQ CQ eta
  have hs:=distinguishedEndpoint_spec Ξ p qc cQ CQ hCQ (by omega) hdom
  have hmem := (hdom.1 q (Ioo_subset_Icc_self hs.1)).1.1
  have hchart : ContDiffAt ℝ ∞ (endpointFunctionalChart Ξ p qc) (eta,q) :=
    (contDiffAt_endpointFunctionalExtension Ξ p qc hz hmem).comp _
      cutoffParameterAssembly.contDiff.contDiffAt
  have hc0:0<qc:=(atomicLocation_mem_unit hz (Fin.last r)).1.trans_lt hc
  let Q : Overlap:=⟨q,⟨hc0.le.trans hunit.1.le,hunit.2.le⟩⟩
  have hd:=hasDerivAt_endpointFunctionalExtension_endpoint Ξ p hp he hn z hz hm
    lam hlam Q hc hunit.1 hunit.2
  have heq : endpointRootEquation Ξ p qc ((z,(m,lam)),(Q:ℝ))=0:=hs.2.1
  rw [heq,mul_zero] at hd
  rw [←interval_partial_derivative_eq _ eta q hchart]
  exact hd.deriv

theorem endpointFunctionalChart_pureQ_hessian_pos (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (hp : 4≤p) (he : Even p) (hn : p∉Ξ.degrees)
    (qc cQ CQ : ℝ) (hCQ : cQ<CQ) (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (m : ℝ) (hm : m∈Ioo (0:ℝ) 1) (lam : ℝ) (hlam : 0<lam)
    (hc : atomicLocation z (Fin.last r)<qc)
    (hdom : (z,(m,lam))∈distinguishedEndpointDomain Ξ p qc cQ CQ)
    (hunit : distinguishedEndpoint Ξ p qc cQ CQ (z,(m,lam))∈Ioo qc 1) :
    ∀v:ℝ,v≠0 → 0<fderiv ℝ (fderiv ℝ (endpointFunctionalChart Ξ p qc))
      ((z,(m,lam)),distinguishedEndpoint Ξ p qc cQ CQ (z,(m,lam))) (0,v) (0,v) := by
  let eta : HighDegreeLowerParameter r:=(z,(m,lam))
  let q:=distinguishedEndpoint Ξ p qc cQ CQ eta
  let f:=endpointFunctionalChart (r:=r) Ξ p qc
  have hs:=distinguishedEndpoint_spec Ξ p qc cQ CQ hCQ (by omega) hdom
  have hmem := (hdom.1 q (Ioo_subset_Icc_self hs.1)).1.1
  have hchart : ContDiffAt ℝ ∞ f (eta,q) :=
    (contDiffAt_endpointFunctionalExtension Ξ p qc hz hmem).comp _
      cutoffParameterAssembly.contDiff.contDiffAt
  have hc0:0<qc:=(atomicLocation_mem_unit hz (Fin.last r)).1.trans_lt hc
  let Q : Overlap:=⟨q,⟨hc0.le.trans hunit.1.le,hunit.2.le⟩⟩
  let a : ℝ:=(1-m)/2*highDegreeSecondExpression Ξ p (lam,q)*
    deriv (fun y=>endpointRootEquation Ξ p qc (eta,y)) q
  have hd : HasDerivAt (deriv (fun y=>f (eta,y))) a q := by
    exact endpointFunctional_second_derivative_at_contact Ξ p hp he hn z hz
      ⟨hm.1,hm.2.trans (by norm_num)⟩ lam hlam Q hc hunit.1 hunit.2 hs.2.1
  have hder : 0<deriv (fun y=>endpointRootEquation Ξ p qc (eta,y)) q :=
    intervalRootDomain_partial_pos _ _ (isOpen_endpointRootSmoothDomain Ξ p qc)
      (contDiffOn_endpointRootEquation Ξ p qc) hdom (Ioo_subset_Icc_self hs.1)
  have hcurv : 0<highDegreeSecondExpression Ξ p (lam,q) := by
    rw [highDegreeSecondExpression,←Ξ.addHighDegree_second p hp he hn lam hlam q]
    exact (Ξ.addHighDegree p hp he hn lam hlam).second_pos (hc0.trans hunit.1)
  have ha : 0<a:=mul_pos (mul_pos (div_pos (sub_pos.mpr hm.2) (by norm_num)) hcurv) hder
  have hslice : ContDiffAt ℝ 2 (fun y=>f (eta,y)) q :=
    (hchart.of_le (by simp)).comp q (contDiffAt_const.prodMk contDiffAt_id)
  intro v hv
  have H:=scalar_hessian_affine (ContinuousLinearMap.inr ℝ (HighDegreeLowerParameter r) ℝ)
    (eta,0) q (by simpa using hchart.of_le (show (2:WithTop ℕ∞)≤∞ by simp)) v v
  have HE : fderiv ℝ (fderiv ℝ (fun y=>f (eta,y))) q v v=
      fderiv ℝ (fderiv ℝ f) (eta,q) (0,v) (0,v) := by
    simpa only [ContinuousLinearMap.inr_apply,Prod.mk_add_mk,add_zero,zero_add] using H
  change 0<fderiv ℝ (fderiv ℝ f) (eta,q) (0,v) (0,v)
  rw [←HE,scalar_hessian_from_response hslice hd v]
  exact mul_pos (sq_pos_of_ne_zero hv) ha

end DepthPaper
