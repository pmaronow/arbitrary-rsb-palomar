module

public import GeneralDepthPaper.ReducedEndpointEnvelope

@[expose] public section


/-! The actual endpoint Hessian is strictly positive at the distinguished
contact when the top atom has positive mass. Local equality with the
smooth extension transfers both ordinary derivatives to the actual
Parisi functional. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 64

theorem endpointFunctional_second_derivative_at_contact (Ξ : AdmissibleCovariance)
    {r : ℕ} (p : ℕ) (hp : 4 ≤ p) (he : Even p) (hn : p∉Ξ.degrees)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) {m : ℝ} (hm : m∈Ioo (0:ℝ) 2)
    (lam : ℝ) (hlam : 0 < lam) (Q : Overlap) {qc : ℝ}
    (hc : atomicLocation z (Fin.last r) < qc) (hcQ : qc < (Q:ℝ)) (hQ1 : (Q:ℝ) < 1)
    (hzero : endpointRootEquation Ξ p qc ((z,(m,lam)),(Q:ℝ))=0) :
    HasDerivAt (deriv (fun q=>endpointFunctionalExtension Ξ p qc (z,(m,(lam,q)))))
      ((1-m)/2*highDegreeSecondExpression Ξ p (lam,(Q:ℝ))*
        deriv (fun q=>endpointRootEquation Ξ p qc ((z,(m,lam)),q)) Q) Q := by
  have hc0 : 0 < qc := (atomicLocation_mem_unit hz (Fin.last r)).1.trans_lt hc
  let g:ℝ→ℝ := fun q=>endpointFunctionalExtension Ξ p qc (z,(m,(lam,q)))
  let φ:ℝ→ℝ := fun q=>endpointRootEquation Ξ p qc ((z,(m,lam)),q)
  have harg : ∀ᶠq in 𝓝 (Q:ℝ),q∈Ioo qc 1 := Ioo_mem_nhds hcQ hQ1
  have hformula : deriv g=ᶠ[𝓝 (Q:ℝ)]
      (fun q=>(1-m)/2*highDegreeSecondExpression Ξ p (lam,q)*φ q) := by
    filter_upwards [harg] with q hq
    let T:Overlap := ⟨q,⟨hc0.le.trans hq.1.le,hq.2.le⟩⟩
    exact (hasDerivAt_endpointFunctionalExtension_endpoint Ξ p hp he hn z hz hm
      lam hlam T hc hq.1 hq.2).deriv
  have hcurv : DifferentiableAt ℝ (fun q=>highDegreeSecondExpression Ξ p (lam,q)) Q :=
    (((contDiff_highDegreeSecondExpression Ξ p).contDiffAt).comp (Q:ℝ)
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hmem := endpointRootSmoothDomain_mem Ξ p qc (z,(m,lam)) Q hz hc hm hlam.le hc0.le hcQ
  have hφ : DifferentiableAt ℝ φ Q :=
    (hasDerivAt_endpointRootEquation_endpoint Ξ p qc (z,(m,lam)) Q hmem).differentiableAt
  have hproduct := (hcurv.hasDerivAt.const_mul ((1-m)/2)).fun_mul hφ.hasDerivAt
  have hprod0 : HasDerivAt
      (fun q=>(1-m)/2*highDegreeSecondExpression Ξ p (lam,q)*φ q)
      ((1-m)/2*highDegreeSecondExpression Ξ p (lam,(Q:ℝ))*deriv φ Q) Q := by
    simpa only [Pi.mul_apply,show φ Q=0 from hzero,mul_zero,zero_add] using hproduct
  exact hprod0.congr_of_eventuallyEq hformula

theorem actual_endpoint_hessian_pos (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (hp : 4 ≤ p) (he : Even p) (hn : p∉Ξ.degrees)
    (z : AtomicPoint r) (hz : IsAtomicPoint z) {m : ℝ} (hm : m∈Ioo (0:ℝ) 1)
    (lam : ℝ) (hlam : 0 < lam) (Q : Overlap) {qc : ℝ}
    (hc : atomicLocation z (Fin.last r) < qc) (hcQ : qc < (Q:ℝ)) (hQ1 : (Q:ℝ) < 1)
    (hzero : endpointRootEquation Ξ p qc ((z,(m,lam)),(Q:ℝ))=0)
    (hder : 0 < deriv (fun q=>endpointRootEquation Ξ p qc ((z,(m,lam)),q)) Q) :
    0 < deriv (deriv (fun q=>twoLevelFunctional (Ξ.addHighDegree p hp he hn lam hlam)
      z hz m (projIcc 0 1 zero_le_one q))) Q := by
  have hc0 : 0 < qc := (atomicLocation_mem_unit hz (Fin.last r)).1.trans_lt hc
  have hd := endpointFunctional_second_derivative_at_contact Ξ p hp he hn z hz
    ⟨hm.1,hm.2.trans (by norm_num)⟩ lam hlam Q hc hcQ hQ1 hzero
  have hsame : (fun q=>endpointFunctionalExtension Ξ p qc (z,(m,(lam,q))))=ᶠ[𝓝 (Q:ℝ)]
      (fun q=>twoLevelFunctional (Ξ.addHighDegree p hp he hn lam hlam) z hz m
        (projIcc 0 1 zero_le_one q)) := by
    filter_upwards [Ioo_mem_nhds hcQ hQ1] with q hq
    let T:Overlap := projIcc 0 1 zero_le_one q
    have hTeq : (T:ℝ)=q := congrArg Subtype.val
      (projIcc_of_mem zero_le_one ⟨hc0.le.trans hq.1.le,hq.2.le⟩)
    have H := endpointFunctionalExtension_eq_actual Ξ p hp he hn z hz m ⟨hm.1,hm.2.le⟩
      lam hlam T hc (by rw [hTeq];exact hq.1.le)
    rw [hTeq] at H
    exact H
  rw [←hsame.deriv.deriv_eq,hd.deriv]
  have hcurv : 0 < highDegreeSecondExpression Ξ p (lam,(Q:ℝ)) := by
    rw [highDegreeSecondExpression,←Ξ.addHighDegree_second p hp he hn lam hlam Q]
    exact (Ξ.addHighDegree p hp he hn lam hlam).second_pos (hc0.trans hcQ)
  exact mul_pos (mul_pos (div_pos (sub_pos.mpr hm.2) (by norm_num)) hcurv) hder

end GeneralDepthPaper
