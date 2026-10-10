module

public import GeneralDepthPaper.ReducedEndpointFunctional

@[expose] public section


/-! The literal envelope identity is an actual chain-rule consequence of
stationarity in the endpoint coordinate. It holds for the smooth extension
at mass one as well as for positive top-atom mass. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

theorem fderiv_of_stationary_endpoint_composition
    {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f:E×ℝ→ℝ) (q:E→ℝ) (theta:E)
    (hf:DifferentiableAt ℝ f (theta,q theta)) (hq:DifferentiableAt ℝ q theta)
    (hzero:fderiv ℝ f (theta,q theta) (0,1)=0) :
    fderiv ℝ (fun u=>f (u,q u)) theta=
      (fderiv ℝ f (theta,q theta)).comp (ContinuousLinearMap.inl ℝ E ℝ) := by
  have hd := hf.hasFDerivAt.comp theta ((hasFDerivAt_id theta).prodMk hq.hasFDerivAt)
  have hd' : fderiv ℝ (fun u=>f (u,q u)) theta=
      (fderiv ℝ f (theta,q theta)).comp
        ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ q theta)) := by
    simpa only [Function.comp_def,id_eq] using hd.fderiv
  rw [hd']
  apply ContinuousLinearMap.ext
  intro v
  change fderiv ℝ f (theta,q theta) (v,fderiv ℝ q theta v)=
    fderiv ℝ f (theta,q theta) (v,0)
  rw [show (v,fderiv ℝ q theta v)=(v,0)+(fderiv ℝ q theta v) • (0,1) by simp,
    map_add,map_smul,hzero,smul_zero,add_zero]

theorem reducedEndpointFunctional_envelope (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (hp4 : 4 ≤ p) (he : Even p) (hn : p∉Ξ.degrees)
    (qc cQ CQ : ℝ) (hCQ : cQ < CQ) {theta : HighDegreeLowerParameter r}
    (hz : IsAtomicPoint theta.1) (hm : theta.2.1∈Ioo (0:ℝ) 2)
    (hlam : 0 < theta.2.2) (hc : atomicLocation theta.1 (Fin.last r) < qc)
    (htheta : theta∈distinguishedEndpointDomain Ξ p qc cQ CQ)
    (hrootunit : distinguishedEndpoint Ξ p qc cQ CQ theta∈Ioo qc 1) :
    fderiv ℝ (reducedEndpointFunctional Ξ p qc cQ CQ) theta=
      (fderiv ℝ (endpointFunctionalChart Ξ p qc)
        (theta,distinguishedEndpoint Ξ p qc cQ CQ theta)).comp
          (ContinuousLinearMap.inl ℝ (HighDegreeLowerParameter r) ℝ) := by
  have hs := distinguishedEndpoint_spec Ξ p qc cQ CQ hCQ (by omega) htheta
  have hc0 : 0 < qc := (atomicLocation_mem_unit hz (Fin.last r)).1.trans_lt hc
  let Q:Overlap := ⟨distinguishedEndpoint Ξ p qc cQ CQ theta,
    ⟨hc0.le.trans hrootunit.1.le,hrootunit.2.le⟩⟩
  have hmem := (htheta.1 _ (Ioo_subset_Icc_self hs.1)).1.1
  have hchart : ContDiffAt ℝ ∞ (endpointFunctionalChart Ξ p qc)
      (theta,distinguishedEndpoint Ξ p qc cQ CQ theta) :=
    (contDiffAt_endpointFunctionalExtension Ξ p qc hz hmem).comp _
      cutoffParameterAssembly.contDiff.contDiffAt
  have hd := hasDerivAt_endpointFunctionalExtension_endpoint Ξ p hp4 he hn theta.1 hz hm
    theta.2.2 hlam Q hc hrootunit.1 hrootunit.2
  have hd0 : HasDerivAt (fun q=>endpointFunctionalChart Ξ p qc (theta,q)) 0
      (distinguishedEndpoint Ξ p qc cQ CQ theta) := by
    simpa only [endpointFunctionalChart,Function.comp_def,cutoffParameterAssembly_apply,
      Q,hs.2.1,mul_zero] using hd
  have hzero : fderiv ℝ (endpointFunctionalChart Ξ p qc)
      (theta,distinguishedEndpoint Ξ p qc cQ CQ theta) (0,1)=0 :=
    (interval_partial_derivative_eq _ _ _ hchart).symm.trans hd0.deriv
  exact fderiv_of_stationary_endpoint_composition _ _ theta
    (hchart.differentiableAt (by simp)) (hs.2.2.differentiableAt (by simp)) hzero

theorem reducedEndpointFunctional_eq_actual (Ξ : AdmissibleCovariance) {r : ℕ}
    (p : ℕ) (hp : 4 ≤ p) (he : Even p) (hn : p∉Ξ.degrees)
    (qc cQ CQ : ℝ) (theta : HighDegreeLowerParameter r) (hz : IsAtomicPoint theta.1)
    (hm : theta.2.1∈Ioc (0:ℝ) 1) (hlam : 0 < theta.2.2)
    (hc : atomicLocation theta.1 (Fin.last r) < qc)
    (hq : distinguishedEndpoint Ξ p qc cQ CQ theta∈Icc (0:ℝ) 1)
    (hqc : qc ≤ distinguishedEndpoint Ξ p qc cQ CQ theta) :
    reducedEndpointFunctional Ξ p qc cQ CQ theta=
      twoLevelFunctional (Ξ.addHighDegree p hp he hn theta.2.2 hlam) theta.1 hz theta.2.1
        (distinguishedOverlap Ξ p qc cQ CQ theta) := by
  have H := endpointFunctionalExtension_eq_actual Ξ p hp he hn theta.1 hz theta.2.1 hm
    theta.2.2 hlam (distinguishedOverlap Ξ p qc cQ CQ theta) hc
      (by rw [distinguishedOverlap_coe Ξ p qc cQ CQ theta hq];exact hqc)
  rw [distinguishedOverlap_coe Ξ p qc cQ CQ theta hq] at H
  exact H

end GeneralDepthPaper
