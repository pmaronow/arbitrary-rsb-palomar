module

public import DepthPaper.StationaryScalarHessian
public import DepthPaper.EndpointChartContacts
public import DepthPaper.TwoLevelCriticalHessian
public import DepthPaper.TwoLevelAtomicMeasureChart

@[expose] public section


/-! Genuine local equality of the endpoint chart with the physical atomic
functional. The mass-one equality uses the disappearing top atom. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 64

def candidateEndpointFunctional (Ξ:AdmissibleCovariance) {r:ℕ}
    (p:ℕ) (qc lam:ℝ) (v:TwoLevelAtomicPoint r) : ℝ :=
  endpointFunctionalChart Ξ p qc ((v.1,(v.2.1,lam)),v.2.2)

theorem candidateEndpointFunctional_eventuallyEq_atomic (Ξ:AdmissibleCovariance) {r:ℕ}
    (p:ℕ) (hp:4≤p) (he:Even p) (hn:p∉Ξ.degrees) (qc lam:ℝ) (hlam:0<lam)
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (m:ℝ) (hm:m∈Ioo (0:ℝ) 1)
    (Q:ℝ) (hc:atomicLocation z (Fin.last r)<qc) (hcQ:qc<Q) (hQ1:Q<1) :
    candidateEndpointFunctional Ξ p qc lam=ᶠ[𝓝 (z,m,Q)]
      (atomicFunctionalExtension (Ξ.addHighDegree p hp he hn lam hlam) (r+1) ∘ twoLevelAtomicCoordinates) := by
  have hc0:0<qc := (atomicLocation_mem_unit hz (Fin.last r)).1.trans_lt hc
  have h1:∀ᶠv:TwoLevelAtomicPoint r in 𝓝 (z,m,Q),IsAtomicPoint v.1 :=
    (show ContinuousAt (fun v:TwoLevelAtomicPoint r=>v.1) (z,m,Q) by fun_prop).eventually
      ((isOpen_atomic_domain r).mem_nhds hz)
  have h2:∀ᶠv:TwoLevelAtomicPoint r in 𝓝 (z,m,Q),v.2.1∈Ioo (0:ℝ) 1 :=
    (show ContinuousAt (fun v:TwoLevelAtomicPoint r=>v.2.1) (z,m,Q) by fun_prop).eventually
      (isOpen_Ioo.mem_nhds hm)
  have h3c:ContinuousAt (fun v:TwoLevelAtomicPoint r=>atomicLocation v.1 (Fin.last r)) (z,m,Q) :=
    ((continuous_atomicLocation (Fin.last r)).comp continuous_fst).continuousAt
  have h3:∀ᶠv:TwoLevelAtomicPoint r in 𝓝 (z,m,Q),atomicLocation v.1 (Fin.last r)<qc :=
    h3c.eventually
      (isOpen_Iio.mem_nhds hc)
  have h4:∀ᶠv:TwoLevelAtomicPoint r in 𝓝 (z,m,Q),v.2.2∈Ioo qc 1 :=
    (show ContinuousAt (fun v:TwoLevelAtomicPoint r=>v.2.2) (z,m,Q) by fun_prop).eventually
      (isOpen_Ioo.mem_nhds ⟨hcQ,hQ1⟩)
  have hnear:=h1.and (h2.and (h3.and h4))
  filter_upwards [hnear] with v hv
  let T:Overlap:=⟨v.2.2,⟨hc0.le.trans hv.2.2.2.1.le,hv.2.2.2.2.le⟩⟩
  have hvalid:=isAtomicPoint_twoLevelCoordinates v.1 hv.1 v.2.1 v.2.2 hv.2.1
    (hv.2.2.1.trans hv.2.2.2.1) hv.2.2.2.2
  change candidateEndpointFunctional Ξ p qc lam v=
    atomicFunctionalExtension _ _ (twoLevelAtomicCoordinates (v.1,v.2.1,v.2.2))
  rw [atomicFunctionalExtension_eq _ _ hvalid]
  rw [atomicMeasure_twoLevelCoordinates _ hv.1 _ hv.2.1 T
      (hv.2.2.1.trans hv.2.2.2.1) hv.2.2.2.2]
  exact endpointFunctionalExtension_eq_actual Ξ p hp he hn v.1 hv.1 v.2.1
    ⟨hv.2.1.1,hv.2.1.2.le⟩ lam hlam T hv.2.2.1 hv.2.2.2.1.le

theorem reduced_mass_one_eventuallyEq_atomic (Ξ:AdmissibleCovariance) {r:ℕ}
    (p:ℕ) (hp:4≤p) (he:Even p) (hn:p∉Ξ.degrees) (qc cQ CQ lam:ℝ)
    (hCQ:cQ<CQ) (hlam:0<lam) (z:AtomicPoint r) (hz:IsAtomicPoint z)
    (hc:atomicLocation z (Fin.last r)<qc)
    (hdom:(z,(1,lam))∈distinguishedEndpointDomain Ξ p qc cQ CQ)
    (hunit:distinguishedEndpoint Ξ p qc cQ CQ (z,(1,lam))∈Ioo qc 1) :
    (fun y:AtomicPoint r=>reducedEndpointFunctional Ξ p qc cQ CQ (y,(1,lam)))=ᶠ[𝓝 z]
      atomicFunctionalExtension (Ξ.addHighDegree p hp he hn lam hlam) r := by
  have hc0:0<qc := (atomicLocation_mem_unit hz (Fin.last r)).1.trans_lt hc
  have hq:=((distinguishedEndpoint_spec Ξ p qc cQ CQ hCQ (by omega) hdom).2.2).continuousAt
  have hgraph:ContinuousAt (fun y:AtomicPoint r=>(y,((1,lam):ℝ×ℝ))) z := by fun_prop
  have hnearQ:∀ᶠy in 𝓝 z,distinguishedEndpoint Ξ p qc cQ CQ (y,(1,lam))∈Ioo qc 1 :=
    (hq.comp (f:=fun y:AtomicPoint r=>(y,((1,lam):ℝ×ℝ))) hgraph).eventually (isOpen_Ioo.mem_nhds hunit)
  have hnearcut:∀ᶠy in 𝓝 z,atomicLocation y (Fin.last r)<qc :=
    (continuous_atomicLocation (Fin.last r)).continuousAt.eventually (isOpen_Iio.mem_nhds hc)
  filter_upwards [(isOpen_atomic_domain r).mem_nhds hz,hnearQ,hnearcut] with y hy hQ hyc
  let T:Overlap:=⟨distinguishedEndpoint Ξ p qc cQ CQ (y,(1,lam)),
    ⟨hc0.le.trans hQ.1.le,hQ.2.le⟩⟩
  change endpointFunctionalExtension Ξ p qc (y,(1,(lam,(T:ℝ))))=_
  rw [endpointFunctionalExtension_eq_actual Ξ p hp he hn y hy 1 ⟨by norm_num,le_rfl⟩ lam hlam T hyc hQ.1.le]
  simp only [twoLevelFunctional,twoLevelMeasure,partialAtomicMeasure,Paper.parisiMix_one,
    atomicFunctionalExtension_eq _ _ hy]

end DepthPaper
