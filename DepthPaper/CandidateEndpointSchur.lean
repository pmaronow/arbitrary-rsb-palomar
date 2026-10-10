module

public import DepthPaper.CandidateEndpointCoordinates
public import DepthPaper.StationaryReducedHessian
public import DepthPaper.EndpointPureHessian

@[expose] public section


/-! Elimination of the actual distinguished endpoint, followed by transfer
through the genuine full atomic chart. Conditional calculus intermediates
are specialized to the proved actual candidate below. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 64

def endpointSwappedAssembly {r:ℕ} : (ℝ×(AtomicPoint r×ℝ))→L[ℝ](HighDegreeLowerParameter r×ℝ) where
  toFun v:=((v.2.1,(v.2.2,0)),v.1)
  map_add' _ _:=by ext <;> simp
  map_smul' _ _:=by ext <;> simp
  cont:=by fun_prop

def endpointSwap {r:ℕ} : TwoLevelAtomicPoint r→L[ℝ](ℝ×(AtomicPoint r×ℝ)) where
  toFun v:=(v.2.2,(v.1,v.2.1))
  map_add' _ _:=rfl
  map_smul' _ _:=rfl
  cont:=by fun_prop

def candidateEndpointSwapped (Ξ:AdmissibleCovariance) {r:ℕ} (p:ℕ) (qc lam:ℝ)
    (v:ℝ×(AtomicPoint r×ℝ)) : ℝ :=
  candidateEndpointFunctional Ξ p qc lam (v.2.1,v.2.2,v.1)

theorem candidateEndpoint_atomic_hessian_pos_from_reduced (Ξ:AdmissibleCovariance) {r:ℕ}
    (p:ℕ) (hp:4≤p) (he:Even p) (hn:p∉Ξ.degrees) (qc cQ CQ lam:ℝ) (hCQ:cQ<CQ)
    (hlam:0<lam) (z:AtomicPoint r) (hz:IsAtomicPoint z) (m:ℝ) (hm:m∈Ioo (0:ℝ) 1)
    (hc:atomicLocation z (Fin.last r)<qc)
    (hdom:(z,(m,lam))∈distinguishedEndpointDomain Ξ p qc cQ CQ)
    (hunit:distinguishedEndpoint Ξ p qc cQ CQ (z,(m,lam))∈Ioo qc 1)
    (hredpos:∀v:AtomicPoint r×ℝ,v≠0→0<fderiv ℝ
      (fderiv ℝ (fixedCouplingReducedObjective Ξ p qc cQ CQ lam)) (z,m) v v)
    (hredcrit:fderiv ℝ (fixedCouplingReducedObjective Ξ p qc cQ CQ lam) (z,m)=0) :
    let Q:=distinguishedEndpoint Ξ p qc cQ CQ (z,(m,lam))
    ∀v:AtomicPoint (r+1),v≠0→0<fderiv ℝ
      (fderiv ℝ (atomicFunctionalExtension (Ξ.addHighDegree p hp he hn lam hlam) (r+1)))
      (twoLevelAtomicCoordinates (z,m,Q)) v v := by
  let eta:HighDegreeLowerParameter r:=(z,(m,lam))
  let Q:=distinguishedEndpoint Ξ p qc cQ CQ eta
  let y:AtomicPoint r×ℝ:=(z,m)
  let q:AtomicPoint r×ℝ→ℝ:=fun u=>distinguishedEndpoint Ξ p qc cQ CQ (u.1,(u.2,lam))
  let f:=candidateEndpointSwapped Ξ (r:=r) p qc lam
  let C:=endpointFunctionalChart Ξ (r:=r) p qc
  have hc0:0<qc := (atomicLocation_mem_unit hz (Fin.last r)).1.trans_lt hc
  let QT:Overlap:=⟨Q,⟨hc0.le.trans hunit.1.le,hunit.2.le⟩⟩
  have hC:ContDiffAt ℝ 2 C (eta,Q) :=
    (contDiffAt_endpointFunctionalChart_actual Ξ p hp he hn qc z hz m lam
      ⟨hm.1,hm.2.le⟩ hlam QT hc hunit.1 hunit.2).of_le (by simp)
  have hAs:∀v:ℝ×(AtomicPoint r×ℝ),
      (((0:AtomicPoint r),(0,lam)),(0:ℝ))+endpointSwappedAssembly v=
        ((v.2.1,(v.2.2,lam)),v.1) := by intro v;ext <;> simp [endpointSwappedAssembly]
  have hfAs:(fun v:ℝ×(AtomicPoint r×ℝ)=>C ((((0:AtomicPoint r),(0,lam)),(0:ℝ))+endpointSwappedAssembly v))=f := by
    funext v
    rw [hAs]
    rfl
  have hf:ContDiffAt ℝ 2 f (q y,y) :=
    hC.comp (g:=C) (f:=fun v:ℝ×(AtomicPoint r×ℝ)=>((v.2.1,(v.2.2,lam)),v.1)) (q y,y)
      ((contDiffAt_snd.fst.prodMk (contDiffAt_snd.snd.prodMk contDiffAt_const)).prodMk contDiffAt_fst)
  have hspec:=distinguishedEndpoint_spec Ξ p qc cQ CQ hCQ (by omega) hdom
  have hq:ContDiffAt ℝ 2 q y :=
    (hspec.2.2.comp y (contDiffAt_fst.prodMk (contDiffAt_snd.prodMk contDiffAt_const))).of_le (by simp)
  have hQzero:∀ᶠu in 𝓝 y,∀v:ℝ,fderiv ℝ f (q u,u) (v,0)=0 := by
    have hgraph:ContinuousAt (fun u:AtomicPoint r×ℝ=>(u.1,(u.2,lam))) y := by fun_prop
    have hdnear:∀ᶠu in 𝓝 y,(u.1,(u.2,lam))∈distinguishedEndpointDomain Ξ p qc cQ CQ :=
      hgraph.eventually ((isOpen_distinguishedEndpointDomain Ξ p qc cQ CQ hCQ (by omega)).mem_nhds hdom)
    have hcut:∀ᶠu in 𝓝 y,atomicLocation u.1 (Fin.last r)<qc :=
      (((continuous_atomicLocation (Fin.last r)).comp continuous_fst).continuousAt
        (x:=y)).eventually (isOpen_Iio.mem_nhds hc)
    have hvalid:∀ᶠu in 𝓝 y,IsAtomicPoint u.1 :=
      (show ContinuousAt (fun u:AtomicPoint r×ℝ=>u.1) y by fun_prop).eventually
        ((isOpen_atomic_domain r).mem_nhds hz)
    have hmass:∀ᶠu in 𝓝 y,u.2∈Ioo (0:ℝ) 1 :=
      (show ContinuousAt (fun u:AtomicPoint r×ℝ=>u.2) y by fun_prop).eventually (isOpen_Ioo.mem_nhds hm)
    have hqunit:∀ᶠu in 𝓝 y,q u∈Ioo qc 1 := hq.continuousAt.eventually (isOpen_Ioo.mem_nhds hunit)
    filter_upwards [hdnear,hcut,hvalid,hmass,hqunit] with u hdu hcu hzu hmu hqu
    have hCu:ContDiffAt ℝ 2 C ((u.1,(u.2,lam)),q u) :=
      (contDiffAt_endpointFunctionalChart_actual Ξ p hp he hn qc u.1 hzu u.2 lam
        ⟨hmu.1,hmu.2.le⟩ hlam
        ⟨q u,⟨hc0.le.trans hqu.1.le,hqu.2.le⟩⟩ hcu hqu.1 hqu.2).of_le (by simp)
    have hd:HasFDerivAt f ((fderiv ℝ C ((u.1,(u.2,lam)),q u)).comp endpointSwappedAssembly) (q u,u) := by
      have hi:=(endpointSwappedAssembly.hasFDerivAt (x:=(q u,u))).const_add
        (((0:AtomicPoint r),(0,lam)),(0:ℝ))
      have hCa:HasFDerivAt C (fderiv ℝ C ((u.1,(u.2,lam)),q u))
          ((((0:AtomicPoint r),(0,lam)),(0:ℝ))+endpointSwappedAssembly (q u,u)) := by
        rw [hAs]
        exact (hCu.differentiableAt (by norm_num)).hasFDerivAt
      have H:=hCa.comp (q u,u) hi
      rw [show C ∘ (fun v=>(((0:AtomicPoint r),(0,lam)),(0:ℝ))+endpointSwappedAssembly v)=f from hfAs] at H
      simpa only [hAs] using H
    have hz1:=endpointFunctionalChart_pureQ_stationary Ξ p hp he hn qc cQ CQ hCQ u.1 hzu u.2
      ⟨hmu.1,hmu.2.trans (by norm_num)⟩ lam hlam hcu hdu hqu
    intro v
    rw [hd.fderiv]
    change fderiv ℝ C ((u.1,(u.2,lam)),q u) (0,v)=0
    have heq:(0,v)=v • ((0:HighDegreeLowerParameter r),(1:ℝ)) := by simp
    rw [heq,map_smul,hz1,smul_zero]
  have hA:∀v:ℝ,v≠0→0<fderiv ℝ (fderiv ℝ f) (q y,y) (v,0) (v,0) := by
    intro v hv
    have H:=scalar_hessian_affine (f:=C) endpointSwappedAssembly
      (((0:AtomicPoint r),(0,lam)),(0:ℝ)) (q y,y) (by simpa only [hAs] using hC) (v,0) (v,0)
    have hdir:endpointSwappedAssembly ((v,0):ℝ×(AtomicPoint r×ℝ))=
        ((0:HighDegreeLowerParameter r),v) := by ext <;> simp [endpointSwappedAssembly]
    rw [hfAs,hAs,hdir] at H
    have HE:fderiv ℝ (fderiv ℝ f) (q y,y) (v,0) (v,0)=
        fderiv ℝ (fderiv ℝ C) (eta,Q) (0,v) (0,v) := H
    rw [HE]
    exact endpointFunctionalChart_pureQ_hessian_pos Ξ p hp he hn qc cQ CQ hCQ z hz m hm lam hlam hc hdom hunit v hv
  have hredEq:(fun u=>f (q u,u))=fixedCouplingReducedObjective Ξ p qc cQ CQ lam := rfl
  have hFullPos:∀v:ℝ×(AtomicPoint r×ℝ),v≠0→0<fderiv ℝ (fderiv ℝ f) (q y,y) v v :=
    stationary_full_hessian_positive hf hq hQzero hA (by simpa only [hredEq,y] using hredpos)
  have hFullCrit:fderiv ℝ f (q y,y)=0 :=
    stationary_full_gradient_zero (hf.differentiableAt (by norm_num))
      (hq.differentiableAt (by norm_num)) hQzero.self_of_nhds (by simpa only [hredEq,y] using hredcrit)
  have hcomp:candidateEndpointFunctional Ξ p qc lam=f ∘ endpointSwap := rfl
  have hPos:∀v:TwoLevelAtomicPoint r,v≠0→0<fderiv ℝ
      (fderiv ℝ (candidateEndpointFunctional Ξ p qc lam)) (z,m,Q) v v := by
    intro v hv
    have hswap:endpointSwap v≠0 := by
      intro heq
      apply hv
      apply Prod.ext
      · exact congrArg (fun u:ℝ×(AtomicPoint r×ℝ)=>u.2.1) heq
      · apply Prod.ext
        · exact congrArg (fun u:ℝ×(AtomicPoint r×ℝ)=>u.2.2) heq
        · exact congrArg (fun u:ℝ×(AtomicPoint r×ℝ)=>u.1) heq
    have H:=scalar_hessian_affine (f:=f) endpointSwap 0 (z,m,Q) (by simpa only [zero_add,endpointSwap,ContinuousLinearMap.coe_mk',LinearMap.coe_mk,AddHom.coe_mk,q,y,Q,eta] using hf) v v
    simp only [zero_add] at H
    rw [hcomp]
    have HE:fderiv ℝ (fderiv ℝ (f ∘ endpointSwap)) (z,m,Q) v v=
        fderiv ℝ (fderiv ℝ f) (endpointSwap (z,m,Q)) (endpointSwap v) (endpointSwap v) := by
      simpa only [Function.comp_def] using H
    rw [HE]
    exact hFullPos (endpointSwap v) hswap
  have hCrit:fderiv ℝ (candidateEndpointFunctional Ξ p qc lam) (z,m,Q)=0 := by
    have hfs:DifferentiableAt ℝ f (endpointSwap (z,m,Q)) := by
      simpa only [endpointSwap,ContinuousLinearMap.coe_mk',LinearMap.coe_mk,AddHom.coe_mk,q,y,Q,eta] using
        hf.differentiableAt (by norm_num)
    rw [hcomp,fderiv_comp (f:=endpointSwap) (g:=f) (z,m,Q) hfs endpointSwap.differentiableAt]
    rw [endpointSwap.hasFDerivAt.fderiv]
    have hpoint:endpointSwap (z,m,Q)=(q y,y) := rfl
    rw [hpoint,hFullCrit]
    ext v <;> simp
  let Ψ:=Ξ.addHighDegree p hp he hn lam hlam
  have hv:=isAtomicPoint_twoLevelCoordinates z hz m Q hm (hc.trans hunit.1) hunit.2
  have hsmooth:ContDiffAt ℝ 2 (atomicFunctionalExtension Ψ (r+1)) (twoLevelAtomicCoordinates (z,m,Q)) :=
    (contDiffAt_atomicFunctionalExtension Ψ _ hv).of_le (by simp)
  have heq:=candidateEndpointFunctional_eventuallyEq_atomic Ξ p hp he hn qc lam hlam z hz m hm Q hc hunit.1 hunit.2
  have hcActual:fderiv ℝ (atomicFunctionalExtension Ψ (r+1) ∘ twoLevelAtomicCoordinates) (z,m,Q)=0 :=
    heq.fderiv_eq.symm.trans hCrit
  apply (twoLevelAtomic_hessian_positive_iff _ (z,m,Q) hm.1.ne' hsmooth hcActual).1
  intro v hv
  rw [←heq.fderiv.fderiv_eq]
  exact hPos v hv

end DepthPaper
