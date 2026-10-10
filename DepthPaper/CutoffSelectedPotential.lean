module

public import DepthPaper.CutoffTerminal
public import DepthPaper.ColeHopfChainClosed
public import FourPapersCommon.MixedScalarTransition

@[expose] public section


/-! The selected mixed potential below the cutoff is the genuine finite
truncated recursion with terminal χ. Grid boundaries and zero upper mass
are retained. This proves the potential and first two spatial jets in 4.1(b). -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff
namespace DepthPaper
open ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

theorem parisiCDF_twoLevelMeasure_below_top {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) {q : ℝ} (hq : q<(Q:ℝ)) :
    Paper.parisiCDF (twoLevelMeasure z hz m Q) q=
      m*Paper.parisiCDF (atomicMeasure z hz) q := by
  rw [parisiCDF_twoLevelMeasure z hz m hm Q q,ite_eq_right (not_le_of_gt hq)]
  ring

theorem parisiCDF_twoLevelMeasure_cutoff_cell {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc)
    (hcQ : qc≤(Q:ℝ)) (i : Fin (r+1)) {q : ℝ}
    (hq : q∈Ico (cutoffAtomicNode z qc i.castSucc) (cutoffAtomicNode z qc i.succ)) :
    Paper.parisiCDF (twoLevelMeasure z hz m Q) q=m*atomicLevel z i := by
  have hqQ : q<(Q:ℝ) := lt_of_lt_of_le hq.2
    ((cutoffAtomicNode_mem z hz qc hc i.succ).2.trans hcQ)
  rw [parisiCDF_twoLevelMeasure_below_top z hz m hm Q hqQ]
  congr 1
  apply parisiCDF_atomicMeasure_cell z hz i
  refine ⟨by simpa only [atomicNode_castSucc,cutoffAtomicNode_castSucc] using hq.1,?_⟩
  have hupper : cutoffAtomicNode z qc i.succ≤atomicNode z i.succ := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.succ_last,cutoffAtomicNode_last,atomicNode_last] using
        hcQ.trans Q.property.2
    · rw [Fin.succ_castSucc,cutoffAtomicNode_castSucc,atomicNode_castSucc]
  exact hq.2.trans_le hupper

def cutoffCandidateData (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc)
    (hcQ : qc≤(Q:ℝ)) : TruncatedParisiData r qc :=
  cutoffTruncatedData Ξ z hz m hm qc hc (cutoffTerminal m (Ξ.first Q-Ξ.first qc))
    (norm_terminalJet_cutoffTerminal_le_one m _ (sub_nonneg.mpr
      (Ξ.first_strictMonoOn.monotoneOn (cutoff_pos z hz qc hc).le Q.property.1 hcQ)))

theorem potential_twoLevelMeasure_eq_cutoff (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc)
    (hcQ : qc≤(Q:ℝ)) (q : ℝ) (hq : q∈Icc (0:ℝ) qc) (x : ℝ) :
    potential Ξ (twoLevelMeasure z hz m Q) q x-cutoffCandidateConstant Ξ m Q qc=
      (cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).potential q x := by
  let d:=cutoffCandidateData Ξ z hz m hm Q qc hc hcQ
  let p:=d.parameter
  let qI:TruncatedClockDomain qc:=⟨q,hq⟩
  let ν:=twoLevelMeasure z hz m Q
  let k:=cutoffCandidateConstant Ξ m Q qc
  let u:Fin (r+2)→ℝ→ℝ:=fun i y=>potential Ξ ν (max q (cutoffAtomicNode z qc i)) y-k
  have hfirst : ∀a:TruncatedClockDomain qc,p.1 a=Ξ.first a := by
    intro a
    exact cutoffCovarianceJetMap_one Ξ qc a
  have hnode : ∀i:Fin (r+2),(p.2.1 i:ℝ)=cutoffAtomicNode z qc i := fun _=>rfl
  have hlevel : ∀i:Fin (r+1),p.2.2.1 i=m*atomicLevel z i := fun _=>rfl
  have hstep (i : Fin (r+1)) (y : ℝ) :
      u i.castSucc y=coleHopf (truncatedStepData p qI i).1
        (truncatedStepData p qI i).2.toNNReal (u i.succ) y := by
    by_cases hqi : cutoffAtomicNode z qc i.succ≤q
    · have hlow : cutoffAtomicNode z qc i.castSucc≤q :=
        ((cutoffAtomicNode_strictMono z hz qc hc).monotone i.castSucc_lt_succ.le).trans hqi
      have hcl : truncatedClamp p.2.1 i qI=p.2.1 i.succ :=
        truncatedClamp_eq_upper_of_le _ _ _ hqi
      simp only [u,max_eq_left hlow,max_eq_left hqi,truncatedStepData,hcl,sub_self,
        Real.toNNReal_zero,coleHopf_zero_var]
    · have hqu : q<cutoffAtomicNode z qc i.succ := lt_of_not_ge hqi
      have hnodes : cutoffAtomicNode z qc i.castSucc<cutoffAtomicNode z qc i.succ :=
        (cutoffAtomicNode_strictMono z hz qc hc) i.castSucc_lt_succ
      have hlt : max q (cutoffAtomicNode z qc i.castSucc)<cutoffAtomicNode z qc i.succ :=
        max_lt hqu hnodes
      have hL : max q (cutoffAtomicNode z qc i.castSucc)∈Icc (0:ℝ) 1 :=
        ⟨hq.1.trans (le_max_left _ _),
          (max_le hq.2 (cutoffAtomicNode_mem z hz qc hc i.castSucc).2).trans
            (hcQ.trans Q.property.2)⟩
      have hU : cutoffAtomicNode z qc i.succ∈Icc (0:ℝ) 1 :=
        ⟨(cutoffAtomicNode_mem z hz qc hc i.succ).1,
          (cutoffAtomicNode_mem z hz qc hc i.succ).2.trans (hcQ.trans Q.property.2)⟩
      have hcl : (truncatedClamp p.2.1 i qI:ℝ)=max q (cutoffAtomicNode z qc i.castSucc) := by
        change min (max q (cutoffAtomicNode z qc i.castSucc)) (cutoffAtomicNode z qc i.succ)=_
        exact min_eq_left hlt.le
      have hch:=FourPapersCommon.mixedPotential_coleHopf_on_constantCDF Ξ.toEvenMixture ν hL hU hlt
        (fun s hs=>parisiCDF_twoLevelMeasure_cutoff_cell z hz m hm Q qc hc hcQ i
          ⟨(le_max_right _ _).trans hs.1,hs.2⟩) y
      have hshift:=coleHopf_add_const
        (FourPapersCommon.mixedPotential_hasLinearGrowth Ξ.toEvenMixture ν hU)
        (FourPapersCommon.continuous_mixedPotential_section Ξ.toEvenMixture ν
          (cutoffAtomicNode z qc i.succ)).measurable
        (-k) (m*atomicLevel z i)
        (Ξ.first (cutoffAtomicNode z qc i.succ)-Ξ.first (max q (cutoffAtomicNode z qc i.castSucc))).toNNReal
        y
      simp only [truncatedStepData,hlevel,hfirst,hcl,hnode]
      change potential Ξ ν (max q (cutoffAtomicNode z qc i.castSucc)) y-k=
        coleHopf (m*atomicLevel z i)
          (Ξ.first (cutoffAtomicNode z qc i.succ)-Ξ.first (max q (cutoffAtomicNode z qc i.castSucc))).toNNReal
          (fun a=>potential Ξ ν (max q (cutoffAtomicNode z qc i.succ)) a-k) y
      rw [max_eq_right hqu.le]
      simp only [AdmissibleCovariance.toEvenMixture_first] at hch
      calc
        _ = coleHopf (m*atomicLevel z i)
            (Ξ.first (cutoffAtomicNode z qc i.succ)-Ξ.first (max q (cutoffAtomicNode z qc i.castSucc))).toNNReal
            (fun a=>potential Ξ ν (cutoffAtomicNode z qc i.succ) a) y-k := by
          exact congrArg (fun a:ℝ=>a-k) hch
        _ = _ := by simpa only [potential,sub_eq_add_neg] using hshift.symm
  have ht (y : ℝ) : u (Fin.last (r+1)) y=terminalValue d.terminal y := by
    simp only [u,cutoffAtomicNode_last,max_eq_right hq.2,d,cutoffCandidateData,cutoffTruncatedData]
    rw [potential_twoLevelMeasure_at_cutoff Ξ z hz m hm Q qc hc hcQ y]
    dsimp only [ν,k]
    ring
  have H:=coleHopf_chain_eq_recursion_nonneg (r+1) (truncatedStepData p qI) d.terminal u
    (fun i=>truncatedStepData_nonneg p d.first_monotone qI i) ht hstep x
  change potential Ξ ν q x-k=
    terminalValue (truncatedPotentialTerminal p (projIcc 0 qc d.qc_pos.le q)) x
  rw [projIcc_of_mem d.qc_pos.le hq]
  simpa only [u,cutoffAtomicNode_zero,max_eq_left hq.1,truncatedPotentialTerminal,p,d,qI,
    TruncatedParisiData.parameter] using H

theorem gradient_twoLevelMeasure_eq_cutoff (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc)
    (hcQ : qc≤(Q:ℝ)) (q : ℝ) (hq : q∈Icc (0:ℝ) qc) (x : ℝ) :
    gradient Ξ (twoLevelMeasure z hz m Q) q x=
      (cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).spatialField 0 (q,x) := by
  let d:=cutoffCandidateData Ξ z hz m hm Q qc hc hcQ
  have hd:=(FourPapersCommon.hasDerivAt_mixedPotential_spatial Ξ.toEvenMixture
    (twoLevelMeasure z hz m Q) q x ⟨hq.1,hq.2.trans (hcQ.trans Q.property.2)⟩).sub_const
      (cutoffCandidateConstant Ξ m Q qc)
  have he : (fun y=>potential Ξ (twoLevelMeasure z hz m Q) q y-cutoffCandidateConstant Ξ m Q qc)=
      (fun y=>d.potential q y) :=
    funext (potential_twoLevelMeasure_eq_cutoff Ξ z hz m hm Q qc hc hcQ q hq)
  change HasDerivAt
    (fun y=>potential Ξ (twoLevelMeasure z hz m Q) q y-cutoffCandidateConstant Ξ m Q qc)
    (gradient Ξ (twoLevelMeasure z hz m Q) q x) x at hd
  rw [he] at hd
  exact hd.unique (hasDerivAt_terminalValue
    (truncatedPotentialTerminal d.parameter (projIcc 0 qc d.qc_pos.le q)) x)

theorem hessian_twoLevelMeasure_eq_cutoff (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc)
    (hcQ : qc≤(Q:ℝ)) (q : ℝ) (hq : q∈Icc (0:ℝ) qc) (x : ℝ) :
    hessian Ξ (twoLevelMeasure z hz m Q) q x=
      (cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).spatialField 1 (q,x) := by
  let d:=cutoffCandidateData Ξ z hz m hm Q qc hc hcQ
  have hd:=FourPapersCommon.hasDerivAt_mixedGradient_spatial Ξ.toEvenMixture
    (twoLevelMeasure z hz m Q) q x
  have he : (fun y=>gradient Ξ (twoLevelMeasure z hz m Q) q y)=
      (fun y=>d.spatialField 0 (q,y)) :=
    funext (gradient_twoLevelMeasure_eq_cutoff Ξ z hz m hm Q qc hc hcQ q hq)
  change HasDerivAt (fun y=>gradient Ξ (twoLevelMeasure z hz m Q) q y)
    (hessian Ξ (twoLevelMeasure z hz m Q) q x) x at hd
  rw [he] at hd
  exact hd.unique (hasDerivAt_truncatedSpatialField_zero d.qc_pos.le d.parameter q x)

end DepthPaper
