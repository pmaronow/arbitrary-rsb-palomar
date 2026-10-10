module

public import GeneralDepthPaper.TruncatedAtomicData
public import GeneralDepthPaper.ColeHopfChainClosed

@[expose] public section


/-! The literal truncated Gaussian recursion is the actual mixed Parisi
potential, at every physical overlap, including the atomic grid boundaries. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff
namespace GeneralDepthPaper
open ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem potential_atomicMeasure_eq_truncated (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (q : ℝ) (hq : q∈Icc (0:ℝ) 1) (x : ℝ) :
    potential Ξ (atomicMeasure z hz) q x=(atomicTruncatedData Ξ z hz).potential q x := by
  let d:=atomicTruncatedData Ξ z hz
  let p:=d.parameter
  let qI:TruncatedClockDomain 1:=⟨q,hq⟩
  let u:Fin (r+2)→ℝ→ℝ:=fun i y=>potential Ξ (atomicMeasure z hz) (max q (atomicNode z i)) y
  have hfirst : ∀a:TruncatedClockDomain 1,p.1 a=Ξ.first a := by
    intro a
    exact covarianceJetMap_one Ξ a
  have hnode : ∀i:Fin (r+2),(p.2.1 i:ℝ)=atomicNode z i := fun _=>rfl
  have hlevel : ∀i:Fin (r+1),p.2.2.1 i=atomicLevel z i := fun _=>rfl
  have hstep (i : Fin (r+1)) (y : ℝ) :
      u i.castSucc y=coleHopf (truncatedStepData p qI i).1
        (truncatedStepData p qI i).2.toNNReal (u i.succ) y := by
    by_cases hqi : atomicNode z i.succ≤q
    · have hlow : atomicNode z i.castSucc≤q :=
        ((atomicNode_strictMono z hz).monotone i.castSucc_lt_succ.le).trans hqi
      have hcl : truncatedClamp p.2.1 i qI=p.2.1 i.succ :=
        truncatedClamp_eq_upper_of_le _ _ _ hqi
      simp only [u,max_eq_left hlow,max_eq_left hqi,truncatedStepData,hcl,sub_self,
        Real.toNNReal_zero,coleHopf_zero_var]
    · have hqu : q<atomicNode z i.succ := lt_of_not_ge hqi
      have hnodes : atomicNode z i.castSucc<atomicNode z i.succ :=
        (atomicNode_strictMono z hz) i.castSucc_lt_succ
      have hlt : max q (atomicNode z i.castSucc)<atomicNode z i.succ := max_lt hqu hnodes
      have hL : max q (atomicNode z i.castSucc)∈Icc (0:ℝ) 1 :=
        ⟨hq.1.trans (le_max_left _ _),max_le hq.2 (atomicNode_mem_unit z hz i.castSucc).2⟩
      have hcl : (truncatedClamp p.2.1 i qI:ℝ)=max q (atomicNode z i.castSucc) := by
        change min (max q (atomicNode z i.castSucc)) (atomicNode z i.succ)=_
        exact min_eq_left hlt.le
      have hc:=FourPapersCommon.mixedPotential_coleHopf_on_constantCDF Ξ.toEvenMixture
        (atomicMeasure z hz) hL (atomicNode_mem_unit z hz i.succ) hlt
        (fun s hs=>parisiCDF_atomicMeasure_cell z hz i
          ⟨(le_max_right _ _).trans hs.1,hs.2⟩) y
      simp only [truncatedStepData,hlevel,hfirst,hcl,hnode]
      simpa only [u,potential,max_eq_right hqu.le,
        AdmissibleCovariance.toEvenMixture_first] using hc
  have ht (y : ℝ) : u (Fin.last (r+1)) y=terminalValue logCoshTerminal y := by
    simp only [u,atomicNode_last,max_eq_right hq.2,potential,
      FourPapersCommon.mixedPotential_terminal,terminalValue_logCoshTerminal]
  have H:=coleHopf_chain_eq_recursion_nonneg (r+1) (truncatedStepData p qI) logCoshTerminal u
    (fun i=>truncatedStepData_nonneg p d.first_monotone qI i) ht hstep x
  change potential Ξ (atomicMeasure z hz) q x=
    terminalValue (truncatedPotentialTerminal p (projIcc 0 1 (by norm_num) q)) x
  rw [projIcc_of_mem (by norm_num : (0:ℝ)≤1) hq]
  simpa only [u,atomicNode_zero,max_eq_left hq.1,truncatedPotentialTerminal,p,d,qI,
    TruncatedParisiData.parameter,atomicTruncatedData] using H

theorem gradient_atomicMeasure_eq_truncated (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (q : ℝ) (hq : q∈Icc (0:ℝ) 1) (x : ℝ) :
    gradient Ξ (atomicMeasure z hz) q x=(atomicTruncatedData Ξ z hz).spatialField 0 (q,x) := by
  have hd:=FourPapersCommon.hasDerivAt_mixedPotential_spatial Ξ.toEvenMixture
    (atomicMeasure z hz) q x hq
  have he : (fun y=>potential Ξ (atomicMeasure z hz) q y)=
      (fun y=>(atomicTruncatedData Ξ z hz).potential q y) :=
    funext (potential_atomicMeasure_eq_truncated Ξ z hz q hq)
  change HasDerivAt (fun y=>potential Ξ (atomicMeasure z hz) q y)
    (gradient Ξ (atomicMeasure z hz) q x) x at hd
  rw [he] at hd
  exact hd.unique (hasDerivAt_terminalValue
    (truncatedPotentialTerminal (atomicTruncatedData Ξ z hz).parameter
      (projIcc 0 1 (by norm_num) q)) x)

theorem hessian_atomicMeasure_eq_truncated (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (q : ℝ) (hq : q∈Icc (0:ℝ) 1) (x : ℝ) :
    hessian Ξ (atomicMeasure z hz) q x=(atomicTruncatedData Ξ z hz).spatialField 1 (q,x) := by
  have hd:=FourPapersCommon.hasDerivAt_mixedGradient_spatial Ξ.toEvenMixture (atomicMeasure z hz) q x
  have he : (fun y=>gradient Ξ (atomicMeasure z hz) q y)=
      (fun y=>(atomicTruncatedData Ξ z hz).spatialField 0 (q,y)) :=
    funext (gradient_atomicMeasure_eq_truncated Ξ z hz q hq)
  change HasDerivAt (fun y=>gradient Ξ (atomicMeasure z hz) q y)
    (hessian Ξ (atomicMeasure z hz) q x) x at hd
  rw [he] at hd
  exact hd.unique (hasDerivAt_truncatedSpatialField_zero (by norm_num)
    (atomicTruncatedData Ξ z hz).parameter q x)

end GeneralDepthPaper
