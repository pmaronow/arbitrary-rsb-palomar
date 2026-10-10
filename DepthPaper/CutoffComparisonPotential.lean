module

public import DepthPaper.TemperatureMassRecursion
public import DepthPaper.CutoffSelectedCoefficient

@[expose] public section


/-! The actual comparison truncated data of 4.1(b). Their terminal is ψ_m;
their entire finite recursion is the selected temperature-scaled potential.
The identity holds on closed cells and at every grid boundary. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace DepthPaper
open ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

def cutoffComparisonData (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) : TruncatedParisiData r qc :=
  cutoffTruncatedData Ξ z hz m hm qc hc (scaledLogCoshTerminal m)
    (norm_terminalJet_scaledLogCoshTerminal_le_one m)

theorem parisiCDF_atomicMeasure_cutoff_cell {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (qc : ℝ)
    (hc : atomicLocation z (Fin.last r)<qc) (hc1 : qc≤1) (i : Fin (r+1))
    {q : ℝ} (hq : q∈Ico (cutoffAtomicNode z qc i.castSucc) (cutoffAtomicNode z qc i.succ)) :
    Paper.parisiCDF (atomicMeasure z hz) q=atomicLevel z i := by
  apply parisiCDF_atomicMeasure_cell z hz i
  refine ⟨by simpa only [atomicNode_castSucc,cutoffAtomicNode_castSucc] using hq.1,?_⟩
  have hupper : cutoffAtomicNode z qc i.succ≤atomicNode z i.succ := by
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa only [Fin.succ_last,cutoffAtomicNode_last,atomicNode_last] using hc1
    · rw [Fin.succ_castSucc,cutoffAtomicNode_castSucc,atomicNode_castSucc]
  exact hq.2.trans_le hupper

theorem atomicSupport_le_cutoff {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (qc : ℝ) (hc : atomicLocation z (Fin.last r)≤qc) :
    ∀q∈FRSB.parisiSupport (atomicMeasure z hz),q≤qc := by
  rintro q ⟨a,ha,rfl⟩
  rw [support_atomicMeasure] at ha
  obtain ⟨i,rfl⟩:=ha
  exact (hz.1.monotone (Fin.le_last i)).trans hc

theorem potential_cutoffComparisonData (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (hc1 : qc≤1)
    (q : ℝ) (hq : q∈Icc (0:ℝ) qc) (x : ℝ) :
    (cutoffComparisonData Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc).potential q x=
      temperatureMassPotential Ξ (atomicMeasure z hz) m qc q x := by
  let d:=cutoffComparisonData Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc
  let p:=d.parameter
  let qI:TruncatedClockDomain qc:=⟨q,hq⟩
  let u:Fin (r+2)→ℝ→ℝ:=fun i y=>temperatureMassPotential Ξ (atomicMeasure z hz) m qc
    (max q (cutoffAtomicNode z qc i)) y
  have hfirst : ∀a:TruncatedClockDomain qc,p.1 a=Ξ.first a := fun a=>cutoffCovarianceJetMap_one Ξ qc a
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
    · have hqu : q<cutoffAtomicNode z qc i.succ:=lt_of_not_ge hqi
      have hnodes : cutoffAtomicNode z qc i.castSucc<cutoffAtomicNode z qc i.succ:=
        (cutoffAtomicNode_strictMono z hz qc hc) i.castSucc_lt_succ
      have hlt : max q (cutoffAtomicNode z qc i.castSucc)<cutoffAtomicNode z qc i.succ:=
        max_lt hqu hnodes
      have hL : max q (cutoffAtomicNode z qc i.castSucc)∈Icc (0:ℝ) 1:=
        ⟨hq.1.trans (le_max_left _ _),
          (max_le hq.2 (cutoffAtomicNode_mem z hz qc hc i.castSucc).2).trans hc1⟩
      have hU : cutoffAtomicNode z qc i.succ∈Icc (0:ℝ) 1:=
        ⟨(cutoffAtomicNode_mem z hz qc hc i.succ).1,
          (cutoffAtomicNode_mem z hz qc hc i.succ).2.trans hc1⟩
      have hcl : (truncatedClamp p.2.1 i qI:ℝ)=max q (cutoffAtomicNode z qc i.castSucc) := by
        change min (max q (cutoffAtomicNode z qc i.castSucc)) (cutoffAtomicNode z qc i.succ)=_
        exact min_eq_left hlt.le
      have H:=temperatureMassPotential_coleHopf Ξ (atomicMeasure z hz) m hm.1 qc hL hU hlt
        (fun s hs=>parisiCDF_atomicMeasure_cutoff_cell z hz qc hc hc1 i
          ⟨(le_max_right _ _).trans hs.1,hs.2⟩) y
      simp only [u,truncatedStepData,hlevel,hfirst,hcl,hnode,max_eq_right hqu.le]
      exact H
  have ht (y : ℝ) : u (Fin.last (r+1)) y=terminalValue d.terminal y := by
    simp only [u,cutoffAtomicNode_last,max_eq_right hq.2,d,cutoffComparisonData,cutoffTruncatedData]
    exact temperatureMassPotential_terminal Ξ (atomicMeasure z hz) m hm.1
      ⟨cutoff_pos z hz qc hc|>.le,hc1⟩ (atomicSupport_le_cutoff z hz qc hc.le) y
  have H:=coleHopf_chain_eq_recursion_nonneg (r+1) (truncatedStepData p qI) d.terminal u
    (fun i=>truncatedStepData_nonneg p d.first_monotone qI i) ht hstep x
  change terminalValue (truncatedPotentialTerminal p (projIcc 0 qc d.qc_pos.le q)) x=
    temperatureMassPotential Ξ (atomicMeasure z hz) m qc q x
  rw [projIcc_of_mem d.qc_pos.le hq]
  simpa only [u,cutoffAtomicNode_zero,max_eq_left hq.1,truncatedPotentialTerminal,p,d,qI,
    TruncatedParisiData.parameter] using H.symm

theorem gradient_cutoffComparisonData (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (hc1 : qc≤1)
    (q : ℝ) (hq : q∈Icc (0:ℝ) qc) (x : ℝ) :
    (cutoffComparisonData Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc).spatialField 0 (q,x)=
      temperatureMassGradient Ξ (atomicMeasure z hz) m q x := by
  let d:=cutoffComparisonData Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc
  have he : (fun y=>d.potential q y)=temperatureMassPotential Ξ (atomicMeasure z hz) m qc q:=
    funext (potential_cutoffComparisonData Ξ z hz m hm qc hc hc1 q hq)
  have hd:=hasDerivAt_terminalValue (truncatedPotentialTerminal d.parameter
    (projIcc 0 qc d.qc_pos.le q)) x
  change HasDerivAt (fun y=>d.potential q y) (d.spatialField 0 (q,x)) x at hd
  rw [he] at hd
  exact hd.unique (hasDerivAt_temperatureMassPotential_spatial Ξ (atomicMeasure z hz) m hm.1 qc q x
    ⟨hq.1,hq.2.trans hc1⟩)

theorem hessian_cutoffComparisonData (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (hc1 : qc≤1)
    (q : ℝ) (hq : q∈Icc (0:ℝ) qc) (x : ℝ) :
    (cutoffComparisonData Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc).spatialField 1 (q,x)=
      temperatureMassHessian Ξ (atomicMeasure z hz) m q x := by
  let d:=cutoffComparisonData Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc
  have he : (fun y=>d.spatialField 0 (q,y))=temperatureMassGradient Ξ (atomicMeasure z hz) m q:=
    funext (gradient_cutoffComparisonData Ξ z hz m hm qc hc hc1 q hq)
  have hd:=hasDerivAt_truncatedSpatialField_zero d.qc_pos.le d.parameter q x
  change HasDerivAt (fun y=>d.spatialField 0 (q,y)) (d.spatialField 1 (q,x)) x at hd
  rw [he] at hd
  exact hd.unique (hasDerivAt_temperatureMassGradient_spatial Ξ (atomicMeasure z hz) m q x)

end DepthPaper
