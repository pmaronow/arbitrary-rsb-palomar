module

public import DepthPaper.CutoffSelectedPotential
public import FourPapersCommon.BrownianClockRescaling

@[expose] public section


/-! Exact coefficient and covariance primitive for the actual cutoff data. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators NNReal
namespace DepthPaper
open FourPapersCommon
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem exists_cutoff_right_cell {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc)
    (q : ℝ) (hq : q∈Ico (0:ℝ) qc) :
    ∃i:Fin (r+1),q∈Ico (cutoffAtomicNode z qc i.castSucc) (cutoffAtomicNode z qc i.succ) := by
  classical
  have hex : ∃i:Fin (r+2),q<cutoffAtomicNode z qc i :=
    ⟨Fin.last (r+1),by simpa only [cutoffAtomicNode_last] using hq.2⟩
  let j:=Fin.find (fun i:Fin (r+2)=>q<cutoffAtomicNode z qc i) hex
  have hj:=Fin.find_spec hex
  have hj0 : j≠0 := by
    intro he
    change q<cutoffAtomicNode z qc j at hj
    rw [he,cutoffAtomicNode_zero] at hj
    exact (not_lt_of_ge hq.1) hj
  obtain ⟨i,hi⟩:=Fin.exists_succ_eq_of_ne_zero hj0
  refine ⟨i,?_,?_⟩
  · exact le_of_not_gt (Fin.find_min hex
      (show i.castSucc<j by rw [←hi];exact i.castSucc_lt_succ))
  · change q<cutoffAtomicNode z qc j at hj
    simpa only [←hi] using hj

theorem cutoffCandidateData_coefficient_eq (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc)
    (hcQ : qc≤(Q:ℝ)) (q : ℝ) (hq : q∈Ico (0:ℝ) qc) :
    (cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).coefficient q=
      Paper.parisiCDF (twoLevelMeasure z hz m Q) q := by
  obtain ⟨i,hi⟩:=exists_cutoff_right_cell z hz qc hc q hq
  rw [parisiCDF_twoLevelMeasure_cutoff_cell z hz m hm Q qc hc hcQ i hi]
  exact truncatedCoefficient_eq_level (cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).parameter
    (cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).node_strictMono.monotone q i hi

theorem rateClock_cutoffCandidateData_eq (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc)
    (hcQ : qc≤(Q:ℝ)) (q : ℝ≥0) (hq : (q:ℝ)≤qc) :
    (rateClock (cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).rateData q:ℝ)=Ξ.first q := by
  let d:=cutoffCandidateData Ξ z hz m hm Q qc hc hcQ
  change (∫s in (0:ℝ)..(q:ℝ),d.covarianceField 2 s.toNNReal)=Ξ.first q
  have he : (∫s in (0:ℝ)..(q:ℝ),d.covarianceField 2 s.toNNReal)=
      ∫s in (0:ℝ)..(q:ℝ),Ξ.second s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le q.coe_nonneg] at hs
    change d.covarianceField 2 (s.toNNReal:ℝ)=Ξ.second s
    rw [Real.coe_toNNReal _ hs.1]
    exact cutoffTruncatedData_covarianceField_two Ξ z hz m hm qc hc _ _ s
      ⟨hs.1,hs.2.trans hq⟩
  rw [he,intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _=>Ξ.hasDerivAt_first s) (Ξ.continuous_second.intervalIntegrable _ _),
    Ξ.first_zero,sub_zero]

def cutoffCovarianceClock (Ξ : AdmissibleCovariance) (qc : ℝ) :
    C(TruncatedClockDomain qc,ℝ≥0) :=
  ⟨fun q=>(Ξ.first q).toNNReal,
    continuous_real_toNNReal.comp (Ξ.continuous_first.comp continuous_subtype_val)⟩

theorem rateNoisePath_cutoffCandidateData_eq (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc)
    (hcQ : qc≤(Q:ℝ)) (ω : Paper.BrownianSample) :
    rateNoisePath (cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).rateData qc ω=
      clockBrownianPath (cutoffCovarianceClock Ξ qc) ω := by
  ext q
  change Paper.canonicalBrownian
      (rateClock (cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).rateData (q:ℝ).toNNReal) ω=
    Paper.canonicalBrownian (Ξ.first q).toNNReal ω
  congr 1
  apply NNReal.coe_injective
  rw [rateClock_cutoffCandidateData_eq Ξ z hz m hm Q qc hc hcQ _
    (by simpa only [Real.coe_toNNReal _ q.property.1] using q.property.2),
    Real.coe_toNNReal _ q.property.1,Real.coe_toNNReal _ (Ξ.first_nonneg q.property.1)]

end DepthPaper
