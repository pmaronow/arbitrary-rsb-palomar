module

public import DepthPaper.TruncatedAtomicPotential
public import FourPapersCommon.BrownianClockRescaling

@[expose] public section


/-! The actual atomic CDF is the finite coefficient between the endpoints,
and the integrated truncated rate is exactly the covariance derivative. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators NNReal
namespace DepthPaper
open FourPapersCommon
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem exists_atomic_right_cell {r : ℕ} (z : AtomicPoint r) (hz : IsAtomicPoint z)
    (q : ℝ) (hq : q∈Ico (0:ℝ) 1) :
    ∃i:Fin (r+1),q∈Ico (atomicNode z i.castSucc) (atomicNode z i.succ) := by
  classical
  have hex : ∃i:Fin (r+2),q<atomicNode z i :=
    ⟨Fin.last (r+1),by simpa only [atomicNode_last] using hq.2⟩
  let j:=Fin.find (fun i:Fin (r+2)=>q<atomicNode z i) hex
  have hj:=Fin.find_spec hex
  have hj0 : j≠0 := by
    intro he
    change q<atomicNode z j at hj
    rw [he,atomicNode_zero] at hj
    exact (not_lt_of_ge hq.1) hj
  obtain ⟨i,hi⟩:=Fin.exists_succ_eq_of_ne_zero hj0
  refine ⟨i,?_,?_⟩
  · exact le_of_not_gt (Fin.find_min hex (show i.castSucc<j by rw [←hi]; exact i.castSucc_lt_succ))
  · change q<atomicNode z j at hj
    simpa only [←hi] using hj

theorem atomicTruncatedData_coefficient_eq (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (q : ℝ) (hq : q∈Ico (0:ℝ) 1) :
    (atomicTruncatedData Ξ z hz).coefficient q=Paper.parisiCDF (atomicMeasure z hz) q := by
  obtain ⟨i,hi⟩:=exists_atomic_right_cell z hz q hq
  rw [parisiCDF_atomicMeasure_cell z hz i hi]
  exact truncatedCoefficient_eq_level (atomicTruncatedData Ξ z hz).parameter
    (atomicTruncatedData Ξ z hz).node_strictMono.monotone q i hi

theorem rateClock_atomicTruncatedData_eq (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (q : ℝ≥0) (hq : (q:ℝ)≤1) :
    (rateClock (atomicTruncatedData Ξ z hz).rateData q : ℝ)=Ξ.first q := by
  let d:=atomicTruncatedData Ξ z hz
  change (∫s in (0:ℝ)..(q:ℝ),d.covarianceField 2 s.toNNReal)=Ξ.first q
  have he : (∫s in (0:ℝ)..(q:ℝ),d.covarianceField 2 s.toNNReal)=
      ∫s in (0:ℝ)..(q:ℝ),Ξ.second s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le q.coe_nonneg] at hs
    change d.covarianceField 2 (s.toNNReal:ℝ)=Ξ.second s
    rw [Real.coe_toNNReal _ hs.1]
    exact atomicTruncatedData_covarianceField_two Ξ z hz s ⟨hs.1,hs.2.trans hq⟩
  rw [he,intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _=>Ξ.hasDerivAt_first s) (Ξ.continuous_second.intervalIntegrable _ _),
    Ξ.first_zero,sub_zero]

def atomicCovarianceClock (Ξ : AdmissibleCovariance) : C(TruncatedClockDomain 1,ℝ≥0) :=
  ⟨fun q=>(Ξ.first q).toNNReal,
    continuous_real_toNNReal.comp (Ξ.continuous_first.comp continuous_subtype_val)⟩

theorem rateNoisePath_atomicTruncatedData_eq (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (ω : Paper.BrownianSample) :
    rateNoisePath (atomicTruncatedData Ξ z hz).rateData 1 ω=
      clockBrownianPath (atomicCovarianceClock Ξ) ω := by
  ext q
  change Paper.canonicalBrownian (rateClock (atomicTruncatedData Ξ z hz).rateData (q:ℝ).toNNReal) ω=
    Paper.canonicalBrownian (Ξ.first q).toNNReal ω
  congr 1
  apply NNReal.coe_injective
  rw [rateClock_atomicTruncatedData_eq Ξ z hz _
    (by simpa only [Real.coe_toNNReal _ q.property.1] using q.property.2),
    Real.coe_toNNReal _ q.property.1,Real.coe_toNNReal _ (Ξ.first_nonneg q.property.1)]

end DepthPaper
