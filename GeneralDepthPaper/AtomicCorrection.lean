module

public import GeneralDepthPaper.AtomicRecursionData
public import FourPapersCommon.WeightedCDF

@[expose] public section


/-! The literal mixed-model atomic CDF correction is an explicit smooth sum.
Its identification is by genuine measure integration and the fundamental
theorem of calculus, retaining all atom locations and masses. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 600000

def covarianceCorrectionPrimitive (Ξ:AdmissibleCovariance) (q:ℝ) : ℝ := q*Ξ.first q-Ξ.value q

theorem hasDerivAt_covarianceCorrectionPrimitive (Ξ:AdmissibleCovariance) (q:ℝ) :
    HasDerivAt (covarianceCorrectionPrimitive Ξ) (q*Ξ.second q) q := by
  convert! ((hasDerivAt_id q).mul (Ξ.hasDerivAt_first q)).sub (Ξ.hasDerivAt_value q) using 1
  simp only [id_eq]
  ring

def atomicCorrection (Ξ:AdmissibleCovariance) {r:ℕ} (z:AtomicPoint r) : ℝ :=
  ∑i:Fin (r+1),atomicWeight z i*
    (covarianceCorrectionPrimitive Ξ 1-covarianceCorrectionPrimitive Ξ (atomicLocation z i))

theorem atomicCorrection_eq_integral (Ξ:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) :
    atomicCorrection Ξ z=∫q in (0:ℝ)..1,q*Ξ.second q*Paper.parisiCDF (atomicMeasure z hz) q := by
  symm
  change FourPapersCommon.weightedCDFIntegral (fun q=>q*Ξ.second q) (atomicMeasure z hz)=atomicCorrection Ξ z
  rw [FourPapersCommon.weightedCDFIntegral_eq_measure_integral
    (fun q=>q*Ξ.second q) (continuous_id.mul Ξ.continuous_second).continuousOn]
  rw [atomicMeasure_measure,integral_finset_sum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (hz.2.2 i).le]
    change atomicWeight z i*(∫q in atomicLocation z i..1,q*Ξ.second q)=_
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun q _=>hasDerivAt_covarianceCorrectionPrimitive Ξ q)
      ((continuous_id.mul Ξ.continuous_second).intervalIntegrable _ _)]
  · intro i _
    exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

end GeneralDepthPaper
