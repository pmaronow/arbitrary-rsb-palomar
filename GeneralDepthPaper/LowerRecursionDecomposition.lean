module

public import GeneralDepthPaper.CutoffComparisonState
public import GeneralDepthPaper.LimitingAtomicObjective

@[expose] public section


/-! The exact algebraic decomposition behind Lemma 4.2. The lower error is
the difference of the two actual cutoff recursions; the covariance remainder
is explicit and independent of the added atom's position Q. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators NNReal
namespace GeneralDepthPaper
open FourPapersCommon
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

theorem atomicCorrection_temperature (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (m : ℝ) (hm : m≠0) :
    atomicCorrection (Ξ.temperatureScale m hm) z=m^2*atomicCorrection Ξ z := by
  simp only [atomicCorrection,covarianceCorrectionPrimitive,Ξ.temperatureScale_first,
    Ξ.temperatureScale_value]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem twoLevelCorrection_eq (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) :
    (∫q in (0:ℝ)..1,q*Ξ.second q*Paper.parisiCDF (twoLevelMeasure z hz m Q) q)=
      m*atomicCorrection Ξ z+(1-m)*
        (covarianceCorrectionPrimitive Ξ 1-covarianceCorrectionPrimitive Ξ Q) := by
  let w:ℝ→ℝ:=fun q=>q*Ξ.second q
  have hw : ContinuousOn w (Icc (0:ℝ) 1):=(continuous_id.mul Ξ.continuous_second).continuousOn
  change weightedCDFIntegral w (Paper.parisiMix (Paper.diracOverlap Q Q.property)
    (atomicMeasure z hz) m)=_
  rw [weightedCDFIntegral_mix w hw _ _ m hm]
  have hd : weightedCDFIntegral w (Paper.diracOverlap Q Q.property)=
      covarianceCorrectionPrimitive Ξ 1-covarianceCorrectionPrimitive Ξ Q := by
    rw [weightedCDFIntegral_eq_measure_integral w hw]
    change (∫q,weightedTail w q ∂Measure.dirac Q)=_
    rw [integral_dirac]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun q _=>hasDerivAt_covarianceCorrectionPrimitive Ξ q)
      ((continuous_id.mul Ξ.continuous_second).intervalIntegrable _ _)
  rw [hd]
  change (1-m)*(covarianceCorrectionPrimitive Ξ 1-covarianceCorrectionPrimitive Ξ Q)+
    m*(∫q in (0:ℝ)..1,q*Ξ.second q*Paper.parisiCDF (atomicMeasure z hz) q)=_
  rw [←atomicCorrection_eq_integral Ξ z hz]
  ring

theorem integral_endpoint_weight_covariance (Ξ : AdmissibleCovariance) (Q : ℝ) :
    (∫q in Q..1,(1-q)*Ξ.second q)=Ξ.first 1-Ξ.first Q-
      (covarianceCorrectionPrimitive Ξ 1-covarianceCorrectionPrimitive Ξ Q) := by
  have hd (q : ℝ) : HasDerivAt (fun q=>Ξ.first q-covarianceCorrectionPrimitive Ξ q)
      ((1-q)*Ξ.second q) q := by
    convert! (Ξ.hasDerivAt_first q).sub (hasDerivAt_covarianceCorrectionPrimitive Ξ q) using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun q _=>hd q)
    (((continuous_const.sub continuous_id).mul Ξ.continuous_second).intervalIntegrable _ _)]
  ring

def lowerRecursionDifference (Ξ Ψ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (hcQ : qc≤(Q:ℝ)) : ℝ :=
  (cutoffCandidateData Ψ z hz m ⟨hm.1.le,hm.2⟩ Q qc hc hcQ).potential 0 0-
    (cutoffComparisonData Ξ z hz m ⟨hm.1.le,hm.2⟩ qc hc).potential 0 0

def lowerCovarianceRemainder (Ξ Ψ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (m qc : ℝ) : ℝ :=
  m/2*((Ψ.first 1-Ξ.first 1)-(Ψ.first qc-Ξ.first qc)-
    (atomicCorrection Ψ z-atomicCorrection Ξ z)-(Ψ.value 1-Ξ.value 1))

def lowerRecursionRemainder (Ξ Ψ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (hcQ : qc≤(Q:ℝ)) : ℝ :=
  lowerRecursionDifference Ξ Ψ z hz m hm Q qc hc hcQ+lowerCovarianceRemainder Ξ Ψ z m qc

theorem twoLevelFunctional_decomposition (Ξ Ψ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Ioc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc) (hcQ : qc≤(Q:ℝ)) :
    twoLevelFunctional Ψ z hz m Q=
      limitingAtomicObjective Ξ r (Ψ.value 1-Ξ.value 1) (z,m)+
        (1-m)/2*(∫q in (Q:ℝ)..1,(1-q)*Ψ.second q)+
          lowerRecursionRemainder Ξ Ψ z hz m hm Q qc hc hcQ := by
  let μ:=atomicMeasure z hz
  let Θ:AdmissibleCovariance:=(temperatureCovarianceFamily Ξ).covariance m
  have hqc : 0≤qc:=(cutoff_pos z hz qc hc).le
  have hp := potential_twoLevelMeasure_eq_cutoff Ψ z hz m ⟨hm.1.le,hm.2⟩ Q qc hc hcQ
    0 ⟨le_rfl,hqc⟩ 0
  have hp' : potential Ψ (twoLevelMeasure z hz m Q) 0 0=
      cutoffCandidateConstant Ψ m Q qc+
        (cutoffCandidateData Ψ z hz m ⟨hm.1.le,hm.2⟩ Q qc hc hcQ).potential 0 0 := by
    linarith
  have ht : atomicCorrection Θ z=m^2*atomicCorrection Ξ z := by
    dsimp only [Θ]
    rw [temperatureCovarianceFamily_covariance Ξ m hm.1.ne']
    exact atomicCorrection_temperature Ξ z m hm.1.ne'
  have hf : limitingAtomicObjective Ξ r (Ψ.value 1-Ξ.value 1) (z,m)=
      (Real.log 2+potential Θ μ 0 0-(1/2:ℝ)*atomicCorrection Θ z)/m+
        (Ψ.value 1-Ξ.value 1)*m/2 := by
    rw [limitingAtomicObjective,limitingAtomicPhi,atomicFunctionalExtension_eq _ z hz,
      parisiFunctional_eq,←atomicCorrection_eq_integral _ z hz]
  have hu := potential_cutoffComparisonData Ξ z hz m hm qc hc (hcQ.trans Q.property.2)
    0 ⟨le_rfl,hqc⟩ 0
  rw [twoLevelFunctional,parisiFunctional_eq,twoLevelCorrection_eq Ψ z hz m ⟨hm.1.le,hm.2⟩ Q,
    hp',hf,ht,integral_endpoint_weight_covariance]
  simp only [lowerRecursionRemainder,lowerRecursionDifference,lowerCovarianceRemainder,
    cutoffCandidateConstant,cutoffLeadingConstant,hu,temperatureMassPotential]
  change _= _+(1-m)/2*(Ψ.first 1-Ψ.first Q-
    (covarianceCorrectionPrimitive Ψ 1-covarianceCorrectionPrimitive Ψ Q))+
      ((_-(m⁻¹*potential Θ μ 0 (m*0)-m/2*(Ξ.first 1-Ξ.first qc)))+_)
  simp only [mul_zero]
  field_simp [hm.1.ne']
  ring

end GeneralDepthPaper
