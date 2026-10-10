module

public import DepthPaper.CutoffSelectedCoefficient
public import DepthPaper.TruncatedAtomicStateLaw

@[expose] public section


/-! Identification of actual diffusion laws below the cutoff. The original
selected solution uses the normalized covariance clock; the truncated data
use its covariance derivative as a rate. Actual Brownian path rescaling
and uniqueness of the additive-noise Picard solution identify the laws. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace DepthPaper
open FourPapersCommon
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

def cutoffOptimalStatePath (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (Q : Overlap)
    (qc : ℝ) (ω : BrownianSample) : C(TruncatedClockDomain qc,ℝ) :=
  ⟨fun q=>optimalState Ξ (twoLevelMeasure z hz m Q) ω q,by
    change Continuous (fun q:TruncatedClockDomain qc=>
      Paper.selectedParisiStateReal (mixedBeta Ξ.toEvenMixture) 0 (mixedBeta_ne_zero Ξ.toEvenMixture)
        (mixedMeasure Ξ.toEvenMixture (twoLevelMeasure z hz m Q)) ω (Ξ.toEvenMixture.clock q))
    simp only [AdmissibleCovariance.toEvenMixture_clock]
    exact (Paper.continuous_selectedParisiStateReal _ _ _ _ ω).comp
      (Ξ.continuous_clock.comp continuous_subtype_val)⟩

theorem cutoffOptimalNoise_eq_rescaled (Ξ : AdmissibleCovariance) (qc : ℝ)
    (hc1 : qc≤1) (ω : BrownianSample) (q : TruncatedClockDomain qc) :
    mixedBeta Ξ.toEvenMixture*Paper.canonicalBrownian (Ξ.clock q).toNNReal ω=
      rescaledClockBrownianPath (mixedBeta Ξ.toEvenMixture) (cutoffCovarianceClock Ξ qc) ω q := by
  change _=mixedBeta Ξ.toEvenMixture*Paper.canonicalBrownian
    ((Ξ.first q).toNNReal/(mixedBeta Ξ.toEvenMixture^2).toNNReal) ω
  congr 2
  apply NNReal.coe_injective
  rw [NNReal.coe_div,Real.coe_toNNReal _ (Ξ.clock_mem_unit ⟨q.property.1,q.property.2.trans hc1⟩).1,
    Real.coe_toNNReal _ (Ξ.first_nonneg q.property.1),
    Real.coe_toNNReal _ (sq_nonneg _),mixedBeta_sq,AdmissibleCovariance.toEvenMixture_variance]
  rfl

theorem cutoffOptimalStatePath_eq_additive (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc)
    (hcQ : qc≤(Q:ℝ)) (ω : BrownianSample) :
    cutoffOptimalStatePath Ξ z hz m Q qc ω=
      additiveStatePath (cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).driftData
        0 qc (cutoff_pos z hz qc hc).le
        (rescaledClockBrownianPath (mixedBeta Ξ.toEvenMixture) (cutoffCovarianceClock Ξ qc) ω) := by
  let d:=cutoffCandidateData Ξ z hz m hm Q qc hc hcQ
  let W:=rescaledClockBrownianPath (mixedBeta Ξ.toEvenMixture) (cutoffCovarianceClock Ξ qc) ω
  let X:=Paper.parisiNoiseExtension d.qc_pos.le (cutoffOptimalStatePath Ξ z hz m Q qc ω)
  have hX:=Paper.continuous_parisiNoiseExtension d.qc_pos.le (cutoffOptimalStatePath Ξ z hz m Q qc ω)
  have heq : ∀t∈Icc (0:ℝ) qc,X t=0+Paper.parisiNoiseExtension d.qc_pos.le W t+
      ∫s in (0:ℝ)..t,d.driftData.coefficient s*d.driftData.gradient s (X s) := by
    intro t ht
    have hx : X t=optimalState Ξ (twoLevelMeasure z hz m Q) ω t := by
      simp only [X,Paper.parisiNoiseExtension,projIcc_of_mem d.qc_pos.le ht,
        cutoffOptimalStatePath,ContinuousMap.coe_mk]
    have hn : Paper.parisiNoiseExtension d.qc_pos.le W t=
        mixedBeta Ξ.toEvenMixture*Paper.canonicalBrownian (Ξ.clock t).toNNReal ω := by
      rw [Paper.parisiNoiseExtension,projIcc_of_mem d.qc_pos.le ht]
      exact (cutoffOptimalNoise_eq_rescaled Ξ qc (hcQ.trans Q.property.2) ω ⟨t,ht⟩).symm
    rw [hx,hn,optimalState_integral_equation Ξ (twoLevelMeasure z hz m Q) ω
      ⟨ht.1,ht.2.trans (hcQ.trans Q.property.2)⟩,zero_add]
    congr 1
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le ht.1]
    intro s hs
    have hsu : s∈Icc (0:ℝ) qc := ⟨hs.1.le,hs.2.le.trans ht.2⟩
    have hsco : s∈Ico (0:ℝ) qc := ⟨hs.1.le,hs.2.trans_le ht.2⟩
    simp only [TruncatedParisiData.driftData,X,Paper.parisiNoiseExtension,
      projIcc_of_mem d.qc_pos.le hsu,cutoffOptimalStatePath,ContinuousMap.coe_mk]
    rw [←gradient_twoLevelMeasure_eq_cutoff Ξ z hz m hm Q qc hc hcQ s hsu]
    have hcv : d.covarianceField 2 s=Ξ.second s :=
      cutoffTruncatedData_covarianceField_two Ξ z hz m hm qc hc _ _ s hsu
    rw [hcv,cutoffCandidateData_coefficient_eq Ξ z hz m hm Q qc hc hcQ s hsco]
  have hu:=additiveStateReal_unique d.driftData 0 qc d.qc_pos.le
    (Paper.parisiNoiseExtension d.qc_pos.le W)
    (Paper.continuous_parisiNoiseExtension d.qc_pos.le W) X hX heq
  ext q
  rw [additiveStatePath_apply]
  exact (show X q=optimalState Ξ (twoLevelMeasure z hz m Q) ω q by
    simp only [X,Paper.parisiNoiseExtension,projIcc_val,cutoffOptimalStatePath,ContinuousMap.coe_mk]).symm.trans
      (hu q.property)

def cutoffTruncatedStatePath (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc)
    (hcQ : qc≤(Q:ℝ)) (ω : BrownianSample) : C(TruncatedClockDomain qc,ℝ) :=
  ⟨fun q=>(cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).state (q:ℝ).toNNReal ω,
    ((cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).continuous_state ω).comp
      (continuous_real_toNNReal.comp continuous_subtype_val)⟩

theorem cutoffTruncatedStatePath_eq_additive (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc)
    (hcQ : qc≤(Q:ℝ)) (ω : BrownianSample) :
    cutoffTruncatedStatePath Ξ z hz m hm Q qc hc hcQ ω=
      additiveStatePath (cutoffCandidateData Ξ z hz m hm Q qc hc hcQ).driftData
        0 qc (cutoff_pos z hz qc hc).le (clockBrownianPath (cutoffCovarianceClock Ξ qc) ω) := by
  let d:=cutoffCandidateData Ξ z hz m hm Q qc hc hcQ
  ext q
  change clockedItoState d.driftData d.rateData 0 qc d.qc_pos.le (q:ℝ).toNNReal ω=_
  rw [clockedItoState_eq _ _ _ _ _
    (by simpa only [Real.coe_toNNReal _ q.property.1] using q.property.2),
    Real.coe_toNNReal _ q.property.1,clockedStateReal_eq_path,
    rateNoisePath_cutoffCandidateData_eq]

theorem cutoff_truncated_state_path_law (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m∈Icc (0:ℝ) 1)
    (Q : Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r)<qc)
    (hcQ : qc≤(Q:ℝ)) :
    Paper.canonicalBrownianMeasure.map (cutoffTruncatedStatePath Ξ z hz m hm Q qc hc hcQ)=
      Paper.canonicalBrownianMeasure.map (cutoffOptimalStatePath Ξ z hz m Q qc) := by
  have hL:=clockBrownianPath_rescaling_law (mixedBeta Ξ.toEvenMixture)
    (mixedBeta_ne_zero Ξ.toEvenMixture) (cutoffCovarianceClock Ξ qc)
  let d:=cutoffCandidateData Ξ z hz m hm Q qc hc hcQ
  rw [show cutoffTruncatedStatePath Ξ z hz m hm Q qc hc hcQ=(fun ω=>
      additiveStatePath d.driftData 0 qc d.qc_pos.le (clockBrownianPath (cutoffCovarianceClock Ξ qc) ω)) from
      funext (cutoffTruncatedStatePath_eq_additive Ξ z hz m hm Q qc hc hcQ),
    show cutoffOptimalStatePath Ξ z hz m Q qc=(fun ω=>
      additiveStatePath d.driftData 0 qc d.qc_pos.le
        (rescaledClockBrownianPath (mixedBeta Ξ.toEvenMixture) (cutoffCovarianceClock Ξ qc) ω)) from
      funext (cutoffOptimalStatePath_eq_additive Ξ z hz m hm Q qc hc hcQ)]
  have hh:=congrArg (fun ν:Measure C(TruncatedClockDomain qc,ℝ)=>
    ν.map (additiveStatePath d.driftData 0 qc d.qc_pos.le)) hL
  rw [Measure.map_map (measurable_additiveStatePath _ _ _ _) (measurable_clockBrownianPath _),
    Measure.map_map (measurable_additiveStatePath _ _ _ _) (measurable_rescaledClockBrownianPath _ _)] at hh
  simpa only [Function.comp_def] using hh

end DepthPaper
