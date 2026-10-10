module

public import DepthPaper.TruncatedAtomicCoefficient

@[expose] public section


/-! Exact law identification between the constructed truncated diffusion
and the actual selected mixed-model diffusion. Brownian rescaling is proved
at the level of entire continuous paths, then transported by genuine Picard
solution maps; no state-law hypothesis is supplied. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace DepthPaper
open FourPapersCommon
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def atomicOptimalStatePath (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (ω : BrownianSample) : C(TruncatedClockDomain 1,ℝ) :=
  ⟨fun q=>optimalState Ξ (atomicMeasure z hz) ω q,by
    change Continuous (fun q:TruncatedClockDomain 1=>
      Paper.selectedParisiStateReal (mixedBeta Ξ.toEvenMixture) 0 (mixedBeta_ne_zero Ξ.toEvenMixture)
        (mixedMeasure Ξ.toEvenMixture (atomicMeasure z hz)) ω (Ξ.toEvenMixture.clock q))
    simp only [AdmissibleCovariance.toEvenMixture_clock]
    exact (Paper.continuous_selectedParisiStateReal _ _ _ _ ω).comp
      (Ξ.continuous_clock.comp continuous_subtype_val)⟩

theorem atomicOptimalNoise_eq_rescaled (Ξ : AdmissibleCovariance)
    (ω : BrownianSample) (q : TruncatedClockDomain 1) :
    mixedBeta Ξ.toEvenMixture*Paper.canonicalBrownian (Ξ.clock q).toNNReal ω=
      rescaledClockBrownianPath (mixedBeta Ξ.toEvenMixture) (atomicCovarianceClock Ξ) ω q := by
  change _=mixedBeta Ξ.toEvenMixture*Paper.canonicalBrownian
    ((Ξ.first q).toNNReal/(mixedBeta Ξ.toEvenMixture^2).toNNReal) ω
  congr 2
  apply NNReal.coe_injective
  rw [NNReal.coe_div,Real.coe_toNNReal _ (Ξ.clock_mem_unit q.property).1,
    Real.coe_toNNReal _ (Ξ.first_nonneg q.property.1),
    Real.coe_toNNReal _ (sq_nonneg _),mixedBeta_sq,AdmissibleCovariance.toEvenMixture_variance]
  rfl

theorem atomicOptimalStatePath_eq_additive (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (ω : BrownianSample) :
    atomicOptimalStatePath Ξ z hz ω=additiveStatePath (atomicTruncatedData Ξ z hz).driftData
      0 1 (by norm_num) (rescaledClockBrownianPath (mixedBeta Ξ.toEvenMixture) (atomicCovarianceClock Ξ) ω) := by
  let d:=atomicTruncatedData Ξ z hz
  let W:=rescaledClockBrownianPath (mixedBeta Ξ.toEvenMixture) (atomicCovarianceClock Ξ) ω
  let X:=Paper.parisiNoiseExtension (by norm_num : (0:ℝ)≤1) (atomicOptimalStatePath Ξ z hz ω)
  have hX:=Paper.continuous_parisiNoiseExtension (by norm_num : (0:ℝ)≤1) (atomicOptimalStatePath Ξ z hz ω)
  have heq : ∀t∈Icc (0:ℝ) 1,X t=0+Paper.parisiNoiseExtension (by norm_num : (0:ℝ)≤1) W t+
      ∫s in (0:ℝ)..t,d.driftData.coefficient s*d.driftData.gradient s (X s) := by
    intro t ht
    have hx : X t=optimalState Ξ (atomicMeasure z hz) ω t := by
      simp only [X,Paper.parisiNoiseExtension,projIcc_of_mem (by norm_num : (0:ℝ)≤1) ht,
        atomicOptimalStatePath,ContinuousMap.coe_mk]
    have hn : Paper.parisiNoiseExtension (by norm_num : (0:ℝ)≤1) W t=
        mixedBeta Ξ.toEvenMixture*Paper.canonicalBrownian (Ξ.clock t).toNNReal ω := by
      rw [Paper.parisiNoiseExtension,projIcc_of_mem (by norm_num : (0:ℝ)≤1) ht]
      exact (atomicOptimalNoise_eq_rescaled Ξ ω ⟨t,ht⟩).symm
    rw [hx,hn,optimalState_integral_equation Ξ (atomicMeasure z hz) ω ht,zero_add]
    congr 1
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le ht.1]
    intro s hs
    have hsu : s∈Icc (0:ℝ) 1 := ⟨hs.1.le,hs.2.le.trans ht.2⟩
    have hsco : s∈Ico (0:ℝ) 1 := ⟨hs.1.le,hs.2.trans_le ht.2⟩
    simp only [TruncatedParisiData.driftData,atomicTruncatedData_covarianceField_two Ξ z hz s hsu,
      atomicTruncatedData_coefficient_eq Ξ z hz s hsco,X,Paper.parisiNoiseExtension,
      projIcc_of_mem (by norm_num : (0:ℝ)≤1) hsu,atomicOptimalStatePath,ContinuousMap.coe_mk]
    rw [←gradient_atomicMeasure_eq_truncated Ξ z hz s hsu]
    dsimp only [d]
    rw [atomicTruncatedData_covarianceField_two Ξ z hz s hsu,
      atomicTruncatedData_coefficient_eq Ξ z hz s hsco]
  have hu:=additiveStateReal_unique d.driftData 0 1 (by norm_num)
    (Paper.parisiNoiseExtension (by norm_num : (0:ℝ)≤1) W)
    (Paper.continuous_parisiNoiseExtension (by norm_num : (0:ℝ)≤1) W) X hX heq
  ext q
  rw [additiveStatePath_apply]
  exact (show X q=optimalState Ξ (atomicMeasure z hz) ω q by
    simp only [X,Paper.parisiNoiseExtension,projIcc_val,atomicOptimalStatePath,ContinuousMap.coe_mk]).symm.trans
      (hu q.property)

def atomicTruncatedStatePath (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (ω : BrownianSample) : C(TruncatedClockDomain 1,ℝ) :=
  ⟨fun q=>(atomicTruncatedData Ξ z hz).state (q:ℝ).toNNReal ω,
    ((atomicTruncatedData Ξ z hz).continuous_state ω).comp
      (continuous_real_toNNReal.comp continuous_subtype_val)⟩

theorem atomicTruncatedStatePath_eq_additive (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (ω : BrownianSample) :
    atomicTruncatedStatePath Ξ z hz ω=additiveStatePath (atomicTruncatedData Ξ z hz).driftData
      0 1 (by norm_num) (clockBrownianPath (atomicCovarianceClock Ξ) ω) := by
  ext q
  change clockedItoState (atomicTruncatedData Ξ z hz).driftData (atomicTruncatedData Ξ z hz).rateData
    0 1 (by norm_num) (q:ℝ).toNNReal ω=_
  rw [clockedItoState_eq _ _ _ _ _
    (by simpa only [Real.coe_toNNReal _ q.property.1] using q.property.2),
    Real.coe_toNNReal _ q.property.1,clockedStateReal_eq_path,
    rateNoisePath_atomicTruncatedData_eq]

theorem atomic_truncated_state_path_law (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) :
    Paper.canonicalBrownianMeasure.map (atomicTruncatedStatePath Ξ z hz)=
      Paper.canonicalBrownianMeasure.map (atomicOptimalStatePath Ξ z hz) := by
  have hL:=clockBrownianPath_rescaling_law (mixedBeta Ξ.toEvenMixture)
    (mixedBeta_ne_zero Ξ.toEvenMixture) (atomicCovarianceClock Ξ)
  rw [show atomicTruncatedStatePath Ξ z hz=(fun ω=>additiveStatePath (atomicTruncatedData Ξ z hz).driftData
    0 1 (by norm_num) (clockBrownianPath (atomicCovarianceClock Ξ) ω)) from
      funext (atomicTruncatedStatePath_eq_additive Ξ z hz),
    show atomicOptimalStatePath Ξ z hz=(fun ω=>additiveStatePath (atomicTruncatedData Ξ z hz).driftData
    0 1 (by norm_num) (rescaledClockBrownianPath (mixedBeta Ξ.toEvenMixture) (atomicCovarianceClock Ξ) ω)) from
      funext (atomicOptimalStatePath_eq_additive Ξ z hz)]
  have hh:=congrArg (fun ν:Measure C(TruncatedClockDomain 1,ℝ)=>
    ν.map (additiveStatePath (atomicTruncatedData Ξ z hz).driftData 0 1 (by norm_num))) hL
  rw [Measure.map_map (measurable_additiveStatePath _ _ _ _)
    (measurable_clockBrownianPath _),
    Measure.map_map (measurable_additiveStatePath _ _ _ _)
      (measurable_rescaledClockBrownianPath _ _)] at hh
  simpa only [Function.comp_def] using hh

end DepthPaper
