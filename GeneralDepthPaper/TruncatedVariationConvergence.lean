module

public import GeneralDepthPaper.TruncatedObservableConvergence
public import GeneralDepthPaper.TruncatedGammaRegularity
public import GeneralDepthPaper.CompactPrimitive

@[expose] public section


/-! Actual closed-interval C² jet convergence of the first-variation function
in Appendix A.2. The jets are its genuine first and second derivatives. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BoundedContinuousFunction ContDiff
namespace GeneralDepthPaper
open FourPapersCommon Paper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

def clockIdentity (qc : ℝ) : C(TruncatedClockDomain qc,ℝ) :=
  ⟨Subtype.val,continuous_subtype_val⟩

namespace TruncatedParisiData

def GammaMap {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) : C(TruncatedClockDomain qc,ℝ) :=
  ⟨fun q => d.Gamma q,d.continuous_Gamma.comp continuous_subtype_val⟩

def Gamma2Map {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) : C(TruncatedClockDomain qc,ℝ) :=
  ⟨fun q => d.Gamma2 q,d.continuous_Gamma2.comp continuous_subtype_val⟩

def firstVariationMap {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) :
    C(TruncatedClockDomain qc,ℝ) :=
  ⟨fun q => d.firstVariation q,(continuous_iff_continuousAt.mpr
    (fun q => (d.hasDerivAt_firstVariation q).continuousAt)).comp continuous_subtype_val⟩

def firstVariationPrimeMap {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) :
    C(TruncatedClockDomain qc,ℝ) :=
  (1/2:ℝ) • (d.covarianceJet 2*(d.GammaMap-clockIdentity qc))

def firstVariationSecondMap {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) :
    C(TruncatedClockDomain qc,ℝ) :=
  (1/2:ℝ) • (d.covarianceJet 3*(d.GammaMap-clockIdentity qc))+
    (1/2:ℝ) • (d.covarianceJet 2*(d.covarianceJet 2*d.Gamma2Map-1))

@[simp] theorem firstVariationPrimeMap_apply {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (q : TruncatedClockDomain qc) : d.firstVariationPrimeMap q=d.firstVariationPrime q := by
  simp [firstVariationPrimeMap,firstVariationPrime,TruncatedParisiData.covarianceField,
    GammaMap,clockIdentity,projIcc_of_mem d.qc_pos.le q.property]
  ring

@[simp] theorem firstVariationSecondMap_apply {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (q : TruncatedClockDomain qc) : d.firstVariationSecondMap q=d.firstVariationSecond q := by
  simp [firstVariationSecondMap,firstVariationSecond,TruncatedParisiData.covarianceField,
    GammaMap,Gamma2Map,clockIdentity,projIcc_of_mem d.qc_pos.le q.property]
  ring

theorem firstVariationMap_eq_primitive {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) :
    d.firstVariationMap=(1/2:ℝ) • compactPrimitiveCLM d.qc_pos.le
      (d.covarianceJet 2*(d.GammaMap-clockIdentity qc)) := by
  ext q
  change (1/2:ℝ)*(∫s in 0..(q:ℝ),d.covarianceField 2 s*(d.Gamma s-s)) =
    (1/2:ℝ)*(∫s in 0..(q:ℝ),(d.covarianceJet 2*(d.GammaMap-clockIdentity qc))
      (projIcc 0 qc d.qc_pos.le s))
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le q.property.1] at hs
  have hsqc : s ∈ Icc (0:ℝ) qc := ⟨hs.1,hs.2.trans q.property.2⟩
  simp only [ContinuousMap.mul_apply,ContinuousMap.sub_apply,GammaMap,clockIdentity,
    ContinuousMap.coe_mk,projIcc_of_mem d.qc_pos.le hsqc,TruncatedParisiData.covarianceField]

/-- The actual value/first/second derivative functions with the usual
componentwise supremum norm, equivalent to the C² norm on the compact strip. -/
def firstVariationJets {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc) :
    Fin 3 → C(TruncatedClockDomain qc,ℝ) :=
  ![d.firstVariationMap,d.firstVariationPrimeMap,d.firstVariationSecondMap]

theorem firstVariationJets_derivative {r : ℕ} {qc : ℝ} (d : TruncatedParisiData r qc)
    (j : Fin 2) (q : TruncatedClockDomain qc) :
    HasDerivWithinAt (fun t => d.firstVariationJets j.castSucc (projIcc 0 qc d.qc_pos.le t))
      (d.firstVariationJets j.succ q) (Icc (0:ℝ) qc) q := by
  have he0 : EqOn (fun t => d.firstVariationMap (projIcc 0 qc d.qc_pos.le t)) d.firstVariation
      (Icc (0:ℝ) qc) := fun t ht => by
    simp [firstVariationMap,projIcc_of_mem d.qc_pos.le ht]
  have he1 : EqOn (fun t => d.firstVariationPrimeMap (projIcc 0 qc d.qc_pos.le t)) d.firstVariationPrime
      (Icc (0:ℝ) qc) := fun t ht => by
    simp [firstVariationPrimeMap_apply,projIcc_of_mem d.qc_pos.le ht]
  fin_cases j
  · change HasDerivWithinAt (fun t => d.firstVariationMap (projIcc 0 qc d.qc_pos.le t))
      (d.firstVariationPrimeMap q) (Icc (0:ℝ) qc) q
    rw [d.firstVariationPrimeMap_apply]
    exact (d.hasDerivAt_firstVariation q).hasDerivWithinAt.congr he0 (he0 q.property)
  · change HasDerivWithinAt (fun t => d.firstVariationPrimeMap (projIcc 0 qc d.qc_pos.le t))
      (d.firstVariationSecondMap q) (Icc (0:ℝ) qc) q
    rw [d.firstVariationSecondMap_apply]
    exact (d.hasDerivWithinAt_firstVariationPrime q q.property).congr he1 (he1 q.property)

end TruncatedParisiData
namespace TruncatedDataConvergence
variable {r : ℕ} {qc : ℝ} {d : ℕ → TruncatedParisiData r qc} {d0 : TruncatedParisiData r qc}

theorem GammaMap (h : TruncatedDataConvergence d d0) :
    Tendsto (fun n => (d n).GammaMap) atTop (𝓝 d0.GammaMap) := by
  apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
  rw [←tendstoUniformlyOn_univ]
  have he := h.Gamma.comp (fun q : TruncatedClockDomain qc => (q:ℝ))
  have hs : (fun q : TruncatedClockDomain qc => (q:ℝ)) ⁻¹' Icc (0:ℝ) qc=univ := by
    ext q; simp only [mem_preimage,mem_Icc,mem_univ,iff_true]; exact q.property
  rw [hs] at he
  exact he

theorem Gamma2Map (h : TruncatedDataConvergence d d0) :
    Tendsto (fun n => (d n).Gamma2Map) atTop (𝓝 d0.Gamma2Map) := by
  apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
  rw [←tendstoUniformlyOn_univ]
  have he := h.Gamma2.comp (fun q : TruncatedClockDomain qc => (q:ℝ))
  have hs : (fun q : TruncatedClockDomain qc => (q:ℝ)) ⁻¹' Icc (0:ℝ) qc=univ := by
    ext q; simp only [mem_preimage,mem_Icc,mem_univ,iff_true]; exact q.property
  rw [hs] at he
  exact he

theorem firstVariationMap (h : TruncatedDataConvergence d d0) :
    Tendsto (fun n => (d n).firstVariationMap) atTop (𝓝 d0.firstVariationMap) := by
  have hh := (h.covariance 2).mul
    (h.GammaMap.sub (tendsto_const_nhds (x := clockIdentity qc)))
  have hp := (compactPrimitiveCLM d0.qc_pos.le).continuous.continuousAt.tendsto.comp hh
  simpa only [TruncatedParisiData.firstVariationMap_eq_primitive,Function.comp_def] using hp.const_smul (1/2:ℝ)

theorem firstVariationPrimeMap (h : TruncatedDataConvergence d d0) :
    Tendsto (fun n => (d n).firstVariationPrimeMap) atTop (𝓝 d0.firstVariationPrimeMap) :=
  ((h.covariance 2).mul
    (h.GammaMap.sub (tendsto_const_nhds (x := clockIdentity qc)))).const_smul (1/2:ℝ)

theorem firstVariationSecondMap (h : TruncatedDataConvergence d d0) :
    Tendsto (fun n => (d n).firstVariationSecondMap) atTop (𝓝 d0.firstVariationSecondMap) :=
  (((h.covariance 3).mul
    (h.GammaMap.sub (tendsto_const_nhds (x := clockIdentity qc)))).const_smul (1/2:ℝ)).add
      (((h.covariance 2).mul (((h.covariance 2).mul h.Gamma2Map).sub
        (tendsto_const_nhds (x := (1:C(TruncatedClockDomain qc,ℝ)))))).const_smul (1/2:ℝ))

theorem firstVariation_C2 (h : TruncatedDataConvergence d d0) :
    Tendsto (fun n => (d n).firstVariationJets) atTop (𝓝 d0.firstVariationJets) := by
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases j
  · exact h.firstVariationMap
  · exact h.firstVariationPrimeMap
  · exact h.firstVariationSecondMap

end TruncatedDataConvergence
end GeneralDepthPaper
