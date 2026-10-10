module

public import GeneralDepthPaper.AtomicMeasureTopology
public import GeneralDepthPaper.CompactPrimitive

@[expose] public section


/-! Uniform actual first-variation derivatives under weak changes of the
order parameter, with the covariance fixed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 600000

def GammaMap (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) : C(Overlap,ℝ) :=
  ⟨fun q=>Gamma Ξ μ q,(continuousOn_Gamma Ξ μ).comp_continuous continuous_subtype_val
    (fun q=>q.property)⟩

def covarianceSecondMap (Ξ : AdmissibleCovariance) : C(Overlap,ℝ) :=
  ⟨fun q=>Ξ.second q,Ξ.continuous_second.comp continuous_subtype_val⟩

def firstVariationPrimeMap (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) : C(Overlap,ℝ) :=
  (1/2:ℝ) • (covarianceSecondMap Ξ*(GammaMap Ξ μ-⟨Subtype.val,continuous_subtype_val⟩))

@[simp] theorem firstVariationPrimeMap_apply (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (q : Overlap) :
    firstVariationPrimeMap Ξ μ q=firstVariationDerivative Ξ μ q := by
  simp only [firstVariationPrimeMap,ContinuousMap.smul_apply,ContinuousMap.mul_apply,
    ContinuousMap.sub_apply,covarianceSecondMap,GammaMap,ContinuousMap.coe_mk,
    smul_eq_mul,firstVariationDerivative]
  ring

theorem tendsto_GammaMap_of_weak {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    (Ξ : AdmissibleCovariance) (μs : ι→ParisiMeasure) (μ : ParisiMeasure)
    (hμ : Tendsto μs L (𝓝 μ)) : Tendsto (fun i=>GammaMap Ξ (μs i)) L (𝓝 (GammaMap Ξ μ)) := by
  apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
  rw [←tendstoUniformlyOn_univ]
  have hu := (FourPapersCommon.tendstoUniformlyOn_mixedGamma_of_weak Ξ.toEvenMixture 0 μs μ hμ).comp
    (fun q : Overlap=>(q:ℝ))
  have he : (fun q : Overlap=>(q:ℝ)) ⁻¹' Icc (0:ℝ) 1=univ := by
    ext q
    simp only [mem_preimage,mem_univ,iff_true]
    exact q.property
  rw [he] at hu
  exact hu

theorem tendsto_firstVariationPrimeMap_of_weak {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (Ξ : AdmissibleCovariance) (μs : ι→ParisiMeasure)
    (μ : ParisiMeasure) (hμ : Tendsto μs L (𝓝 μ)) :
    Tendsto (fun i=>firstVariationPrimeMap Ξ (μs i)) L (𝓝 (firstVariationPrimeMap Ξ μ)) :=
  ((tendsto_const_nhds (x:=covarianceSecondMap Ξ)).mul
    ((tendsto_GammaMap_of_weak Ξ μs μ hμ).sub tendsto_const_nhds)).const_smul (1/2:ℝ)

theorem firstVariation_difference_eq_integral (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    {a b : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) :
    firstVariation Ξ μ b-firstVariation Ξ μ a=
      ∫q in a..b,firstVariationDerivative Ξ μ q := by
  let F : ℝ→ℝ := fun q=>Ξ.second q*(Gamma Ξ μ q-q)
  have hc : ContinuousOn F (Icc (0:ℝ) 1) :=
    Ξ.continuous_second.continuousOn.mul ((continuousOn_Gamma Ξ μ).sub continuousOn_id)
  have hi (q : ℝ) (hq : q∈Icc (0:ℝ) 1) : IntervalIntegrable F volume 0 q :=
    (hc.mono (Icc_subset_Icc_right hq.2)).intervalIntegrable_of_Icc hq.1
  have hh := intervalIntegral.integral_interval_sub_left (hi b hb) (hi a ha)
  rw [firstVariation_eq,firstVariation_eq,←mul_sub]
  change (1/2:ℝ)*((∫q in 0..b,F q)-(∫q in 0..a,F q))=_
  rw [hh,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro q _
  dsimp only [F,firstVariationDerivative]
  ring

theorem firstVariation_increment_sub_norm_le (Ξ : AdmissibleCovariance) (μ ν : ParisiMeasure)
    {a b : ℝ} (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) :
    ‖(firstVariation Ξ ν b-firstVariation Ξ ν a)-
      (firstVariation Ξ μ b-firstVariation Ξ μ a)‖ ≤
      ‖firstVariationPrimeMap Ξ ν-firstVariationPrimeMap Ξ μ‖*|b-a| := by
  rw [firstVariation_difference_eq_integral Ξ ν ha hb,
    firstVariation_difference_eq_integral Ξ μ ha hb]
  have hcont (ρ : ParisiMeasure) : ContinuousOn (firstVariationDerivative Ξ ρ) (Icc (0:ℝ) 1) :=
    (contDiffOn_firstVariationDerivative Ξ ρ).continuousOn
  have hi (ρ : ParisiMeasure) : IntervalIntegrable (firstVariationDerivative Ξ ρ) volume a b :=
    ((hcont ρ).mono (uIcc_subset_Icc ha hb)).intervalIntegrable
  rw [←intervalIntegral.integral_sub (hi ν) (hi μ)]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro q hq
  have hqu : q∈Icc (0:ℝ) 1 := (uIcc_subset_Icc ha hb) (uIoc_subset_uIcc hq)
  simpa only [ContinuousMap.sub_apply,firstVariationPrimeMap_apply] using
    (firstVariationPrimeMap Ξ ν-firstVariationPrimeMap Ξ μ).norm_coe_le_norm ⟨q,hqu⟩

end GeneralDepthPaper
