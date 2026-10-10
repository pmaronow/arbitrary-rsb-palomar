module

public import GeneralDepthPaper.WeakVariationContinuity

@[expose] public section


/-! Uniform continuity of the actual lower first-variation primitive under
weak changes of the overlap measure. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 500000

def firstVariationValueMap (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) : C(Overlap,ℝ) :=
  compactPrimitiveCLM (by norm_num : (0:ℝ)≤1) (firstVariationPrimeMap Ξ μ)

@[simp] theorem firstVariationValueMap_apply (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (q : Overlap) : firstVariationValueMap Ξ μ q=firstVariation Ξ μ q := by
  rw [firstVariationValueMap,compactPrimitiveCLM_apply]
  calc
    (∫s in 0..(q:ℝ),firstVariationPrimeMap Ξ μ (projIcc 0 1 (by norm_num) s))=
        ∫s in 0..(q:ℝ),firstVariationDerivative Ξ μ s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le q.property.1] at hs
      have hsq : s∈Icc (0:ℝ) 1 := ⟨hs.1,hs.2.trans q.property.2⟩
      simp only [firstVariationPrimeMap_apply,projIcc_of_mem (by norm_num : (0:ℝ)≤1) hsq]
    _=firstVariation Ξ μ q := by
      rw [←firstVariation_difference_eq_integral Ξ μ (by norm_num) q.property,
        firstVariation_zero,sub_zero]

theorem tendsto_firstVariationValueMap_of_weak {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (Ξ : AdmissibleCovariance) (μs : ι→ParisiMeasure)
    (μ : ParisiMeasure) (hμ : Tendsto μs L (𝓝 μ)) :
    Tendsto (fun i=>firstVariationValueMap Ξ (μs i)) L (𝓝 (firstVariationValueMap Ξ μ)) := by
  exact (compactPrimitiveCLM (by norm_num : (0:ℝ)≤1)).continuous.continuousAt.tendsto.comp
    (tendsto_firstVariationPrimeMap_of_weak Ξ μs μ hμ)

theorem firstVariation_two_values_sub_norm_le (Ξ : AdmissibleCovariance) (μ ν : ParisiMeasure)
    (a b : Overlap) :
    ‖(firstVariation Ξ ν a-firstVariation Ξ ν b)-(firstVariation Ξ μ a-firstVariation Ξ μ b)‖≤
      2*‖firstVariationValueMap Ξ ν-firstVariationValueMap Ξ μ‖ := by
  have ha := (firstVariationValueMap Ξ ν-firstVariationValueMap Ξ μ).norm_coe_le_norm a
  have hb := (firstVariationValueMap Ξ ν-firstVariationValueMap Ξ μ).norm_coe_le_norm b
  simp only [ContinuousMap.sub_apply,firstVariationValueMap_apply] at ha hb
  have he : (firstVariation Ξ ν a-firstVariation Ξ ν b)-(firstVariation Ξ μ a-firstVariation Ξ μ b)=
      (firstVariation Ξ ν a-firstVariation Ξ μ a)-(firstVariation Ξ ν b-firstVariation Ξ μ b) := by ring
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

end GeneralDepthPaper
