module

public import DepthPaper.FirstVariation
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section


/-! Actual convex supporting-plane bounds for the mixed Parisi functional. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace DepthPaper

theorem firstVariation_supporting_plane (Ξ : AdmissibleCovariance) (μ ν : ParisiMeasure) :
    -((∫q : Overlap,firstVariation Ξ μ q ∂(ν : Measure Overlap))-
      (∫q : Overlap,firstVariation Ξ μ q ∂(μ : Measure Overlap))) ≤
      parisiFunctional Ξ ν-parisiFunctional Ξ μ := by
  have hc := FourPapersCommon.convexOn_mixedFunctional_mix Ξ.toEvenMixture 0 μ ν
  have hd := hasDerivWithinAt_parisiFunctional_mix Ξ μ ν
  have hb := hc.le_slope_of_hasDerivWithinAt_Ioi
    (by norm_num : (0:ℝ)∈Icc (0:ℝ) 1) (by norm_num : (1:ℝ)∈Icc (0:ℝ) 1)
    (by norm_num : (0:ℝ)<1) hd
  simpa only [slope_def_field,Paper.parisiMix_zero,Paper.parisiMix_one,
    sub_zero,div_one,parisiFunctional] using hb

theorem firstVariation_supporting_planes (Ξ : AdmissibleCovariance) (μ ν : ParisiMeasure) :
    -((∫q : Overlap,firstVariation Ξ μ q ∂(ν : Measure Overlap))-
      (∫q : Overlap,firstVariation Ξ μ q ∂(μ : Measure Overlap))) ≤
        parisiFunctional Ξ ν-parisiFunctional Ξ μ ∧
    parisiFunctional Ξ ν-parisiFunctional Ξ μ ≤
      -((∫q : Overlap,firstVariation Ξ ν q ∂(ν : Measure Overlap))-
        (∫q : Overlap,firstVariation Ξ ν q ∂(μ : Measure Overlap))) := by
  refine ⟨firstVariation_supporting_plane Ξ μ ν,?_⟩
  have hh := firstVariation_supporting_plane Ξ ν μ
  linarith

end DepthPaper
