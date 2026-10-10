module

public import GeneralDepthPaper.FirstVariation
public import FourPapersCommon.MixedQuadraticFirstVariation

@[expose] public section


/-! The original-overlap global quadratic first-variation display, for
all Parisi probability measures and the genuine finite mixed covariance. -/
noncomputable section
open Set MeasureTheory
namespace GeneralDepthPaper
open FourPapersCommon

def parisiMeasureD1 (μ ν:ParisiMeasure) : ℝ :=
  ∫q in (0:ℝ)..1,|Paper.parisiCDF μ q-Paper.parisiCDF ν q|

theorem parisiMeasureD1_eq_cdfDistance (μ ν:ParisiMeasure) :
    parisiMeasureD1 μ ν=parisiCDFDistance μ ν := by
  simp only [parisiMeasureD1,parisiCDFDistance,Real.norm_eq_abs]

/-- Equation (2.4): the constant depends only on the actual covariance,
and the estimate holds for every pair of measures, with atoms permitted. -/
theorem quadratic_first_variation (Ξ:AdmissibleCovariance) :
    ∃C:ℝ,0<C ∧ ∀μ ν:ParisiMeasure,
      |parisiFunctional Ξ ν-parisiFunctional Ξ μ+
        ((∫q,firstVariation Ξ μ q ∂(ν:Measure Overlap))-
          (∫q,firstVariation Ξ μ q ∂(μ:Measure Overlap)))|≤C*(parisiMeasureD1 μ ν)^2 := by
  let c:=Ξ.toEvenMixture.second 1*mixedMomentL1Constant Ξ.toEvenMixture/2
  have hc:0≤c:=div_nonneg
    (mul_nonneg (Ξ.toEvenMixture.second_nonneg 1) (mixedMomentL1Constant_nonneg _)) (by norm_num)
  refine ⟨c+1,by linarith,?_⟩
  intro μ ν
  have hh:=mixedFunctional_quadratic_firstVariation Ξ.toEvenMixture 0 μ ν
  change |parisiFunctional Ξ ν-parisiFunctional Ξ μ+
    ((∫q,firstVariation Ξ μ q ∂(ν:Measure Overlap))-
      (∫q,firstVariation Ξ μ q ∂(μ:Measure Overlap)))|≤c*(parisiCDFDistance μ ν)^2 at hh
  rw [parisiMeasureD1_eq_cdfDistance]
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))

end GeneralDepthPaper
