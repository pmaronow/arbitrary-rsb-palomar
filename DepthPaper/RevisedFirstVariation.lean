module

public import DepthPaper.RevisedModel
public import FourPapersCommon.MixedQuadraticFirstVariation
public import FourPapersCommon.MixedSharpGradient
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! Global first-variation and sharp gradient bounds for every finite positive
mixed even polynomial, including quadratic interactions. All quantities use
the genuine common mixed-covariance Parisi construction. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
namespace DepthPaper.RevisedCovariance
open FourPapersCommon

def parisiMeasureD1 (μ ν:ParisiMeasure) : ℝ :=
  ∫q in (0:ℝ)..1,|Paper.parisiCDF μ q-Paper.parisiCDF ν q|

theorem parisiMeasureD1_eq_cdfDistance (μ ν:ParisiMeasure) :
    parisiMeasureD1 μ ν=parisiCDFDistance μ ν := by
  simp only [parisiMeasureD1,parisiCDFDistance,Real.norm_eq_abs]

/-- Equation (2.4): the constant depends only on the actual covariance,
and the estimate holds for every pair of measures, with atoms permitted. -/
theorem quadratic_first_variation (Ξ:RevisedCovariance) :
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

theorem firstVariation_supporting_plane (Ξ : RevisedCovariance) (μ ν : ParisiMeasure) :
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

theorem firstVariation_supporting_planes (Ξ : RevisedCovariance) (μ ν : ParisiMeasure) :
    -((∫q : Overlap,firstVariation Ξ μ q ∂(ν : Measure Overlap))-
      (∫q : Overlap,firstVariation Ξ μ q ∂(μ : Measure Overlap))) ≤
        parisiFunctional Ξ ν-parisiFunctional Ξ μ ∧
    parisiFunctional Ξ ν-parisiFunctional Ξ μ ≤
      -((∫q : Overlap,firstVariation Ξ ν q ∂(ν : Measure Overlap))-
        (∫q : Overlap,firstVariation Ξ ν q ∂(μ : Measure Overlap))) := by
  refine ⟨firstVariation_supporting_plane Ξ μ ν,?_⟩
  have hh := firstVariation_supporting_plane Ξ ν μ
  linarith

theorem gradient_sharp_d1_bound (Ξ : RevisedCovariance)
    (μ ν : ParisiMeasure) (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1) (x : ℝ) :
    ‖gradient Ξ ν q x - gradient Ξ μ q x‖ ≤
      Real.exp (Ξ.first 1) * Ξ.second 1 * parisiMeasureD1 μ ν := by
  simpa only [gradient, RevisedCovariance.toEvenMixture_first,
    RevisedCovariance.toEvenMixture_second, parisiMeasureD1_eq_cdfDistance] using
    mixedGradient_sharp_CDF_L1_bound Ξ.toEvenMixture μ ν q hq x

theorem hasDerivAt_potential_difference (Ξ : RevisedCovariance)
    (μ ν : ParisiMeasure) (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1) (x : ℝ) :
    HasDerivAt (fun y => potential Ξ ν q y - potential Ξ μ q y)
      (gradient Ξ ν q x - gradient Ξ μ q x) x :=
  (hasDerivAt_mixedPotential_spatial Ξ.toEvenMixture ν q x hq).sub
    (hasDerivAt_mixedPotential_spatial Ξ.toEvenMixture μ q x hq)

/-- The actual spatial derivative difference as a bounded continuous function
on the full physical time strip and the entire real field line. -/
def gradientDifferenceBCF (Ξ : RevisedCovariance) (μ ν : ParisiMeasure) :
    (Overlap × ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => gradient Ξ ν p.1 p.2 - gradient Ξ μ p.1 p.2)
    (by
      have hc (ρ : ParisiMeasure) : Continuous (fun p : Overlap × ℝ => gradient Ξ ρ p.1 p.2) := by
        unfold gradient mixedGradient
        simp only [RevisedCovariance.toEvenMixture_clock]
        exact (Paper.continuous_parisiGradient _ _).comp
          (((Ξ.continuous_clock.comp (continuous_subtype_val.comp continuous_fst))).prodMk continuous_snd)
      exact (hc ν).sub (hc μ)) 2
    (fun p => (norm_sub_le _ _).trans (by
      have hν := norm_mixedGradient_le_one Ξ.toEvenMixture ν ((p.1:ℝ),p.2)
      have hμ := norm_mixedGradient_le_one Ξ.toEvenMixture μ ((p.1:ℝ),p.2)
      change ‖gradient Ξ ν p.1 p.2‖ ≤ 1 at hν
      change ‖gradient Ξ μ p.1 p.2‖ ≤ 1 at hμ
      linarith))

/-- Exactly `‖w_x‖∞ ≤ exp(Ξ'(1)) Ξ''(1) d₁(μ,ν)`, with no cited estimate
or profile-response identity among the hypotheses. -/
theorem norm_gradientDifferenceBCF_le (Ξ : RevisedCovariance)
    (μ ν : ParisiMeasure) :
    ‖gradientDifferenceBCF Ξ μ ν‖ ≤
      Real.exp (Ξ.first 1) * Ξ.second 1 * parisiMeasureD1 μ ν := by
  have hC : 0 ≤ Real.exp (Ξ.first 1) * Ξ.second 1 * parisiMeasureD1 μ ν :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Ξ.second_nonneg (q := 1) zero_le_one))
      (by rw [parisiMeasureD1_eq_cdfDistance]; exact parisiCDFDistance_nonneg μ ν)
  apply (BoundedContinuousFunction.norm_le hC).mpr
  intro p
  exact gradient_sharp_d1_bound Ξ μ ν p.1 p.1.property p.2

end DepthPaper.RevisedCovariance
