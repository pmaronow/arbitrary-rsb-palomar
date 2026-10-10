module

public import FourPapersCommon.MixedMomentL1
public import FourPapersCommon.MixedContact

@[expose] public section


/-! The actual global quadratic first-variation remainder. Genuine convex
supporting planes at both measures squeeze the remainder; the actual moment
CDF-L1 estimate supplies the quadratic modulus. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace FourPapersCommon
open Paper
set_option maxHeartbeats 900000

def mixedDirectionalVariation (ξ:AdmissibleEvenMixture) (h:ℝ) (μ ν:ParisiMeasure) : ℝ :=
  (1/2:ℝ)*∫q in (0:ℝ)..1,ξ.second q*(parisiCDF ν q-parisiCDF μ q)*(mixedGamma ξ h μ q-q)

theorem mixedFunctional_supporting_plane (ξ:AdmissibleEvenMixture) (h:ℝ) (μ ν:ParisiMeasure) :
    mixedDirectionalVariation ξ h μ ν≤ mixedFunctional ξ h ν-mixedFunctional ξ h μ := by
  have hh:=(convexOn_mixedFunctional_mix ξ h μ ν).le_slope_of_hasDerivWithinAt_Ioi
    (x:=0) (y:=1) (by norm_num) (by norm_num) (by norm_num)
      (hasDerivWithinAt_mixedFunctional_mix_cdf ξ h μ ν)
  simpa only [slope_def_field,parisiMix_zero,parisiMix_one,sub_zero,div_one,
    mixedDirectionalVariation] using hh

theorem mixedFirstVariation_signed_pairing (ξ:AdmissibleEvenMixture) (h:ℝ) (μ ν:ParisiMeasure) :
    (∫q,mixedFirstVariation ξ h μ q ∂(ν:Measure Overlap))-
      (∫q,mixedFirstVariation ξ h μ q ∂(μ:Measure Overlap))=-mixedDirectionalVariation ξ h μ ν := by
  have hi (ρ:ParisiMeasure) : Integrable (fun q:Overlap=>mixedFirstVariation ξ h μ q)
      (ρ:Measure Overlap) := integrable_overlap_continuous
    ((continuousOn_mixedFirstVariation ξ h μ).comp_continuous continuous_subtype_val
      (fun q=>q.property)) ρ
  have he (ρ:ParisiMeasure) : (∫q,mixedTailVariation ξ h μ q ∂(ρ:Measure Overlap))=
      mixedFirstVariation ξ h μ 1-(∫q,mixedFirstVariation ξ h μ q ∂(ρ:Measure Overlap)) := by
    simp_rw [mixedTailVariation_eq_total_sub]
    rw [integral_sub (integrable_const _) (hi ρ)]
    simp only [integral_const,probReal_univ,one_smul]
  have hs:=integral_mixedTailVariation_sub_eq_cdf ξ h μ ν
  rw [he ν,he μ] at hs
  change _=mixedDirectionalVariation ξ h μ ν at hs
  linarith

theorem mixedDirectionalVariation_sum_bound (ξ:AdmissibleEvenMixture) (h:ℝ) (μ ν:ParisiMeasure) :
    ‖mixedDirectionalVariation ξ h μ ν+mixedDirectionalVariation ξ h ν μ‖≤
      (ξ.second 1*mixedMomentL1Constant ξ/2)*(parisiCDFDistance μ ν)^2 := by
  let c:=ξ.second 1*mixedMomentL1Constant ξ
  let f:=fun q:ℝ=>ξ.second q*(parisiCDF ν q-parisiCDF μ q)*
    (mixedGamma ξ h μ q-mixedGamma ξ h ν q)
  have hI (ρ:ParisiMeasure) (σ:ParisiMeasure) : IntervalIntegrable
      (fun q=>ξ.second q*(parisiCDF σ q-parisiCDF ρ q)*(mixedGamma ξ h ρ q-q)) volume 0 1 := by
    convert (mixedMomentWeight_intervalIntegrable ξ h ρ σ).sub
      (mixedMomentWeight_intervalIntegrable ξ h ρ ρ) using 1
    funext q;ring
  have he : mixedDirectionalVariation ξ h μ ν+mixedDirectionalVariation ξ h ν μ=
      (1/2:ℝ)*∫q in (0:ℝ)..1,f q := by
    unfold mixedDirectionalVariation
    rw [←mul_add,←intervalIntegral.integral_add (hI μ ν) (hI ν μ)]
    congr 1
    apply intervalIntegral.integral_congr
    intro q _
    dsimp only [f];ring
  have hb:∀q∈uIoc (0:ℝ) 1,‖f q‖≤
      c*parisiCDFDistance μ ν*‖parisiCDF μ q-parisiCDF ν q‖ := by
    intro q hq
    rw [uIoc_of_le zero_le_one] at hq
    have hs:‖ξ.second q‖≤ξ.second 1:=by
      simpa only [Real.norm_eq_abs] using ξ.abs_second_le_at_one (abs_le.mpr ⟨by linarith [hq.1],hq.2⟩)
    have hm:=mixedGamma_CDF_L1_bound ξ h μ ν q ⟨hq.1.le,hq.2⟩
    dsimp only [f]
    rw [norm_mul,norm_mul,norm_sub_rev (parisiCDF ν q) (parisiCDF μ q)]
    have hstep:=mul_le_mul_of_nonneg_right hs (norm_nonneg (parisiCDF μ q-parisiCDF ν q))
    have hh:=mul_le_mul hstep hm (norm_nonneg _)
      (mul_nonneg (ξ.second_nonneg 1) (norm_nonneg _))
    convert hh using 1 <;>dsimp only [c];ring
  have hdom:IntervalIntegrable (fun q=>c*parisiCDFDistance μ ν*‖parisiCDF μ q-parisiCDF ν q‖)
      volume 0 1:= (parisiCDF_difference_intervalIntegrable μ ν 0 1).const_mul _
  rw [uIoc_of_le zero_le_one] at hb
  have hn:=intervalIntegral.norm_integral_le_of_norm_le zero_le_one (.of_forall hb) hdom
  rw [intervalIntegral.integral_const_mul] at hn
  change ‖∫q in (0:ℝ)..1,f q‖≤c*parisiCDFDistance μ ν*parisiCDFDistance μ ν at hn
  rw [he,norm_mul,Real.norm_of_nonneg (by norm_num : 0≤(1/2:ℝ))]
  have hh:=mul_le_mul_of_nonneg_left hn (show 0≤(1/2:ℝ) by norm_num)
  exact hh.trans_eq (by dsimp only [c];ring)

/-- The original signed-first-variation remainder has a covariance-only
quadratic constant, for every pair of genuine Parisi probability measures. -/
theorem mixedFunctional_quadratic_firstVariation (ξ:AdmissibleEvenMixture) (h:ℝ)
    (μ ν:ParisiMeasure) :
    |mixedFunctional ξ h ν-mixedFunctional ξ h μ+
      ((∫q,mixedFirstVariation ξ h μ q ∂(ν:Measure Overlap))-
        (∫q,mixedFirstVariation ξ h μ q ∂(μ:Measure Overlap)))|≤
      (ξ.second 1*mixedMomentL1Constant ξ/2)*(parisiCDFDistance μ ν)^2 := by
  rw [mixedFirstVariation_signed_pairing]
  have hlo:=mixedFunctional_supporting_plane ξ h μ ν
  have hhi:=mixedFunctional_supporting_plane ξ h ν μ
  have hnorm:=mixedDirectionalVariation_sum_bound ξ h μ ν
  have hupper:=le_abs_self (-(mixedDirectionalVariation ξ h μ ν+mixedDirectionalVariation ξ h ν μ))
  rw [abs_neg,←Real.norm_eq_abs] at hupper
  rw [abs_of_nonneg (by linarith : 0≤ mixedFunctional ξ h ν-mixedFunctional ξ h μ+
    -mixedDirectionalVariation ξ h μ ν)]
  linarith

end FourPapersCommon
