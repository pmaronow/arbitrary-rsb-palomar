module

public import FourPapersCommon.ParisiMomentL1
public import FourPapersCommon.MixedFirstVariation
public import FourPapersCommon.MixtureBounds

@[expose] public section


/-! Original-overlap CDF-L1 estimates for the actual mixed-even PDE and
diffusion moments. The variance clock is integrated by genuine substitution. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace FourPapersCommon
open Paper
set_option maxHeartbeats 800000

theorem mixedMeasure_CDF_L1_bound (ξ:AdmissibleEvenMixture) (μ ν:ParisiMeasure) :
    parisiCDFDistance (mixedMeasure ξ μ) (mixedMeasure ξ ν)≤
      (ξ.second 1/ξ.variance)*parisiCDFDistance μ ν := by
  let f:=fun q:ℝ=>‖parisiCDF μ q-parisiCDF ν q‖
  let w:=fun q:ℝ=>ξ.second q/ξ.variance
  have hfi:IntervalIntegrable f volume 0 1:=parisiCDF_difference_intervalIntegrable μ ν 0 1
  have hwi:ContinuousOn w (uIcc (0:ℝ) 1):=by
    rw [uIcc_of_le zero_le_one]
    exact (ξ.continuousOn_second.mono (fun q hq=>⟨by linarith [hq.1],hq.2⟩)).div_const _
  have he : parisiCDFDistance (mixedMeasure ξ μ) (mixedMeasure ξ ν)=
      ∫q in (0:ℝ)..1,f q*w q := by
    have hs:=integral_mixedClock_substitution ξ
      (fun q=>‖parisiCDF (mixedMeasure ξ μ) q-parisiCDF (mixedMeasure ξ ν) q‖)
      (q:=1) (by norm_num)
    rw [ξ.clock_one] at hs
    rw [parisiCDFDistance,←hs]
    apply intervalIntegral.integral_congr
    intro q hq
    rw [uIcc_of_le zero_le_one] at hq
    dsimp only [f,w]
    rw [parisiCDF_mixedMeasure ξ μ q hq,parisiCDF_mixedMeasure ξ ν q hq]
  rw [he]
  have hm:=intervalIntegral.integral_mono_on zero_le_one (hfi.mul_continuousOn hwi)
    (hfi.mul_const (ξ.second 1/ξ.variance)) (fun q hq=>by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact div_le_div_of_nonneg_right
        (ξ.second_le_at_one (abs_le.mpr ⟨by linarith [hq.1],hq.2⟩)) ξ.variance_pos.le)
  simpa only [intervalIntegral.integral_mul_const,parisiCDFDistance,f,mul_comm] using hm

def mixedMomentL1Constant (ξ:AdmissibleEvenMixture) : ℝ :=
  parisiMomentL1Constant (mixedBeta ξ)*(ξ.second 1/ξ.variance)

theorem mixedMomentL1Constant_nonneg (ξ:AdmissibleEvenMixture) : 0≤ mixedMomentL1Constant ξ:=
  mul_nonneg (parisiMomentL1Constant_nonneg _) (div_nonneg (ξ.second_nonneg 1) ξ.variance_pos.le)

theorem mixedGamma_CDF_L1_bound (ξ:AdmissibleEvenMixture) (h:ℝ) (μ ν:ParisiMeasure)
    (q:ℝ) (hq:q∈Icc (0:ℝ) 1) :
    ‖mixedGamma ξ h μ q-mixedGamma ξ h ν q‖≤ mixedMomentL1Constant ξ*parisiCDFDistance μ ν := by
  rw [mixedGamma_eq_selected,mixedGamma_eq_selected]
  exact (selectedParisiSecondMoment_CDF_L1_bound (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
    (mixedMeasure ξ μ) (mixedMeasure ξ ν) (ξ.clock q) (ξ.clock_mem_unitInterval hq)).trans
    ((mul_le_mul_of_nonneg_left (mixedMeasure_CDF_L1_bound ξ μ ν)
      (parisiMomentL1Constant_nonneg _)).trans_eq (by dsimp only [mixedMomentL1Constant];ring))

end FourPapersCommon
