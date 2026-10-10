module

public import DepthPaper.Curvature
public import FourPapersCommon.MixedFiniteDiffusionLaw
public import FRSB.BrownianMarkov
public import Mathlib.Probability.Moments.Variance

@[expose] public section


/-! A uniform compact-mass estimate for the actual original-clock mixed
diffusion. The drift is bounded by the accumulated covariance ξ′(q), while
the noise has exactly the centered Gaussian law of variance ξ′(q). -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace DepthPaper
open FourPapersCommon
set_option maxHeartbeats 900000

def covarianceDriver (Ξ:AdmissibleCovariance) (q:ℝ) (sample:BrownianSample):ℝ :=
  mixedBeta Ξ.toEvenMixture*Paper.canonicalBrownian (Ξ.clock q).toNNReal sample

theorem optimalState_driver_displacement (Ξ:AdmissibleCovariance) (μ:ParisiMeasure)
    {q:ℝ} (hq:q∈Icc (0:ℝ) 1) (sample:BrownianSample) :
    |optimalState Ξ μ sample q-covarianceDriver Ξ q sample|≤Ξ.first q := by
  rw [optimalState_integral_equation Ξ μ sample hq]
  simp only [covarianceDriver,add_sub_cancel_left]
  have hi:IntervalIntegrable Ξ.second volume 0 q:=Ξ.continuous_second.intervalIntegrable _ _
  have hh:=intervalIntegral.norm_integral_le_of_norm_le
    (f:=fun s:ℝ=>Ξ.second s*Paper.parisiCDF μ s*gradient Ξ μ s (optimalState Ξ μ sample s)) hq.1
    (.of_forall fun s hs=>by
      have hn:=Ξ.second_nonneg hs.1.le
      have hm0:=Paper.parisiCDF_nonneg μ s
      have hm1:=Paper.parisiCDF_le_one μ s
      have hg:=norm_gradient_le_one Ξ μ s (optimalState Ξ μ sample s)
      rw [norm_mul,norm_mul,Real.norm_eq_abs,abs_of_nonneg hn,
        Real.norm_eq_abs,abs_of_nonneg hm0]
      calc
        Ξ.second s*Paper.parisiCDF μ s*‖gradient Ξ μ s (optimalState Ξ μ sample s)‖
            ≤Ξ.second s*1*1:=by gcongr
        _=Ξ.second s:=by ring) hi
  have hf:(∫s in 0..q,Ξ.second s)=Ξ.first q:=by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _=>Ξ.hasDerivAt_first s) hi,
      Ξ.first_zero,sub_zero]
  simpa only [Real.norm_eq_abs,hf] using hh

theorem hasLaw_covarianceDriver (Ξ:AdmissibleCovariance) {q:ℝ}
    (hq:q∈Icc (0:ℝ) 1) :
    HasLaw (covarianceDriver Ξ q) (gaussianReal 0 (Ξ.first q).toNNReal)
      Paper.canonicalBrownianMeasure := by
  have hh:=FRSB.hasLaw_scaledBrownian (mixedBeta Ξ.toEvenMixture) (Ξ.clock q).toNNReal
  have hv:mixedBeta Ξ.toEvenMixture^2*((Ξ.clock q).toNNReal:ℝ)=Ξ.first q:=by
    rw [mixedBeta_sq,Real.coe_toNNReal _ (Ξ.clock_mem_unit hq).1]
    simp only [AdmissibleCovariance.toEvenMixture_variance,AdmissibleCovariance.clock]
    field_simp [Ξ.variance_pos.ne']
  rw [hv] at hh
  exact hh

theorem measurable_covarianceDriver (Ξ:AdmissibleCovariance) (q:ℝ) :
    Measurable (covarianceDriver Ξ q):=
  (Paper.measurable_canonicalBrownian _).const_mul _

theorem optimalState_compact_mass (Ξ:AdmissibleCovariance) (μ:ParisiMeasure)
    {q B:ℝ} (hq:q∈Icc (0:ℝ) 1) (hB:0≤B) (hvar:Ξ.first q≤B) :
    (1/2:ℝ)≤Paper.canonicalBrownianMeasure.real
      {sample:BrownianSample | |optimalState Ξ μ sample q|≤3*B+2} := by
  let Z:=covarianceDriver Ξ q
  let c:ℝ:=2*(B+1)
  have hc:0 < c:=by dsimp [c];linarith
  have hLaw:=hasLaw_covarianceDriver Ξ hq
  have hmean:(∫sample,Z sample ∂Paper.canonicalBrownianMeasure)=0:=by
    simpa only [Z,integral_id_gaussianReal] using hLaw.integral_eq
  have hvariance:variance Z Paper.canonicalBrownianMeasure=Ξ.first q:=by
    rw [hLaw.variance_eq,variance_id_gaussianReal,Real.coe_toNNReal _ (Ξ.first_nonneg hq.1)]
  have hmem:MemLp Z 2 Paper.canonicalBrownianMeasure:=
    hLaw.memLp (memLp_id_gaussianReal (2:ℝ≥0))
  have htail:=meas_ge_le_variance_div_sq hmem hc
  rw [hmean,hvariance] at htail
  simp only [sub_zero] at htail
  have hr:Ξ.first q/c^2≤1/2:=by
    apply (div_le_iff₀ (sq_pos_of_pos hc)).mpr
    dsimp [c]
    nlinarith [sq_nonneg B]
  have htail2:Paper.canonicalBrownianMeasure {sample | c≤|Z sample|}≤(1/2:ℝ≥0∞):=by
    exact htail.trans (by simpa using ENNReal.ofReal_le_ofReal hr)
  have htailreal:Paper.canonicalBrownianMeasure.real {sample | c≤|Z sample|}≤1/2:=by
    exact (ENNReal.toReal_mono (by norm_num : (1/2:ℝ≥0∞)≠⊤) htail2).trans_eq (by norm_num)
  have htmeas:MeasurableSet {sample:BrownianSample | c≤|Z sample|}:=
    measurableSet_le measurable_const (measurable_covarianceDriver Ξ q).abs
  have hgood:(1/2:ℝ)≤Paper.canonicalBrownianMeasure.real {sample | |Z sample| < c}:=by
    have hh:=measureReal_add_measureReal_compl (μ:=Paper.canonicalBrownianMeasure) htmeas
    have he:{sample:BrownianSample | c≤|Z sample|}ᶜ={sample | |Z sample| < c}:=by
      ext sample;simp
    rw [he] at hh
    simp only [measureReal_def,measure_univ,ENNReal.toReal_one] at hh
    change Paper.canonicalBrownianMeasure.real {sample | c≤|Z sample|}+
      Paper.canonicalBrownianMeasure.real {sample | |Z sample| < c}=1 at hh
    linarith
  apply hgood.trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro sample hs
  have hd:=optimalState_driver_displacement Ξ μ hq sample
  have habs:|optimalState Ξ μ sample q|≤|Z sample|+Ξ.first q:=by
    calc
      _=|(optimalState Ξ μ sample q-Z sample)+Z sample|:=by congr 1;ring
      _≤|optimalState Ξ μ sample q-Z sample|+|Z sample|:=abs_add_le _ _
      _≤|Z sample|+Ξ.first q:=by dsimp [Z];linarith
  change |Z sample| < c at hs
  dsimp [c] at hs
  change |optimalState Ξ μ sample q|≤3*B+2
  linarith

end DepthPaper
