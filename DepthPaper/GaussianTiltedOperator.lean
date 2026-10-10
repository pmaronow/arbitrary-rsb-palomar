module

public import DepthPaper.GaussianNormalizerUnits

@[expose] public section


/-! Actual Gaussian tilted averages of bounded displacement/space observables.
The map is jointly analytic in mass, variance, terminal datum and observable;
the zero-mass branch is the original Gaussian averaging operator. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction ContDiff
namespace DepthPaper
set_option maxSynthPendingDepth 32
abbrev GaussianObservable := (ℝ×ℝ) →ᵇ ℝ
abbrev TiltedParameter := ColeHopfParameter×GaussianObservable

def referenceGaussianNumerator (w : ℝ) (p : TiltedParameter) : ℝ →ᵇ ℝ :=
  gaussianPrecisionPrefactor w p.1.1.2 • gaussianKernelAverage w.toNNReal
    (weightedTerminalKernel (gaussianPrecisionDifference p.1.1.2 w,p.1.1.1•p.1.2)*p.2)

def centeredGaussianNumerator (p : TiltedParameter) : ℝ →ᵇ ℝ :=
  referenceGaussianNumerator (2*p.1.1.2) p

theorem referenceGaussianNumerator_apply (w : ℝ) (p : TiltedParameter)
    (hv : 0<p.1.1.2) (hvw : p.1.1.2<w) (x : ℝ) :
    referenceGaussianNumerator w p x=
      ∫d,Real.exp (p.1.1.1*(terminalValue p.1.2 (x+d)-terminalValue p.1.2 x))*p.2 (d,x)
        ∂gaussianReal 0 p.1.1.2.toNNReal := by
  have hw : 0<w := hv.trans hvw
  have hvN : (0:ℝ≥0)<p.1.1.2.toNNReal := by
    rw [←NNReal.coe_lt_coe,NNReal.coe_zero,Real.coe_toNNReal _ hv.le]
    exact hv
  have hwN : (0:ℝ≥0)<w.toNNReal := by
    rw [←NNReal.coe_lt_coe,NNReal.coe_zero,Real.coe_toNNReal _ hw.le]
    exact hw
  have hb : 0<gaussianPrecisionDifference p.1.1.2 w := gaussianPrecisionDifference_pos hv hvw
  change gaussianPrecisionPrefactor w p.1.1.2*(∫d,
    weightedTerminalKernel (gaussianPrecisionDifference p.1.1.2 w,p.1.1.1•p.1.2) (d,x)*p.2 (d,x)
    ∂gaussianReal 0 w.toNNReal)=_
  rw [integral_gaussianReal_eq_integral_smul hwN.ne',
    integral_gaussianReal_eq_integral_smul hvN.ne',←integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun d=>by
    dsimp only
    simp only [smul_eq_mul]
    rw [weightedTerminalKernel_apply _ hb,
      gaussianPDFReal_precision_ratio p.1.1.2.toNNReal w.toNNReal hvN hwN]
    simp only [Real.coe_toNNReal _ hv.le,Real.coe_toNNReal _ hw.le,
      terminalValue_smul,gaussianPrecisionPrefactor]
    simp only [mul_assoc]
    rw [←mul_assoc (Real.exp _) (Real.exp _) (p.2 (d,x)),←Real.exp_add]
    congr 3 <;> ring

theorem centeredGaussianNumerator_apply (p : TiltedParameter)
    (hv : 0<p.1.1.2) (x : ℝ) :
    centeredGaussianNumerator p x=
      ∫d,Real.exp (p.1.1.1*(terminalValue p.1.2 (x+d)-terminalValue p.1.2 x))*p.2 (d,x)
        ∂gaussianReal 0 p.1.1.2.toNNReal :=
  referenceGaussianNumerator_apply (2*p.1.1.2) p hv (by linarith) x

theorem analyticAt_referenceGaussianNumerator (w : ℝ) (p : TiltedParameter)
    (hv : 0<p.1.1.2) (hvw : p.1.1.2<w) :
    AnalyticAt ℝ (referenceGaussianNumerator w) p := by
  have hvA : AnalyticAt ℝ (fun q:TiltedParameter=>q.1.1.2) p :=
    analyticAt_snd.comp (analyticAt_fst.comp analyticAt_fst)
  have hmA : AnalyticAt ℝ (fun q:TiltedParameter=>q.1.1.1) p :=
    analyticAt_fst.comp (analyticAt_fst.comp analyticAt_fst)
  have hgA : AnalyticAt ℝ (fun q:TiltedParameter=>q.1.2) p :=
    analyticAt_snd.comp analyticAt_fst
  have hs : AnalyticAt ℝ (fun q:TiltedParameter=>Real.sqrt (2*Real.pi*q.1.1.2)) p :=
    (Real.contDiffAt_sqrt (n:=ω) (show 2*Real.pi*p.1.1.2≠0 by positivity)).analyticAt.comp
      (f:=fun q:TiltedParameter=>2*Real.pi*q.1.1.2) (analyticAt_const.mul hvA)
  have hpref : AnalyticAt ℝ (fun q:TiltedParameter=>gaussianPrecisionPrefactor w q.1.1.2) p :=
    analyticAt_const.div hs (by apply ne_of_gt; positivity)
  have hprecision : AnalyticAt ℝ (fun q:TiltedParameter=>gaussianPrecisionDifference q.1.1.2 w) p :=
    (analyticAt_const.div (analyticAt_const.mul hvA) (show 2*p.1.1.2≠0 by positivity)).sub analyticAt_const
  have hkernel : AnalyticAt ℝ (fun q:TiltedParameter=>
      weightedTerminalKernel (gaussianPrecisionDifference q.1.1.2 w,q.1.1.1•q.1.2)) p :=
    (analyticAt_weightedTerminalKernel _ (gaussianPrecisionDifference_pos hv hvw)).comp
      (hprecision.prod (hmA.smul hgA))
  have havg : AnalyticAt ℝ (fun q:TiltedParameter=>gaussianKernelAverage w.toNNReal
      (weightedTerminalKernel (gaussianPrecisionDifference q.1.1.2 w,q.1.1.1•q.1.2)*q.2)) p :=
    ((gaussianKernelAverageCLM w.toNNReal).analyticAt _).comp (hkernel.mul analyticAt_snd)
  exact hpref.smul havg

theorem analyticAt_centeredGaussianNumerator (p : TiltedParameter) (hv : 0<p.1.1.2) :
    AnalyticAt ℝ centeredGaussianNumerator p := by
  have hlocal : ∀ᶠq:TiltedParameter in 𝓝 p,0<q.1.1.2 ∧ q.1.1.2<2*p.1.1.2 :=
    (show Tendsto (fun q:TiltedParameter=>q.1.1.2) (𝓝 p) (𝓝 p.1.1.2) from
      (continuous_snd.comp (continuous_fst.comp continuous_fst)).tendsto p)
      (Ioo_mem_nhds hv (by linarith))
  apply (analyticAt_referenceGaussianNumerator (2*p.1.1.2) p hv (by linarith)).congr
  filter_upwards [hlocal] with q hq
  ext x
  rw [referenceGaussianNumerator_apply _ q hq.1 hq.2,centeredGaussianNumerator_apply q hq.1]

def tiltedGaussianOperator (p : TiltedParameter) : ℝ →ᵇ ℝ :=
  Ring.inverse (centeredGaussianNormalizer p.1)*centeredGaussianNumerator p

theorem analyticAt_tiltedGaussianOperator (p : TiltedParameter) (hv : 0<p.1.1.2) :
    AnalyticAt ℝ tiltedGaussianOperator p := by
  exact ((analyticAt_inverse_centeredGaussianNormalizer p.1 hv).comp
    (f:=fun q:TiltedParameter=>q.1) analyticAt_fst).mul
    (analyticAt_centeredGaussianNumerator p hv)

/-- Inverting in the Banach algebra agrees with pointwise reciprocal. -/
theorem inverse_centeredGaussianNormalizer_apply (p : ColeHopfParameter)
    (hv : 0<p.1.2) (x : ℝ) :
    Ring.inverse (centeredGaussianNormalizer p) x=(centeredGaussianNormalizer p x)⁻¹ := by
  have hmul := Ring.mul_inverse_cancel (centeredGaussianNormalizer p)
    (isUnit_centeredGaussianNormalizer p hv)
  have hx := congrArg (fun f:ℝ →ᵇ ℝ=>f x) hmul
  change centeredGaussianNormalizer p x*Ring.inverse (centeredGaussianNormalizer p) x=1 at hx
  have hn : centeredGaussianNormalizer p x≠0 :=
    (gaussianNormalizerLower_pos p |>.trans_le (gaussianNormalizerLower_le p hv x)).ne'
  apply mul_left_cancel₀ hn
  rw [mul_inv_cancel₀ hn]
  exact hx

theorem tiltedGaussianOperator_apply (p : TiltedParameter) (hv : 0<p.1.1.2) (x : ℝ) :
    tiltedGaussianOperator p x=
      (∫d,Real.exp (p.1.1.1*(terminalValue p.1.2 (x+d)-terminalValue p.1.2 x))*p.2 (d,x)
        ∂gaussianReal 0 p.1.1.2.toNNReal)/
      (∫d,Real.exp (p.1.1.1*(terminalValue p.1.2 (x+d)-terminalValue p.1.2 x))
        ∂gaussianReal 0 p.1.1.2.toNNReal) := by
  change Ring.inverse (centeredGaussianNormalizer p.1) x*centeredGaussianNumerator p x=_
  rw [inverse_centeredGaussianNormalizer_apply p.1 hv,
    centeredGaussianNumerator_apply p hv,centeredGaussianNormalizer_apply p.1 hv]
  ring

end DepthPaper
