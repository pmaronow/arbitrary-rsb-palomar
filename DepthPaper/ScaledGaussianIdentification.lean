module

public import DepthPaper.ScaledGaussianMean

@[expose] public section


/-! The standard-deviation kernels are the actual Gaussian tilted moments,
including the degenerate Gaussian measure at zero variance. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace DepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
open ColeHopfFoundation.ProbabilityTheory

theorem scaledGaussianTiltMean_apply (H : ColeHopfParameter → ℝ →ᵇ ℝ)
    (p : ColeHopfParameter) (hU : UniformContinuous (H p)) (x : ℝ) :
    scaledGaussianTiltMean H p x =
      (∫z,Real.exp (p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x)) *
          H p (x+p.1.2*z) ∂gaussianReal 0 1) /
      (∫z,Real.exp (p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x))
        ∂gaussianReal 0 1) := by
  rw [scaledGaussianTiltMean,BoundedContinuousFunction.mul_apply,
    inverse_scaledGaussianNormalizer_apply,scaledGaussianNormalizer_apply]
  have he : scaledGaussianTiltNumerator H p x =
      ∫z,Real.exp (p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x)) *
        H p (x+p.1.2*z) ∂gaussianReal 0 1 := by
    change (BoundedContinuousFunction.evalCLM ℝ x)
      (∫z,scaledGaussianKernel p z * bcfSpatialTranslate (p.1.2*z) (H p)
        ∂gaussianReal 0 1) = _
    rw [←ContinuousLinearMap.integral_comp_comm _ (integrable_scaledGaussianTiltNumerator H p hU)]
    simp only [BoundedContinuousFunction.evalCLM_apply,BoundedContinuousFunction.mul_apply,
      scaledGaussianKernel_apply,bcfSpatialTranslate_apply]
  rw [he,div_eq_mul_inv,mul_comm]

def varianceGaussianTiltMean (H : TerminalSpace → ℝ →ᵇ ℝ)
    (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  scaledGaussianTiltMean (fun q => H q.2) ((p.1.1,Real.sqrt p.1.2),p.2)

theorem continuous_varianceGaussianTiltMean (H : TerminalSpace → ℝ →ᵇ ℝ)
    (hH : Continuous H) (hU : ∀g,UniformContinuous (H g)) :
    Continuous (varianceGaussianTiltMean H) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hdata : ContinuousAt (fun q : ColeHopfParameter =>
      ((q.1.1,Real.sqrt q.1.2),q.2)) p := by
    fun_prop
  exact (continuousAt_scaledGaussianTiltMean (fun q => H q.2)
    (fun q => hU q.2) _ (hH.comp continuous_snd).continuousAt).comp
      (f := fun q : ColeHopfParameter => ((q.1.1,Real.sqrt q.1.2),q.2)) hdata

@[simp] theorem varianceGaussianTiltMean_zero (H : TerminalSpace → ℝ →ᵇ ℝ)
    (a : ℝ) (g : TerminalSpace) : varianceGaussianTiltMean H ((a,0),g) = H g := by
  simp [varianceGaussianTiltMean]

theorem varianceGaussianTiltMean_eq_actual (H : TerminalSpace → ℝ →ᵇ ℝ)
    (p : ColeHopfParameter) (hv : 0 < p.1.2) (hU : UniformContinuous (H p.2)) :
    varianceGaussianTiltMean H p = gaussianTerminalTiltMean p (H p.2) := by
  ext x
  rw [varianceGaussianTiltMean,scaledGaussianTiltMean_apply _ _ hU,
    gaussianTerminalTiltMean,tiltedGaussianOperator_apply _ hv]
  simp only [shiftedGaussianObservable_apply]
  have hs : Real.sqrt (p.1.2.toNNReal : ℝ) = Real.sqrt p.1.2 := by
    rw [Real.coe_toNNReal _ hv.le]
  have hn : Continuous (fun d : ℝ =>
      Real.exp (p.1.1*(terminalValue p.2 (x+d)-terminalValue p.2 x)) * H p.2 (x+d)) := by
    have hg := (contDiff_terminalValue p.2).continuous
    have hG := (H p.2).continuous
    fun_prop
  have hd : Continuous (fun d : ℝ =>
      Real.exp (p.1.1*(terminalValue p.2 (x+d)-terminalValue p.2 x))) := by
    have hg := (contDiff_terminalValue p.2).continuous
    fun_prop
  rw [integral_gaussianReal_eq_integral_sqrt_mul p.1.2.toNNReal hn.aestronglyMeasurable,
    integral_gaussianReal_eq_integral_sqrt_mul p.1.2.toNNReal hd.aestronglyMeasurable,hs]

end DepthPaper
