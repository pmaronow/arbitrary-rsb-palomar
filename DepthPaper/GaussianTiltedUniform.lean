module

public import DepthPaper.GaussianTiltedSpatial
public import DepthPaper.TerminalTranslation

@[expose] public section


/-! Actual Gaussian tilted means preserve uniform continuity. The proof uses
strong translation continuity of each terminal datum and each observable, rather
than operator-norm continuity of translations. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace DepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000

def shiftedGaussianObservableCLM : (ℝ →ᵇ ℝ)→L[ℝ]GaussianObservable :=
  BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    ⟨fun s:ℝ×ℝ=>s.2+s.1,by fun_prop⟩

@[simp] theorem shiftedGaussianObservableCLM_apply (G : ℝ →ᵇ ℝ) :
    shiftedGaussianObservableCLM G=shiftedGaussianObservable G := rfl

theorem gaussianTerminalTiltMean_translate (p : ColeHopfParameter) (hv : 0<p.1.2)
    (G : ℝ →ᵇ ℝ) (r : ℝ) :
    bcfSpatialTranslate r (gaussianTerminalTiltMean p G)=
      gaussianTerminalTiltMean (p.1,terminalTranslate r p.2) (bcfSpatialTranslate r G) := by
  ext x
  rw [bcfSpatialTranslate_apply,gaussianTerminalTiltMean_apply _ _ hv,
    gaussianTerminalTiltMean_apply (p.1,terminalTranslate r p.2) _ hv]
  unfold uncenteredGaussianTiltMean
  simp only [bcfSpatialTranslate_apply,terminalValue_translate,add_assoc,add_comm,add_left_comm]

theorem uniformContinuous_gaussianTerminalTiltMean (p : ColeHopfParameter)
    (hv : 0<p.1.2) (G : ℝ →ᵇ ℝ) (hG : UniformContinuous G) :
    UniformContinuous (gaussianTerminalTiltMean p G) := by
  apply uniformContinuous_of_bcfSpatialTranslate
  let q (r : ℝ) : TiltedParameter :=
    ((p.1,terminalTranslate r p.2),shiftedGaussianObservable (bcfSpatialTranslate r G))
  have hq : Continuous q := by
    exact (continuous_const.prodMk (continuous_terminalTranslate p.2)).prodMk
      (shiftedGaussianObservableCLM.continuous.comp (continuous_bcfSpatialTranslate G hG))
  have hq0 : q 0=(p,shiftedGaussianObservable G) := by simp [q]
  have hmean : ContinuousAt (fun r:ℝ=>tiltedGaussianOperator (q r)) 0 := by
    have hA := (analyticAt_tiltedGaussianOperator (q 0) hv).continuousAt
    exact hA.comp hq.continuousAt
  convert! hmean using 1
  funext r
  exact gaussianTerminalTiltMean_translate p hv G r

end DepthPaper
