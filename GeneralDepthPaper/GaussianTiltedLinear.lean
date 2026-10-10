module

public import GeneralDepthPaper.GaussianTiltedBounds
public import Mathlib.Analysis.Normed.Operator.Mul

@[expose] public section


/-! The genuine normalized Gaussian average is linear in its observable. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64

def tiltedGaussianAverageCLM (p : ColeHopfParameter) : GaussianObservable→L[ℝ](ℝ →ᵇ ℝ) :=
  (ContinuousLinearMap.mul ℝ (ℝ →ᵇ ℝ) (Ring.inverse (centeredGaussianNormalizer p))).comp
    (gaussianPrecisionPrefactor (2*p.1.2) p.1.2 •
      (gaussianKernelAverageCLM (2*p.1.2).toNNReal).comp
        (ContinuousLinearMap.mul ℝ GaussianObservable
          (weightedTerminalKernel (gaussianPrecisionDifference p.1.2 (2*p.1.2),p.1.1•p.2))))

@[simp] theorem tiltedGaussianAverageCLM_apply (p : ColeHopfParameter) (H : GaussianObservable) :
    tiltedGaussianAverageCLM p H=tiltedGaussianOperator (p,H) := rfl

theorem tiltedGaussianOperator_add (p : ColeHopfParameter) (H J : GaussianObservable) :
    tiltedGaussianOperator (p,H+J)=tiltedGaussianOperator (p,H)+tiltedGaussianOperator (p,J) :=
  (tiltedGaussianAverageCLM p).map_add H J

theorem tiltedGaussianOperator_smul (p : ColeHopfParameter) (c : ℝ) (H : GaussianObservable) :
    tiltedGaussianOperator (p,c•H)=c•tiltedGaussianOperator (p,H) :=
  (tiltedGaussianAverageCLM p).map_smul c H

theorem norm_tiltedGaussianAverageCLM_le_one (p : ColeHopfParameter) (hv : 0<p.1.2) :
    ‖tiltedGaussianAverageCLM p‖≤1 := by
  apply (tiltedGaussianAverageCLM p).opNorm_le_bound zero_le_one
  intro H
  simpa only [tiltedGaussianAverageCLM_apply,one_mul] using norm_tiltedGaussianOperator_le (p,H) hv

end GeneralDepthPaper
