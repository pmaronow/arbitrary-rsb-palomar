module

public import DepthPaper.ColeHopfGradientTime

@[expose] public section


/-! The exact coupled-invariant equality used in the curvature proof. The
averages are the actual normalized Gaussian tilt, including mass zero and
variance zero. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem gaussianTerminalTiltMean_one (p : ColeHopfParameter) (hv : 0 < p.1.2) :
    gaussianTerminalTiltMean p 1 = 1 := by
  ext x
  rw [gaussianTerminalTiltMean,tiltedGaussianOperator_apply _ hv]
  have hp := integral_exp_pos (integrable_centeredGaussianExponential p.1.1 p.2 p.1.2.toNNReal x)
  simp only [shiftedGaussianObservable_apply,BoundedContinuousFunction.coe_one,Pi.one_apply,mul_one]
  exact div_self hp.ne'

theorem gaussianTerminalTiltMean_sub (p : ColeHopfParameter) (G H : ℝ →ᵇ ℝ) :
    gaussianTerminalTiltMean p (G-H) = gaussianTerminalTiltMean p G-gaussianTerminalTiltMean p H := by
  rw [sub_eq_add_neg,gaussianTerminalTiltMean_add]
  have hn := gaussianTerminalTiltMean_smul p (-1) H
  simpa only [neg_one_smul,sub_eq_add_neg] using congrArg
    (fun K : ℝ →ᵇ ℝ => gaussianTerminalTiltMean p G+K) hn

def terminalTiltVariance (p : ColeHopfParameter) (x : ℝ) : ℝ :=
  varianceGaussianTiltMean (fun g => terminalJet g 0^2) p x-
    (varianceGaussianTiltMean (fun g => terminalJet g 0) p x)^2

/-- Display 16: the coupled invariant has an exact mean-plus-variance
decomposition, rather than only a preservation inequality. -/
theorem coleHopf_coupled_invariant_identity (p : ColeHopfParameter)
    (hv : 0 ≤ p.1.2) (x : ℝ) :
    (1-(terminalJet (coleHopfTerminal p) 0 x)^2)-terminalJet (coleHopfTerminal p) 1 x =
      varianceGaussianTiltMean (fun g => (1:ℝ →ᵇ ℝ)-terminalJet g 0^2-terminalJet g 1) p x+
        (1-p.1.1)*terminalTiltVariance p x := by
  by_cases hp : 0 < p.1.2
  · have hu : UniformContinuous (((1:ℝ →ᵇ ℝ)-terminalJet p.2 0^2-terminalJet p.2 1) : ℝ → ℝ) := by
      change UniformContinuous (fun x => 1-(terminalJet p.2 0 x)^2-terminalJet p.2 1 x)
      exact ((uniformContinuous_const.sub
        (uniformContinuous_bcf_pow _ (uniformContinuous_terminalJet p.2 0) 2)).sub
        (uniformContinuous_terminalJet p.2 1))
    have hj0 := terminalJet_coleHopfTerminal_boundary p hv
    simp only [hj0,Matrix.cons_val_zero,Matrix.cons_val_one,
      boundaryGaussianJetOne_eq p hp,boundaryGaussianJetTwo_eq p hp,
      varianceGaussianTiltMean_eq_actual (fun g => (1:ℝ →ᵇ ℝ)-terminalJet g 0^2-terminalJet g 1) p hp hu,
      varianceGaussianTiltMean_eq_actual (fun g => terminalJet g 0) p hp (uniformContinuous_terminalJet p.2 0),
      varianceGaussianTiltMean_eq_actual (fun g => terminalJet g 0^2) p hp
        (uniformContinuous_bcf_pow _ (uniformContinuous_terminalJet p.2 0) 2),
      terminalTiltVariance]
    rw [gaussianTerminalTiltMean_sub,gaussianTerminalTiltMean_sub,gaussianTerminalTiltMean_one p hp]
    simp only [BoundedContinuousFunction.sub_apply,BoundedContinuousFunction.coe_one,Pi.one_apply,
      gaussianTerminalTiltMean_jet_zero]
    change (1-(terminalGaussianJetOne p x)^2)-terminalGaussianJetTwo p x =
      1-gaussianTerminalTiltMean p (terminalJet p.2 0^2) x-
        gaussianTerminalTiltMean p (terminalJet p.2 1) x+
      (1-p.1.1)*(gaussianTerminalTiltMean p (terminalJet p.2 0^2) x-
        (terminalGaussianJetOne p x)^2)
    simp only [terminalGaussianJetTwo,terminalGaussianMoment,gaussianTerminalTiltMean,
      shiftedGaussianObservable_pow,shiftedGaussianObservable_jet,
      BoundedContinuousFunction.add_apply,BoundedContinuousFunction.smul_apply,
      BoundedContinuousFunction.sub_apply,BoundedContinuousFunction.pow_apply,smul_eq_mul]
    ring
  · have h0 : p.1.2 = 0 := le_antisymm (le_of_not_gt hp) hv
    have he : p = ((p.1.1,0),p.2) := by ext <;> simp_all
    rw [he,coleHopfTerminal_zero_variance]
    simp [terminalTiltVariance]

end DepthPaper
