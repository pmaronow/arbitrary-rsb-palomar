module

public import DepthPaper.GaussianBoundaryJets
public import Common.Mathlib.Probability.Distributions.Gaussian.HeatSemigroup

@[expose] public section


/-! The genuine Gaussian heat derivative on the closed nonnegative variance
axis, including its one-sided zero-variance endpoint. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace DepthPaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64
open ColeHopfFoundation.ProbabilityTheory

theorem hasDerivWithinAt_gaussianHeat_variance_nonneg
    (H H' H'' : ℝ → ℝ)
    (hd : ∀y,HasDerivAt H (H' y) y) (hd' : ∀y,HasDerivAt H' (H'' y) y)
    (hg : HasExpGrowth H) (hg' : HasExpGrowth H') (hg'' : HasExpGrowth H'')
    (hc'' : Continuous H'') (V : ℝ) (hV : 0 ≤ V) (x : ℝ) :
    HasDerivWithinAt (fun v : ℝ => ∫z,H (x+z) ∂gaussianReal 0 v.toNNReal)
      ((1/2:ℝ)*(∫z,H'' (x+z) ∂gaussianReal 0 V.toNNReal)) (Ici 0) V := by
  rcases eq_or_lt_of_le hV with h0 | hpos
  · subst V
    simpa only [Real.toNNReal_zero,integral_comp_add_gaussianReal_zero_var] using
      hasDerivWithinAt_integral_comp_add_gaussianReal_var_zero hd hd' hg hg' hg'' hc'' x
  · exact (hasDerivAt_integral_comp_add_gaussianReal_var hd hd' hg hg' hg'' hc'' hpos x).hasDerivWithinAt

theorem integrable_bcf_exp_terminal_shift (a : ℝ) (v : ℝ≥0) (g : TerminalSpace)
    (G : ℝ →ᵇ ℝ) (x : ℝ) :
    Integrable (fun z => G (x+z)*Real.exp (a*terminalValue g (x+z))) (gaussianReal 0 v) :=
  (((hasExpGrowth_bcf G).mul ((hasLinearGrowth_terminalValue g).exp_mul a)).comp_add_const x).integrable_gaussianReal
      ((G.continuous.comp (continuous_const.add continuous_id)).mul
        (Real.continuous_exp.comp (continuous_const.mul
          ((contDiff_terminalValue g).continuous.comp (continuous_const.add continuous_id))))).aestronglyMeasurable

theorem uncenteredGaussianTiltMean_add (a : ℝ) (v : ℝ≥0) (g : TerminalSpace)
    (G H : ℝ →ᵇ ℝ) (x : ℝ) :
    uncenteredGaussianTiltMean a v g (G+H) x =
      uncenteredGaussianTiltMean a v g G x+uncenteredGaussianTiltMean a v g H x := by
  unfold uncenteredGaussianTiltMean
  simp only [BoundedContinuousFunction.add_apply,add_mul]
  rw [integral_add (integrable_bcf_exp_terminal_shift a v g G x)
    (integrable_bcf_exp_terminal_shift a v g H x),add_div]

theorem uncenteredGaussianTiltMean_smul (a : ℝ) (v : ℝ≥0) (g : TerminalSpace)
    (c : ℝ) (G : ℝ →ᵇ ℝ) (x : ℝ) :
    uncenteredGaussianTiltMean a v g (c•G) x = c*uncenteredGaussianTiltMean a v g G x := by
  unfold uncenteredGaussianTiltMean
  simp only [BoundedContinuousFunction.smul_apply,smul_eq_mul,mul_assoc]
  rw [integral_const_mul,mul_div_assoc]

theorem varianceGaussianTiltMean_apply_nonneg (H : TerminalSpace → ℝ →ᵇ ℝ)
    (p : ColeHopfParameter) (hv : 0 ≤ p.1.2) (hU : UniformContinuous (H p.2)) (x : ℝ) :
    varianceGaussianTiltMean H p x =
      uncenteredGaussianTiltMean p.1.1 p.1.2.toNNReal p.2 (H p.2) x := by
  rcases eq_or_lt_of_le hv with h0 | hpos
  · have hp : p = ((p.1.1,0),p.2) := by ext <;> simp_all
    rw [hp,varianceGaussianTiltMean_zero]
    simp [uncenteredGaussianTiltMean]
  · rw [varianceGaussianTiltMean_eq_actual H p hpos hU,
      gaussianTerminalTiltMean_apply p (H p.2) hpos x]

end DepthPaper
