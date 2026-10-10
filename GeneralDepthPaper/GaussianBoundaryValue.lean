module

public import GeneralDepthPaper.ScaledGaussianIncrement

@[expose] public section


/-! Identification of the continuous zero-variance centered value with the
literal Cole–Hopf operator, including at mass zero. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
open ColeHopfFoundation.ProbabilityTheory

theorem scaledGaussianIncrementMean_apply (p : ColeHopfParameter) (x : ℝ) :
    scaledGaussianIncrementMean p x =
      (∫z,Real.exp (p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x)) *
          (terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x) ∂gaussianReal 0 1) /
      (∫z,Real.exp (p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x))
        ∂gaussianReal 0 1) := by
  rw [scaledGaussianIncrementMean,BoundedContinuousFunction.mul_apply,
    inverse_scaledGaussianNormalizer_apply,scaledGaussianNormalizer_apply]
  have he : scaledGaussianIncrementNumerator p x =
      ∫z,Real.exp (p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x)) *
        (terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x) ∂gaussianReal 0 1 := by
    change (BoundedContinuousFunction.evalCLM ℝ x)
      (∫z,scaledGaussianKernel p z * terminalIncrement (p.1.2*z) p.2
        ∂gaussianReal 0 1) = _
    rw [←ContinuousLinearMap.integral_comp_comm _ (integrable_scaledGaussianIncrement_integrand p)]
    simp only [BoundedContinuousFunction.evalCLM_apply,BoundedContinuousFunction.mul_apply,
      scaledGaussianKernel_apply,terminalIncrement_apply]
  rw [he,div_eq_mul_inv,mul_comm]

def varianceGaussianCenteredValue (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  scaledGaussianCenteredValue ((p.1.1,Real.sqrt p.1.2),p.2)

theorem continuous_varianceGaussianCenteredValue : Continuous varianceGaussianCenteredValue :=
  continuous_scaledGaussianCenteredValue.comp (by fun_prop)

@[simp] theorem varianceGaussianCenteredValue_zero (a : ℝ) (g : TerminalSpace) :
    varianceGaussianCenteredValue ((a,0),g) = 0 := by
  simp [varianceGaussianCenteredValue]

theorem varianceGaussianCenteredValue_apply (p : ColeHopfParameter) (hv : 0 ≤ p.1.2) (x : ℝ) :
    varianceGaussianCenteredValue p x =
      coleHopf p.1.1 p.1.2.toNNReal (terminalValue p.2) x-terminalValue p.2 x := by
  have hcont : Continuous (fun t : ℝ =>
      scaledGaussianIncrementMean ((t*p.1.1,Real.sqrt p.1.2),p.2)) :=
    continuous_scaledGaussianIncrementMean.comp (by fun_prop)
  change (BoundedContinuousFunction.evalCLM ℝ x)
    (∫t in (0:ℝ)..1,scaledGaussianIncrementMean ((t*p.1.1,Real.sqrt p.1.2),p.2)) = _
  rw [←ContinuousLinearMap.intervalIntegral_comp_comm _ (hcont.intervalIntegrable 0 1),
    coleHopf_centered_integral (terminalValue p.2) (hasLinearGrowth_terminalValue p.2)
      (contDiff_terminalValue p.2).continuous.measurable]
  apply intervalIntegral.integral_congr
  intro t ht
  change scaledGaussianIncrementMean ((t*p.1.1,Real.sqrt p.1.2),p.2) x = _
  rw [scaledGaussianIncrementMean_apply]
  dsimp only
  have hn : Continuous (fun d : ℝ =>
      (terminalValue p.2 (x+d)-terminalValue p.2 x) *
        Real.exp ((t*p.1.1)*(terminalValue p.2 (x+d)-terminalValue p.2 x))) := by
    have hg := (contDiff_terminalValue p.2).continuous
    fun_prop
  have hd : Continuous (fun d : ℝ =>
      Real.exp ((t*p.1.1)*(terminalValue p.2 (x+d)-terminalValue p.2 x))) := by
    have hg := (contDiff_terminalValue p.2).continuous
    fun_prop
  rw [integral_gaussianReal_eq_integral_sqrt_mul p.1.2.toNNReal hn.aestronglyMeasurable,
    integral_gaussianReal_eq_integral_sqrt_mul p.1.2.toNNReal hd.aestronglyMeasurable,
    Real.coe_toNNReal _ hv]
  congr 1
  apply integral_congr_ae
  exact .of_forall fun z => mul_comm _ _

end GeneralDepthPaper
