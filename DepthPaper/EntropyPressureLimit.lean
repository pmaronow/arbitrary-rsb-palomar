module

public import DepthPaper.PressureTemperatureLaw
public import FourPapersCommon.ConvexDerivativeConvergence

@[expose] public section


/-! The actual expected entropy has a strictly positive thermodynamic limit
at every differentiability point of the scaled pressure at temperature one.
The nondegenerate-chart differentiability hypothesis is discharged separately;
this file does not claim the complete numbered proposition by itself. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace DepthPaper
open FourPapersCommon OverlapPaper

theorem convexOn_scaledThermodynamicPressure (ξ : AdmissibleEvenMixture) :
    ConvexOn ℝ univ (scaledThermodynamicPressure ξ) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy a b ha hb hab
  change scaledThermodynamicPressure ξ (a*x+b*y) ≤
    a*scaledThermodynamicPressure ξ x+b*scaledThermodynamicPressure ξ y
  apply le_of_tendsto_of_tendsto (tendsto_expectedScaledPressure ξ (a*x+b*y))
    (((tendsto_expectedScaledPressure ξ x).const_mul a).add
      ((tendsto_expectedScaledPressure ξ y).const_mul b))
  exact .of_forall fun n=>(convexOn_expectedScaledPressure ξ n).2 hx hy ha hb hab

def thermodynamicEntropy (ξ : AdmissibleEvenMixture) : ℝ :=
  scaledThermodynamicPressure ξ 1-deriv (scaledThermodynamicPressure ξ) 1

theorem tendsto_expectedEntropyDensity_of_differentiable (ξ : AdmissibleEvenMixture)
    (hd : DifferentiableAt ℝ (scaledThermodynamicPressure ξ) 1) :
    Tendsto (expectedEntropyDensity ξ) atTop (𝓝 (thermodynamicEntropy ξ)) := by
  have H := tendsto_deriv_of_convex_pointwise
    (fun n=>convexOn_expectedScaledPressure ξ n)
    (fun n=>(hasDerivAt_expectedScaledPressure ξ n 1).differentiableAt)
    (tendsto_expectedScaledPressure ξ) hd.hasDerivAt
  exact ((tendsto_expectedScaledPressure ξ 1).sub H).congr
    (fun n=>(expectedEntropyDensity_eq_pressure_sub_deriv ξ n).symm)

theorem thermodynamicEntropy_ge_penalty_of_differentiable (ξ : AdmissibleEvenMixture)
    (hd : DifferentiableAt ℝ (scaledThermodynamicPressure ξ) 1) :
    entropyPenalty (4*ξ.variance) ≤ thermodynamicEntropy ξ := by
  apply ge_of_tendsto (tendsto_expectedEntropyDensity_of_differentiable ξ hd)
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact expectedEntropyDensity_ge_penalty ξ hn

theorem thermodynamicEntropy_pos_of_differentiable (ξ : AdmissibleEvenMixture)
    (hd : DifferentiableAt ℝ (scaledThermodynamicPressure ξ) 1) :
    0 < thermodynamicEntropy ξ :=
  (entropyPenalty_pos _).trans_le (thermodynamicEntropy_ge_penalty_of_differentiable ξ hd)

end DepthPaper
