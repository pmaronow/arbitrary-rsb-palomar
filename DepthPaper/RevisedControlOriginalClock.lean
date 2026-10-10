module

public import DepthPaper.RevisedModel
public import FourPapersCommon.MixedClockDynamics
public import Paper.ParisiControlFirstVariation

@[expose] public section

/-! Exact original-overlap coordinate representations of the fixed optimal
control drift and its terminal state. The variance-clock substitution holds
for arbitrary order parameters, including their CDF jumps. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace DepthPaper
open FourPapersCommon Paper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 64

theorem mixed_integral_cdf_difference_gradient_eq_controlDrift
    (ξ : AdmissibleEvenMixture) (h : ℝ) (μ ν : Paper.ParisiMeasure)
    (sample : Paper.BrownianSample) :
    (∫q in (0:ℝ)..1,ξ.second q*(parisiCDF ν q-parisiCDF μ q)*
      mixedGradient ξ μ (q,mixedState ξ h μ sample q)) =
      parisiControlDrift (mixedBeta ξ) (mixedMeasure ξ ν)
        (selectedParisiFeedbackControl (mixedBeta ξ) h (mixedMeasure ξ μ)) sample -
      parisiControlDrift (mixedBeta ξ) (mixedMeasure ξ μ)
        (selectedParisiFeedbackControl (mixedBeta ξ) h (mixedMeasure ξ μ)) sample := by
  let A := selectedParisiFeedbackControl (mixedBeta ξ) h (mixedMeasure ξ μ)
  let g : ℝ → ℝ := fun t => mixedBeta ξ^2*
    (parisiCDF (mixedMeasure ξ ν) t-parisiCDF (mixedMeasure ξ μ) t)*A t sample
  have hA := isParisiAdmissibleControl_selectedParisiFeedbackControl
    (mixedBeta ξ) h (mixedMeasure ξ μ)
  have hmeas : ∀ sample,Measurable (fun s => A s sample) :=
    fun sample => (hA.continuous_paths sample).measurable
  have hnν := (parisiControl_intervalIntegrable (mixedMeasure ξ ν) A hmeas hA.bounded sample).1
  have hnμ := (parisiControl_intervalIntegrable (mixedMeasure ξ μ) A hmeas hA.bounded sample).1
  have hnormalized :
      parisiControlDrift (mixedBeta ξ) (mixedMeasure ξ ν) A sample -
        parisiControlDrift (mixedBeta ξ) (mixedMeasure ξ μ) A sample = ∫t in (0:ℝ)..1,g t := by
    unfold parisiControlDrift
    rw [←mul_sub,←intervalIntegral.integral_sub hnν hnμ,
      ←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [g]
    ring
  have hsub := integral_mixedClock_substitution ξ g (q:=1) (by norm_num)
  rw [ξ.clock_one] at hsub
  have hactual : (∫q in (0:ℝ)..1,g (ξ.clock q)*(ξ.second q/ξ.variance)) =
      ∫q in (0:ℝ)..1,ξ.second q*(parisiCDF ν q-parisiCDF μ q)*
        mixedGradient ξ μ (q,mixedState ξ h μ sample q) := by
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le zero_le_one]
    intro q hq
    have hqU : q∈Icc (0:ℝ) 1 := ⟨hq.1.le,hq.2.le⟩
    dsimp only [g,A]
    rw [mixedBeta_sq,parisiCDF_mixedMeasure ξ ν q hqU,
      parisiCDF_mixedMeasure ξ μ q hqU,
      selectedParisiFeedbackControl_apply (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
        (mixedMeasure ξ μ) (ξ.clock q) (ξ.clock_mem_unitInterval hqU) sample]
    unfold mixedGradient mixedState
    field_simp [ξ.variance_pos.ne']
  exact (hactual.symm.trans hsub).trans hnormalized.symm

namespace RevisedCovariance

/-- The exact original-clock random variable `I` in revised Appendix A.6. -/
theorem integral_cdf_difference_gradient_eq_controlDrift (Ξ : RevisedCovariance)
    (μ ν : ParisiMeasure) (sample : BrownianSample) :
    (∫q in (0:ℝ)..1,Ξ.second q*(parisiCDF ν q-parisiCDF μ q)*
      gradient Ξ μ q (optimalState Ξ μ sample q)) =
      parisiControlDrift (mixedBeta Ξ.toEvenMixture) (mixedMeasure Ξ.toEvenMixture ν)
        (selectedParisiFeedbackControl (mixedBeta Ξ.toEvenMixture) 0
          (mixedMeasure Ξ.toEvenMixture μ)) sample -
      parisiControlDrift (mixedBeta Ξ.toEvenMixture) (mixedMeasure Ξ.toEvenMixture μ)
        (selectedParisiFeedbackControl (mixedBeta Ξ.toEvenMixture) 0
          (mixedMeasure Ξ.toEvenMixture μ)) sample := by
  have H := mixed_integral_cdf_difference_gradient_eq_controlDrift Ξ.toEvenMixture 0 μ ν sample
  simpa only [toEvenMixture_second,gradient,optimalState] using H

theorem optimalState_terminal_eq_controlDrift (Ξ : RevisedCovariance)
    (μ : ParisiMeasure) (sample : BrownianSample) :
    optimalState Ξ μ sample 1 = mixedBeta Ξ.toEvenMixture*canonicalBrownian 1 sample +
      parisiControlDrift (mixedBeta Ξ.toEvenMixture) (mixedMeasure Ξ.toEvenMixture μ)
        (selectedParisiFeedbackControl (mixedBeta Ξ.toEvenMixture) 0
          (mixedMeasure Ξ.toEvenMixture μ)) sample := by
  have H := selectedParisiFeedbackControl_terminal_state_eq
    (mixedBeta Ξ.toEvenMixture) 0 (mixedBeta_ne_zero Ξ.toEvenMixture)
    (mixedMeasure Ξ.toEvenMixture μ) sample
  simp only [zero_add] at H
  simpa only [optimalState,mixedState,Ξ.toEvenMixture.clock_one] using H.symm

end RevisedCovariance
end DepthPaper
