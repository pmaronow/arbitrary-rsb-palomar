module

public import DepthPaper.RevisedEntropyCorollary
public import GeneralDepthPaper.RevisedCovarianceInverse

@[expose] public section

/-! The revised paper's entropy statements on its finite-support covariance
interface. All internal differentiability and Hessian requirements are
discharged; the final hypotheses are precisely the paper's finite atomic
nondegeneracy and subcriticality conditions. -/
noncomputable section
open MeasureTheory
namespace DepthPaper.RevisedCovariance
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

def entropyTemperaturePressure (Ξ : RevisedCovariance) (m : ℝ) : ℝ :=
  if hm:m=0 then Real.log 2 else parisiPressure (Ξ.temperatureScale m hm)

def diffusionEntropy (Ξ : RevisedCovariance) : ℝ :=
  entropyTemperaturePressure Ξ 1 - deriv (entropyTemperaturePressure Ξ) 1

theorem entropyTemperaturePressure_eq_scaledPressure (Ξ : RevisedCovariance) :
    entropyTemperaturePressure Ξ = scaledThermodynamicPressure Ξ.toEvenMixture := by
  funext m
  by_cases hm : m=0
  · simp only [entropyTemperaturePressure,scaledThermodynamicPressure,dite_eq_left hm]
  · rw [entropyTemperaturePressure,dite_eq_right hm,scaledPressure_eq_temperature_pressure Ξ hm]

theorem diffusionEntropy_eq_thermodynamicEntropy (Ξ : RevisedCovariance) :
    diffusionEntropy Ξ=thermodynamicEntropy Ξ.toEvenMixture := by
  rw [diffusionEntropy,entropyTemperaturePressure_eq_scaledPressure]
  rfl

/-- Exact Corollary 3.3, including its strict positivity conclusion. -/
theorem diffusion_entropy (Ξ : RevisedCovariance) (hsub : Ξ.IsSubcritical) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (hnd : Nondegenerate Ξ z hz) :
    diffusionEntropy Ξ =
      (∫sample,revisedSpinEntropy (optimalState Ξ (atomicMeasure z hz) sample 1)
        ∂Paper.canonicalBrownianMeasure) - firstVariation Ξ (atomicMeasure z hz) 1 ∧
      0 < diffusionEntropy Ξ := by
  have hzG : GeneralDepthPaper.IsAtomicPoint z := (GeneralDepthPaper.revised_isAtomicPoint z).mp hz
  have hsubG : Ξ.toGeneralCovariance.IsSubcritical := by
    rw [←GeneralDepthPaper.AdmissibleCovariance.toRevisedCovariance_isSubcritical_iff,
      toGeneralCovariance_toRevisedCovariance]
    exact hsub
  have hndG : Nondegenerate Ξ.toGeneralCovariance.toRevisedCovariance z
      ((GeneralDepthPaper.revised_isAtomicPoint z).mpr hzG) := by
    rw [toGeneralCovariance_toRevisedCovariance]
    exact hnd
  have H := GeneralDepthPaper.revised_diffusion_entropy Ξ.toGeneralCovariance hsubG z hzG hndG
  simp_rw [←GeneralDepthPaper.revised_optimalState,←GeneralDepthPaper.revised_firstVariation,
    toGeneralCovariance_toRevisedCovariance,toGeneralCovariance_toEvenMixture] at H
  rw [diffusionEntropy_eq_thermodynamicEntropy]
  convert! H using 1

end DepthPaper.RevisedCovariance
