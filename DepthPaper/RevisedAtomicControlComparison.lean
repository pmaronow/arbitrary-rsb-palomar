module

public import DepthPaper.RevisedModel
public import DepthPaper.RevisedControlSecondDerivative
public import DepthPaper.RevisedSecondDerivativeComparison
public import DepthPaper.RevisedControlInjectivity
public import Paper.ParisiHJBFeedback
public import DepthPaper.RevisedControlAffinity

@[expose] public section

/-! Quantitative curvature of the genuine normalized-clock optimal control
along a two-sided affine line of CDFs. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace DepthPaper.RevisedCovariance
open FourPapersCommon Paper
set_option maxHeartbeats 1200000

def fixedControlCorrection (Ξ : RevisedCovariance) (μ : ParisiMeasure) : ℝ :=
  ∫q in (0 : ℝ)..1,q*Ξ.second q*parisiCDF μ q

def fixedControlExpectation (Ξ : RevisedCovariance) (μ ν : ParisiMeasure) (t : ℝ) : ℝ :=
  ∫ sample,parisiAffineControlPayoff (mixedBeta Ξ.toEvenMixture) 0 (canonicalBrownian 1)
    (selectedParisiFeedbackControl (mixedBeta Ξ.toEvenMixture) 0
      (mixedMeasure Ξ.toEvenMixture μ))
    (mixedMeasure Ξ.toEvenMixture μ) (mixedMeasure Ξ.toEvenMixture ν) t sample
    ∂canonicalBrownianMeasure

def fixedControlCurvature (Ξ : RevisedCovariance) (μ ν : ParisiMeasure) : ℝ :=
  ∫ sample,parisiAffineControlSecondDerivative (mixedBeta Ξ.toEvenMixture) 0 (canonicalBrownian 1)
    (selectedParisiFeedbackControl (mixedBeta Ξ.toEvenMixture) 0
      (mixedMeasure Ξ.toEvenMixture μ))
    (mixedMeasure Ξ.toEvenMixture μ) (mixedMeasure Ξ.toEvenMixture ν) 0 sample
    ∂canonicalBrownianMeasure

def fixedControlComparison (Ξ : RevisedCovariance) (μ ν : ParisiMeasure)
    (ε t : ℝ) : ℝ :=
  Real.log 2+fixedControlExpectation Ξ μ ν (t/ε)-
    (fixedControlCorrection Ξ μ+(t/ε)*(fixedControlCorrection Ξ ν-fixedControlCorrection Ξ μ))/2

theorem differentiableAt_fixedControlExpectation (Ξ : RevisedCovariance)
    (μ ν : ParisiMeasure) (t : ℝ) :
    DifferentiableAt ℝ (fixedControlExpectation Ξ μ ν) t := by
  have hA := isParisiAdmissibleControl_selectedParisiFeedbackControl
    (mixedBeta Ξ.toEvenMixture) 0 (mixedMeasure Ξ.toEvenMixture μ)
  exact (hasDerivAt_integral_parisiAffineControlPayoff canonicalBrownianMeasure
    (mixedBeta Ξ.toEvenMixture) 0 (canonicalBrownian 1) (measurable_canonicalBrownian 1)
    integrable_hjb_canonicalBrownian_one _ hA.measurable hA.bounded
    (mixedMeasure Ξ.toEvenMixture μ) (mixedMeasure Ξ.toEvenMixture ν) t).differentiableAt

theorem hasDerivAt_deriv_fixedControlExpectation (Ξ : RevisedCovariance)
    (μ ν : ParisiMeasure) :
    HasDerivAt (deriv (fixedControlExpectation Ξ μ ν)) (fixedControlCurvature Ξ μ ν) 0 := by
  have hA := isParisiAdmissibleControl_selectedParisiFeedbackControl
    (mixedBeta Ξ.toEvenMixture) 0 (mixedMeasure Ξ.toEvenMixture μ)
  exact hasDerivAt_deriv_integral_parisiAffineControlPayoff canonicalBrownianMeasure
    (mixedBeta Ξ.toEvenMixture) 0 (canonicalBrownian 1) (measurable_canonicalBrownian 1)
    integrable_hjb_canonicalBrownian_one _ hA.measurable hA.bounded
    (mixedMeasure Ξ.toEvenMixture μ) (mixedMeasure Ξ.toEvenMixture ν) 0

theorem fixedControlCurvature_pos (Ξ : RevisedCovariance)
    (μ ν : ParisiMeasure) (hne : ν≠μ) : 0<fixedControlCurvature Ξ μ ν := by
  have hA := isParisiAdmissibleControl_selectedParisiFeedbackControl
    (mixedBeta Ξ.toEvenMixture) 0 (mixedMeasure Ξ.toEvenMixture μ)
  apply integral_parisiAffineControlSecondDerivative_pos canonicalBrownianMeasure
    (mixedBeta Ξ.toEvenMixture) 0 (canonicalBrownian 1) (measurable_canonicalBrownian 1)
    _ hA.measurable hA.bounded (mixedMeasure Ξ.toEvenMixture μ)
    (mixedMeasure Ξ.toEvenMixture ν) 0
  intro hd
  exact hne (mixed_fixed_feedback_drift_injective Ξ.toEvenMixture 0 μ ν μ hd)

theorem differentiableAt_fixedControlComparison (Ξ : RevisedCovariance)
    (μ ν : ParisiMeasure) (ε t : ℝ) :
    DifferentiableAt ℝ (fixedControlComparison Ξ μ ν ε) t := by
  exact ((differentiableAt_const _).add
    ((differentiableAt_fixedControlExpectation Ξ μ ν (t/ε)).comp t
      (differentiableAt_id.div_const ε))).sub
    (((differentiableAt_const _).add
      ((differentiableAt_id.div_const ε).mul (differentiableAt_const _))).div_const 2)

theorem hasDerivAt_deriv_fixedControlComparison (Ξ : RevisedCovariance)
    (μ ν : ParisiMeasure) (ε : ℝ) :
    HasDerivAt (deriv (fixedControlComparison Ξ μ ν ε))
      (fixedControlCurvature Ξ μ ν/ε^2) 0 :=
  hasDerivAt_deriv_rescaled_affine_correction
    (differentiableAt_fixedControlExpectation Ξ μ ν)
    (hasDerivAt_deriv_fixedControlExpectation Ξ μ ν)

theorem fixedControlComparison_zero (Ξ : RevisedCovariance)
    (μ ν : ParisiMeasure) (ε : ℝ) :
    fixedControlComparison Ξ μ ν ε 0=parisiFunctional Ξ μ := by
  have he := parisiControlObjective_feedback_eq_potential (mixedBeta Ξ.toEvenMixture) 0
    (mixedMeasure Ξ.toEvenMixture μ)
  have hexp : fixedControlExpectation Ξ μ ν 0=
      parisiControlObjective canonicalBrownianMeasure (mixedBeta Ξ.toEvenMixture) 0
        (canonicalBrownian 1) (selectedParisiFeedbackControl (mixedBeta Ξ.toEvenMixture) 0
          (mixedMeasure Ξ.toEvenMixture μ)) (mixedMeasure Ξ.toEvenMixture μ) := by
    unfold fixedControlExpectation parisiControlObjective
    apply integral_congr_ae
    exact .of_forall fun sample=>by simp [parisiAffineControlPayoff,parisiControlPayoff]
  rw [parisiFunctional_eq]
  simp only [fixedControlComparison,zero_div,zero_mul,add_zero,hexp,he]
  simp only [potential,mixedPotential,Ξ.toEvenMixture.clock_zero,fixedControlCorrection]
  ring

theorem fixedControlComparison_le (Ξ : RevisedCovariance)
    (μ ν ρ : ParisiMeasure) (ε t : ℝ)
    (hphysical : ∀q∈Icc (0 : ℝ) 1,parisiCDF ρ q=
      parisiCDF μ q+(t/ε)*(parisiCDF ν q-parisiCDF μ q))
    (hclock : ∀q∈Icc (0 : ℝ) 1,
      parisiCDF (mixedMeasure Ξ.toEvenMixture ρ) q=
        parisiCDF (mixedMeasure Ξ.toEvenMixture μ) q+
          (t/ε)*(parisiCDF (mixedMeasure Ξ.toEvenMixture ν) q-
            parisiCDF (mixedMeasure Ξ.toEvenMixture μ) q)) :
    fixedControlComparison Ξ μ ν ε t≤parisiFunctional Ξ ρ := by
  let A := selectedParisiFeedbackControl (mixedBeta Ξ.toEvenMixture) 0
    (mixedMeasure Ξ.toEvenMixture μ)
  have hA : IsParisiAdmissibleControl A :=
    isParisiAdmissibleControl_selectedParisiFeedbackControl _ _ _
  have hpay : fixedControlExpectation Ξ μ ν (t/ε)=
      parisiControlObjective canonicalBrownianMeasure (mixedBeta Ξ.toEvenMixture) 0
        (canonicalBrownian 1) A (mixedMeasure Ξ.toEvenMixture ρ) := by
    unfold fixedControlExpectation parisiControlObjective
    apply integral_congr_ae
    exact .of_forall fun sample=>
      (parisiControlPayoff_affine_of_cdf _ _ (canonicalBrownian 1) _ _ _ _ hclock A
        (fun sample=> (hA.continuous_paths sample).measurable) hA.bounded sample).symm
  have hcorr : fixedControlCorrection Ξ ρ=fixedControlCorrection Ξ μ+
      (t/ε)*(fixedControlCorrection Ξ ν-fixedControlCorrection Ξ μ) :=
    weightedCDFIntegral_affine_of_cdf (fun q=>q*Ξ.second q)
      (continuous_id.mul Ξ.continuous_second).continuousOn μ ν ρ (t/ε) hphysical
  have hup := parisiControlObjective_le_potential (mixedBeta Ξ.toEvenMixture) 0
    (mixedBeta_ne_zero Ξ.toEvenMixture) (mixedMeasure Ξ.toEvenMixture ρ) A hA
  rw [parisiFunctional_eq]
  change fixedControlComparison Ξ μ ν ε t≤Real.log 2+potential Ξ ρ 0 0-
    (1/2:ℝ)*fixedControlCorrection Ξ ρ
  unfold fixedControlComparison
  rw [hpay,←hcorr]
  have hpot : potential Ξ ρ 0 0=parisiPotential (mixedBeta Ξ.toEvenMixture)
      (mixedMeasure Ξ.toEvenMixture ρ) (0,0) := by
    simp only [potential,mixedPotential,Ξ.toEvenMixture.clock_zero]
  rw [hpot]
  linarith

end DepthPaper.RevisedCovariance
