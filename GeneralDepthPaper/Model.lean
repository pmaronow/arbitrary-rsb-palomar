module

public import GeneralDepthPaper.CovarianceBridge
public import FourPapersCommon.MixedClockDynamics

@[expose] public section


/-! The manuscript's genuine finite mixed even-spin model, in the original
overlap coordinate. The Parisi pressure is a variational infimum; no physical
free-energy identification or optimizing property is folded into these data. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ContDiff
namespace GeneralDepthPaper
open FourPapersCommon

abbrev ParisiMeasure := Paper.ParisiMeasure
abbrev Overlap := Paper.Overlap
abbrev BrownianSample := Paper.BrownianSample

def potential (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (q x : ℝ) : ℝ :=
  mixedPotential Ξ.toEvenMixture μ (q,x)

def gradient (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (q x : ℝ) : ℝ :=
  mixedGradient Ξ.toEvenMixture μ (q,x)

def hessian (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (q x : ℝ) : ℝ :=
  mixedHessian Ξ.toEvenMixture μ (q,x)

def optimalState (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (sample : BrownianSample) (q : ℝ) : ℝ :=
  mixedState Ξ.toEvenMixture 0 μ sample q

def Gamma (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) : ℝ→ℝ :=
  mixedGamma Ξ.toEvenMixture 0 μ

def curvatureMoment (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) : ℝ→ℝ :=
  mixedCurvatureMoment2 Ξ.toEvenMixture 0 μ

def firstVariation (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) : ℝ→ℝ :=
  mixedFirstVariation Ξ.toEvenMixture 0 μ

def parisiFunctional (Ξ : AdmissibleCovariance) : ParisiMeasure→ℝ :=
  mixedFunctional Ξ.toEvenMixture 0

def parisiPressure (Ξ : AdmissibleCovariance) : ℝ :=
  mixedPressure Ξ.toEvenMixture 0

def IsParisiMinimizer (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) : Prop :=
  IsMixedMinimizer Ξ.toEvenMixture 0 μ

theorem parisiFunctional_eq (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    parisiFunctional Ξ μ = Real.log 2+potential Ξ μ 0 0-
      (1/2:ℝ)*∫q in (0:ℝ)..1,q*Ξ.second q*Paper.parisiCDF μ q := by
  simp only [parisiFunctional,mixedFunctional,potential,
    AdmissibleCovariance.toEvenMixture_second]

theorem firstVariation_eq (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (q : ℝ) :
    firstVariation Ξ μ q = (1/2:ℝ)*∫s in (0:ℝ)..q,Ξ.second s*(Gamma Ξ μ s-s) := by
  simp only [firstVariation,mixedFirstVariation,AdmissibleCovariance.toEvenMixture_second,Gamma]

theorem optimalState_integral_equation (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (sample : BrownianSample) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    optimalState Ξ μ sample q = mixedBeta Ξ.toEvenMixture*
      Paper.canonicalBrownian (Ξ.clock q).toNNReal sample+
      ∫s in 0..q,Ξ.second s*Paper.parisiCDF μ s*gradient Ξ μ s (optimalState Ξ μ sample s) := by
  simpa only [zero_add,AdmissibleCovariance.toEvenMixture_clock,
    AdmissibleCovariance.toEvenMixture_second,optimalState,gradient] using
    mixedState_integral_equation Ξ.toEvenMixture 0 μ sample hq

theorem hasDerivAt_Gamma (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Ioo (0:ℝ) 1) :
    HasDerivAt (Gamma Ξ μ) (Ξ.second q*curvatureMoment Ξ μ q) q := by
  simpa only [Gamma,curvatureMoment,AdmissibleCovariance.toEvenMixture_second] using
    hasDerivAt_mixedGamma Ξ.toEvenMixture 0 μ hq

theorem hasDerivWithinAt_Gamma (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (Gamma Ξ μ) (Ξ.second q*curvatureMoment Ξ μ q) (Icc (0:ℝ) 1) q := by
  simpa only [Gamma,curvatureMoment,AdmissibleCovariance.toEvenMixture_second] using
    hasDerivWithinAt_mixedGamma Ξ.toEvenMixture 0 μ hq

theorem contDiffOn_Gamma_one (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    ContDiffOn ℝ 1 (Gamma Ξ μ) (Icc (0:ℝ) 1) :=
  contDiffOn_mixedGamma_one Ξ.toEvenMixture 0 μ

theorem continuousOn_Gamma (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    ContinuousOn (Gamma Ξ μ) (Icc (0:ℝ) 1) :=
  continuousOn_mixedGamma Ξ.toEvenMixture 0 μ

@[simp] theorem Gamma_zero (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    Gamma Ξ μ 0=0 := mixedGamma_zero Ξ.toEvenMixture μ

theorem Gamma_nonneg (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (q : ℝ) :
    0 ≤ Gamma Ξ μ q := mixedGamma_nonneg Ξ.toEvenMixture 0 μ q

theorem Gamma_le_one (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (q : ℝ) :
    Gamma Ξ μ q ≤ 1 := mixedGamma_le_one Ξ.toEvenMixture 0 μ q

theorem curvatureMoment_nonneg (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (q : ℝ) :
    0 ≤ curvatureMoment Ξ μ q := mixedCurvatureMoment2_nonneg Ξ.toEvenMixture 0 μ q

theorem curvatureMoment_le_one (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (q : ℝ) :
    curvatureMoment Ξ μ q ≤ 1 := mixedCurvatureMoment2_le_one Ξ.toEvenMixture 0 μ q

theorem curvatureMoment_le_one_sub_Gamma (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1) : curvatureMoment Ξ μ q ≤ 1-Gamma Ξ μ q :=
  mixedCurvatureMoment2_le_one_sub_Gamma Ξ.toEvenMixture 0 μ hq

@[simp] theorem firstVariation_zero (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    firstVariation Ξ μ 0=0 := mixedFirstVariation_zero Ξ.toEvenMixture 0 μ

end GeneralDepthPaper
