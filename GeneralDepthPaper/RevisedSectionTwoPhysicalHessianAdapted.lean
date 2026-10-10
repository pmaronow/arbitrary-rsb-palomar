module

public import GeneralDepthPaper.RevisedSectionTwoPhysicalClockInverse
public import FRSB.ConstantMassLaw

@[expose] public section

/-! The actual Hessian along the actual diffusion is measurable in the
original Brownian past at its covariance-clock time. Thus each physical
left-step coefficient is a past-measurable random variable, rather than
an arbitrary multiplier of a Brownian increment. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Paper
open scoped NNReal Topology

namespace GeneralDepthPaper
open FourPapersCommon

theorem stronglyAdapted_sectionTwoVarianceHessian (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) :
    StronglyAdapted canonicalBrownianFiltration (sectionTwoVarianceHessian Ξ μ) := by
  intro v
  exact (continuous_parisiHessian_all _ _).comp_stronglyMeasurable
    (stronglyMeasurable_const.prodMk
      (FRSB.stronglyAdapted_selectedParisiState _ _ _ _ v))

theorem stronglyMeasurable_sectionTwoActualHessian (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (q : Overlap) :
    StronglyMeasurable[canonicalBrownianFiltration (sectionTwoBrownianTime Ξ q)]
      (fun sample => hessian Ξ μ q (optimalState Ξ μ sample q)) := by
  have he : (fun sample => hessian Ξ μ q (optimalState Ξ μ sample q)) =
      sectionTwoVarianceHessian Ξ μ (sectionTwoBrownianTime Ξ q) := by
    funext sample
    exact (sectionTwoVarianceHessian_eq_actual Ξ μ q sample).symm
  rw [he]
  exact stronglyAdapted_sectionTwoVarianceHessian Ξ μ _

theorem sectionTwoPhysicalOverlapAtTime_brownianTime (Ξ : AdmissibleCovariance)
    (v : ℝ≥0) (hv : (v : ℝ) ≤ 1) :
    sectionTwoBrownianTime Ξ (sectionTwoPhysicalOverlapAtTime Ξ v) = v := by
  unfold sectionTwoBrownianTime
  rw [← sectionTwoPhysicalTimeAtVarianceTime_coe,
    sectionTwoPhysicalTimeAtVarianceTime_clock Ξ v hv, Real.toNNReal_coe]

theorem stronglyMeasurable_sectionTwoActualHessianAtVarianceTime
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (v : ℝ≥0)
    (hv : (v : ℝ) ≤ 1) :
    StronglyMeasurable[canonicalBrownianFiltration v]
      (fun sample => hessian Ξ μ (sectionTwoPhysicalOverlapAtTime Ξ v)
        (optimalState Ξ μ sample (sectionTwoPhysicalOverlapAtTime Ξ v))) := by
  have h := stronglyMeasurable_sectionTwoActualHessian Ξ μ
    (sectionTwoPhysicalOverlapAtTime Ξ v)
  rwa [sectionTwoPhysicalOverlapAtTime_brownianTime Ξ v hv] at h

theorem stronglyMeasurable_sectionTwoPhysicalHessianCoefficient
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) (q : Overlap) :
    StronglyMeasurable[canonicalBrownianFiltration (sectionTwoBrownianTime Ξ q)]
      (fun sample => Real.sqrt (Ξ.second q) *
        hessian Ξ μ q (optimalState Ξ μ sample q)) :=
  (stronglyMeasurable_sectionTwoActualHessian Ξ μ q).const_mul _

theorem continuous_sectionTwoVarianceHessian_path (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (sample : BrownianSample) :
    Continuous (fun v : ℝ≥0 => sectionTwoVarianceHessian Ξ μ v sample) := by
  exact (continuous_parisiHessian_all _ _).comp
    (NNReal.continuous_coe.prodMk
      (continuous_canonicalParisiItoState (mixedBeta Ξ.toEvenMixture) 0
        (mixedMeasure Ξ.toEvenMixture μ)
        (fun t x => parisiGradient (mixedBeta Ξ.toEvenMixture)
          (mixedMeasure Ξ.toEvenMixture μ) (t,x))
        (continuous_parisiGradient _ _)
        (fun t x => norm_parisiGradient_le_one _ _ (t,x))
        (lipschitzWith_parisiGradient _ (mixedBeta_ne_zero _) _) sample))

theorem isStronglyProgressive_sectionTwoVarianceHessian
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    IsStronglyProgressive canonicalBrownianFiltration (sectionTwoVarianceHessian Ξ μ) :=
  (stronglyAdapted_sectionTwoVarianceHessian Ξ μ).isStronglyProgressive_of_continuous
    (continuous_sectionTwoVarianceHessian_path Ξ μ)

theorem continuous_sectionTwoActualHessian_path (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (sample : BrownianSample) :
    Continuous (fun q : Overlap => hessian Ξ μ q (optimalState Ξ μ sample q)) := by
  have he : (fun q : Overlap => hessian Ξ μ q (optimalState Ξ μ sample q)) =
      fun q => sectionTwoVarianceHessian Ξ μ (sectionTwoBrownianTime Ξ q) sample := by
    funext q
    exact (sectionTwoVarianceHessian_eq_actual Ξ μ q sample).symm
  rw [he]
  exact (continuous_sectionTwoVarianceHessian_path Ξ μ sample).comp
    (continuous_real_toNNReal.comp (Ξ.continuous_clock.comp continuous_subtype_val))

/-- The literal physical coefficient is progressively measurable in the
same covariance-clock-reindexed original filtration as the actual diffusion.
Continuous Brownian modifications are adapted to this past modulo null sets. -/
theorem isStronglyProgressive_sectionTwoPhysicalHessianCoefficient
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) :
    IsStronglyProgressive (sectionTwoGradientFiltration Ξ)
      (fun q sample => Real.sqrt (Ξ.second q) *
        hessian Ξ μ q (optimalState Ξ μ sample q)) := by
  have ha : StronglyAdapted (sectionTwoGradientFiltration Ξ)
      (fun q sample => Real.sqrt (Ξ.second q) *
        hessian Ξ μ q (optimalState Ξ μ sample q)) :=
    fun q => stronglyMeasurable_sectionTwoPhysicalHessianCoefficient Ξ μ q
  apply ha.isStronglyProgressive_of_continuous
  intro sample
  exact (Ξ.continuous_second.sqrt.comp continuous_subtype_val).mul
    (continuous_sectionTwoActualHessian_path Ξ μ sample)

end GeneralDepthPaper
