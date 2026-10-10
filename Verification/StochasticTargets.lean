module

public import GeneralDepthPaper.RevisedSectionTwoStochasticClock

@[expose] public section

/-! The proved finite-support variance-clock stochastic clause of revised
Lemma 2.2. The target states concrete Hessian left-sum convergence and its
actual-gradient identity. The physical-time standard Brownian representation
is proved in `Verification.PhysicalStochasticTargets`. This older target
retains its variance-clock statement and finite-support scope. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal
namespace Verification.StochasticTargets
open GeneralDepthPaper

/-- Exact proved scope: any finite-support overlap probability law,
including endpoint atoms, for every finite positive even covariance.
No subcriticality, stationary-contact, or stochastic representation
hypothesis is needed. -/
theorem lemma2_2_finite_atomic_clock_stochastic (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (hμ : (μ:Measure Overlap).support.Finite) :
    HasQuadraticVariationBeforeStopProcessInProbability (sectionTwoExtendedClockDriver Ξ)
      (fun t _ => Ξ.first t) Paper.canonicalBrownianMeasure ∧
    (∀ q n, TendstoInMeasure Paper.canonicalBrownianMeasure
      (fun j => sectionTwoHessianClockLeftSums Ξ μ hμ q n j) atTop
      (sectionTwoHessianClockInnerLimit Ξ μ hμ q n)) ∧
    (∀ q, TendstoInMeasure Paper.canonicalBrownianMeasure
      (fun n => sectionTwoHessianClockInnerLimit Ξ μ hμ q n) atTop
      (sectionTwoGradientProcess Ξ μ q)) ∧
    (∀ q, sectionTwoHessianClockIntegral Ξ μ hμ q =ᵐ[Paper.canonicalBrownianMeasure]
      sectionTwoGradientProcess Ξ μ q) ∧
    (∀ sample, Continuous (fun q => sectionTwoGradientProcess Ξ μ q sample)) ∧
    (∀ q, AEStronglyMeasurable (sectionTwoHessianClockIntegral Ξ μ hμ q)
      Paper.canonicalBrownianMeasure) :=
  ⟨sectionTwoExtendedClockDriver_quadraticVariation Ξ,
    sectionTwoHessianClockLeftSums_tendsto Ξ μ hμ,
    sectionTwoHessianClockInnerLimit_tendsto Ξ μ hμ,
    sectionTwoHessianClockIntegral_eq Ξ μ hμ,
    continuous_sectionTwoGradientProcess_path Ξ μ,
    sectionTwoHessianClockIntegral_aestronglyMeasurable Ξ μ hμ⟩

/-- The normalization of every concrete summand is checked directly:
the integrand is the actual spatial Hessian along the actual state, and
the increment is the actual clock-driver increment on that same path. -/
theorem lemma2_2_clock_summands (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (u v : Overlap) (sample : Paper.BrownianSample) :
    sectionTwoVarianceHessian Ξ μ (u:ℝ).toNNReal sample*
      (FourPapersCommon.mixedBeta Ξ.toEvenMixture*
        (Paper.canonicalBrownian (v:ℝ).toNNReal sample-
          Paper.canonicalBrownian (u:ℝ).toNNReal sample))=
    hessian Ξ μ (sectionTwoOverlapAtVarianceTime Ξ u)
      (optimalState Ξ μ sample (sectionTwoOverlapAtVarianceTime Ξ u))*
      (sectionTwoClockDriver Ξ (sectionTwoOverlapAtVarianceTime Ξ v) sample-
        sectionTwoClockDriver Ξ (sectionTwoOverlapAtVarianceTime Ξ u) sample) :=
  sectionTwoVarianceHessian_summand_eq_physical Ξ μ u v sample

end Verification.StochasticTargets
