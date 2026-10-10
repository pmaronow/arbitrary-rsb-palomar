module

public import GeneralDepthPaper.RevisedSectionTwoPhysicalBrownianGluing
public import GeneralDepthPaper.RevisedSectionTwoPhysicalState
public import GeneralDepthPaper.RevisedSectionTwoPhysicalHessianAdapted

@[expose] public section

/-! The full finite-support target of revised Lemma 2.2. Its stochastic
clause uses a genuine physical-time standard Brownian motion on the original
canonical sample space. Both the state noise and the actual Hessian integral
use that same driver. The physical Hessian integral is constructed from its
predictable left sums, rather than defined as the gradient process.

The covariance is any finite positive even polynomial of degree at least
two. The proof needs no subcriticality, positive volatility at zero, or
restriction on atoms at either endpoint. The printed finite-support
hypothesis is retained for the Hessian stochastic-integral construction. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal

namespace Verification.PhysicalStochasticTargets
open GeneralDepthPaper

/-- Literal analytic, martingale, endpoint and physical stochastic clauses
of revised Lemma 2.2. The final convergence statements identify the concrete
physical Brownian sums with the actual continuous gradient modification.
Brownian adaptation modulo null sets and future-increment independence are
stated in the same original clock past as the actual selected diffusion. -/
theorem lemma2_2_finite_atomic_physical_exact (Ξ : AdmissibleCovariance)
    (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite) :
    (∀ q ∈ Icc (0 : ℝ) 1, ∀ x, |gradient Ξ μ q x| ≤ 1 ∧
      0 < hessian Ξ μ q x ∧ hessian Ξ μ q x ≤ 1 - gradient Ξ μ q x ^ 2) ∧
    Martingale (sectionTwoGradientProcess Ξ μ) (sectionTwoGradientFiltration Ξ)
      Paper.canonicalBrownianMeasure ∧
    (∀ sample, sectionTwoGradientProcess Ξ μ ⟨0, by norm_num⟩ sample = 0 ∧
      sectionTwoGradientProcess Ξ μ ⟨1, by norm_num⟩ sample =
        Real.tanh (optimalState Ξ μ sample 1)) ∧
    ContDiffOn ℝ 1 (Gamma Ξ μ) (Icc (0 : ℝ) 1) ∧ Gamma Ξ μ 0 = 0 ∧
    (∀ q ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (Gamma Ξ μ)
        (Ξ.second q * (∫ sample,
          hessian Ξ μ q (optimalState Ξ μ sample q) ^ 2
            ∂Paper.canonicalBrownianMeasure)) (Icc (0 : ℝ) 1) q ∧
      0 ≤ derivWithin (Gamma Ξ μ) (Icc (0 : ℝ) 1) q ∧
      derivWithin (Gamma Ξ μ) (Icc (0 : ℝ) 1) q ≤
        Ξ.second q * (1 - Gamma Ξ μ q) ∧ Gamma Ξ μ q ≤ Ξ.first q) ∧
    IsBrownianReal (sectionTwoPhysicalBrownian Ξ) Paper.canonicalBrownianMeasure ∧
    (∀ sample, sectionTwoPhysicalBrownian Ξ 0 sample = 0) ∧
    (∀ sample, Continuous (fun t => sectionTwoPhysicalBrownian Ξ t sample)) ∧
    IsStronglyProgressive (sectionTwoGradientFiltration Ξ)
      (fun q sample => Real.sqrt (Ξ.second q) *
        hessian Ξ μ q (optimalState Ξ μ sample q)) ∧
    (∀ q, AEStronglyMeasurable[sectionTwoPhysicalBrownianPast Ξ q]
      (sectionTwoPhysicalBrownian Ξ q.val.toNNReal) Paper.canonicalBrownianMeasure) ∧
    (∀ s t : Overlap, s ≤ t → Indep
      (MeasurableSpace.comap
        (sectionTwoPhysicalBrownian Ξ t.val.toNNReal -
          sectionTwoPhysicalBrownian Ξ s.val.toNNReal) inferInstance)
      (sectionTwoPhysicalBrownianPast Ξ s) Paper.canonicalBrownianMeasure) ∧
    (∀ q : Overlap, (fun sample => optimalState Ξ μ sample q)
      =ᵐ[Paper.canonicalBrownianMeasure]
        (fun sample => sectionTwoPhysicalNoiseWienerIntegral Ξ q sample +
          ∫ s in (0 : ℝ)..(q : ℝ), Ξ.second s * Paper.parisiCDF μ s *
            gradient Ξ μ s (optimalState Ξ μ sample s))) ∧
    (∀ q n, TendstoInMeasure Paper.canonicalBrownianMeasure
      (fun j => sectionTwoHessianPhysicalBrownianLeftSums Ξ μ hμ
        (sectionTwoPhysicalBrownian Ξ) q n j) atTop
      (sectionTwoHessianPhysicalBrownianInnerLimit Ξ μ hμ
        (sectionTwoPhysicalBrownian Ξ) q n)) ∧
    (∀ q, TendstoInMeasure Paper.canonicalBrownianMeasure
      (fun n => sectionTwoHessianPhysicalBrownianInnerLimit Ξ μ hμ
        (sectionTwoPhysicalBrownian Ξ) q n) atTop
      (sectionTwoGradientProcess Ξ μ q)) ∧
    (∀ q, sectionTwoHessianPhysicalBrownianIntegral Ξ μ hμ
      (sectionTwoPhysicalBrownian Ξ) q =ᵐ[Paper.canonicalBrownianMeasure]
        sectionTwoGradientProcess Ξ μ q) ∧
    (∀ sample, Continuous (fun q => sectionTwoGradientProcess Ξ μ q sample)) := by
  obtain ⟨ha, hm, he, hc, h0, hΓ⟩ := revised_lemma_2_2_analytic_martingale Ξ μ
  exact ⟨ha, hm, he, hc, h0, hΓ,
    isBrownianReal_sectionTwoPhysicalBrownian Ξ,
    sectionTwoPhysicalBrownian_zero Ξ,
    continuous_sectionTwoPhysicalBrownian Ξ,
    isStronglyProgressive_sectionTwoPhysicalHessianCoefficient Ξ μ,
    aestronglyMeasurable_sectionTwoPhysicalBrownian_past Ξ,
    indep_sectionTwoPhysicalBrownian_increment_past Ξ,
    optimalState_physicalBrownian_integral_equation Ξ μ,
    sectionTwoHessianPhysicalBrownianLeftSums_tendsto Ξ μ hμ,
    sectionTwoHessianPhysicalBrownianInnerLimit_tendsto Ξ μ hμ,
    sectionTwoHessianPhysicalBrownianIntegral_eq Ξ μ hμ,
    continuous_sectionTwoGradientProcess_path Ξ μ⟩

end Verification.PhysicalStochasticTargets
