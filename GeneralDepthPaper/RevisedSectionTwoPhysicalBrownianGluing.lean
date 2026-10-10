module

public import GeneralDepthPaper.RevisedSectionTwoPhysicalBrownianSums
public import GeneralDepthPaper.RevisedSectionTwoPhysicalBrownian
public import GeneralDepthPaper.RevisedSectionTwoPhysicalBrownianCell

@[expose] public section

/-! Joining the actual physical Brownian Hessian sums over all finite CDF
cells. The stochastic integral is constructed from these sums; convergence
and identification with the actual continuous gradient are proved separately. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus Paper
open scoped Topology NNReal ENNReal

namespace GeneralDepthPaper
open FourPapersCommon SpinGlass.Targets

theorem finiteSchemePhysicalHessianSum_sub_tendsto_of_cells
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) {k : ℕ}
    (s : RSBScheme k) (t : ℝ≥0) (n : ℕ)
    (hcell : ∀ i ∈ Finset.range (k+2),
      TendstoInMeasure canonicalBrownianMeasure
        (fun j sample =>
          finiteSchemePhysicalHessianCellSum Ξ μ (sectionTwoPhysicalBrownian Ξ)
            (physicalVolatility Ξ) s t n i j sample -
          finiteSchemePhysicalHessianCellSum Ξ μ (sectionTwoExtendedClockDriver Ξ)
            (fun _ => 1) s t n i j sample) atTop (fun _ => 0)) :
    TendstoInMeasure canonicalBrownianMeasure
      (fun j sample =>
        finiteSchemePhysicalHessianSum Ξ μ (sectionTwoPhysicalBrownian Ξ)
          (physicalVolatility Ξ) s t n j sample -
        finiteSchemePhysicalHessianSum Ξ μ (sectionTwoExtendedClockDriver Ξ)
          (fun _ => 1) s t n j sample) atTop (fun _ => 0) := by
  have h := tendstoInMeasure_finset_sum (Finset.range (k+2))
    (fun i j sample =>
      finiteSchemePhysicalHessianCellSum Ξ μ (sectionTwoPhysicalBrownian Ξ)
        (physicalVolatility Ξ) s t n i j sample -
      finiteSchemePhysicalHessianCellSum Ξ μ (sectionTwoExtendedClockDriver Ξ)
        (fun _ => 1) s t n i j sample)
    (fun _ _ => 0) hcell
  simpa only [Finset.sum_sub_distrib, Finset.sum_const_zero,
    finiteSchemePhysicalHessianSum] using h

theorem sectionTwoHessianPhysicalBrownianLeftSums_sub_clock_tendsto
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) (q : Overlap) (n : ℕ) :
    TendstoInMeasure canonicalBrownianMeasure
      (fun j sample =>
        sectionTwoHessianPhysicalBrownianLeftSums Ξ μ hμ (sectionTwoPhysicalBrownian Ξ)
          q n j sample - sectionTwoHessianClockLeftSums Ξ μ hμ q n j sample)
      atTop (fun _ => 0) := by
  have ht : (sectionTwoBrownianTime Ξ q : ℝ) ≤ 1 := by
    rw [sectionTwoBrownianTime, Real.coe_toNNReal _ (Ξ.clock_mem_unit q.property).1]
    exact (Ξ.clock_mem_unit q.property).2
  have h : TendstoInMeasure canonicalBrownianMeasure
      (fun j sample =>
        sectionTwoHessianPhysicalBrownianLeftSums Ξ μ hμ (sectionTwoPhysicalBrownian Ξ)
          q n j sample - sectionTwoHessianPhysicalClockLeftSums Ξ μ hμ q n j sample)
      atTop (fun _ => 0) :=
    finiteSchemePhysicalHessianSum_sub_tendsto_of_cells Ξ μ
      (sectionTwoMixedFiniteScheme Ξ μ hμ) (sectionTwoBrownianTime Ξ q) n
      (fun i hi => finiteSchemePhysicalHessianCellSum_sub_tendsto Ξ μ _ _ ht n i
        (by have := Finset.mem_range.mp hi; omega))
  simpa only [sectionTwoHessianPhysicalClockLeftSums_eq_clock] using h

theorem sectionTwoHessianPhysicalBrownianLeftSums_tendsto_clock
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) (q : Overlap) (n : ℕ) :
    TendstoInMeasure canonicalBrownianMeasure
      (fun j => sectionTwoHessianPhysicalBrownianLeftSums Ξ μ hμ
        (sectionTwoPhysicalBrownian Ξ) q n j) atTop
      (sectionTwoHessianClockInnerLimit Ξ μ hμ q n) := by
  have h := (sectionTwoHessianPhysicalBrownianLeftSums_sub_clock_tendsto Ξ μ hμ q n).add_real_noMeas
    (sectionTwoHessianClockLeftSums_tendsto Ξ μ hμ q n)
  simpa only [sub_add_cancel, zero_add] using h

theorem sectionTwoHessianPhysicalBrownianInnerLimit_eq_clock
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) (q : Overlap) (n : ℕ) :
    sectionTwoHessianPhysicalBrownianInnerLimit Ξ μ hμ (sectionTwoPhysicalBrownian Ξ) q n
      =ᵐ[canonicalBrownianMeasure] sectionTwoHessianClockInnerLimit Ξ μ hμ q n :=
  stochasticProbabilityLimit_eq
    (sectionTwoHessianPhysicalBrownianLeftSums_tendsto_clock Ξ μ hμ q n)

theorem sectionTwoHessianPhysicalBrownianLeftSums_tendsto
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) (q : Overlap) (n : ℕ) :
    TendstoInMeasure canonicalBrownianMeasure
      (fun j => sectionTwoHessianPhysicalBrownianLeftSums Ξ μ hμ
        (sectionTwoPhysicalBrownian Ξ) q n j) atTop
      (sectionTwoHessianPhysicalBrownianInnerLimit Ξ μ hμ (sectionTwoPhysicalBrownian Ξ) q n) :=
  stochasticProbabilityLimit_tendsto
    ⟨_, sectionTwoHessianPhysicalBrownianLeftSums_tendsto_clock Ξ μ hμ q n⟩

theorem sectionTwoHessianPhysicalBrownianInnerLimit_tendsto
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) (q : Overlap) :
    TendstoInMeasure canonicalBrownianMeasure
      (fun n => sectionTwoHessianPhysicalBrownianInnerLimit Ξ μ hμ
        (sectionTwoPhysicalBrownian Ξ) q n) atTop (sectionTwoGradientProcess Ξ μ q) :=
  (sectionTwoHessianClockInnerLimit_tendsto Ξ μ hμ q).congr_left
    (fun n => (sectionTwoHessianPhysicalBrownianInnerLimit_eq_clock Ξ μ hμ q n).symm)

/-- The literal physical Brownian integral, independently constructed from
actual sigma-times-Hessian left sums, equals the actual gradient. -/
theorem sectionTwoHessianPhysicalBrownianIntegral_eq
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) (q : Overlap) :
    sectionTwoHessianPhysicalBrownianIntegral Ξ μ hμ (sectionTwoPhysicalBrownian Ξ) q
      =ᵐ[canonicalBrownianMeasure] sectionTwoGradientProcess Ξ μ q :=
  stochasticProbabilityLimit_eq
    (sectionTwoHessianPhysicalBrownianInnerLimit_tendsto Ξ μ hμ q)

theorem sectionTwoHessianPhysicalBrownianIntegral_aestronglyMeasurable
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) (q : Overlap) :
    AEStronglyMeasurable
      (sectionTwoHessianPhysicalBrownianIntegral Ξ μ hμ (sectionTwoPhysicalBrownian Ξ) q)
      canonicalBrownianMeasure :=
  (measurable_sectionTwoGradientProcess_fixed Ξ μ q).aestronglyMeasurable.congr
    (sectionTwoHessianPhysicalBrownianIntegral_eq Ξ μ hμ q).symm

/-- The actual continuous gradient is a continuous modification of the
physical Brownian integral. This does not assert an uncountable intersection
of coordinatewise probability-one events. -/
theorem sectionTwoHessianPhysicalBrownianIntegral_continuous_modification
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) :
    (∀ sample, Continuous (fun q => sectionTwoGradientProcess Ξ μ q sample)) ∧
    (∀ q, sectionTwoHessianPhysicalBrownianIntegral Ξ μ hμ (sectionTwoPhysicalBrownian Ξ) q
      =ᵐ[canonicalBrownianMeasure] sectionTwoGradientProcess Ξ μ q) :=
  ⟨continuous_sectionTwoGradientProcess_path Ξ μ,
    sectionTwoHessianPhysicalBrownianIntegral_eq Ξ μ hμ⟩

/-- The complete finite-atomic physical-time stochastic clause of Lemma 2.2.
The Brownian law, common state driver and progressive coefficient are proved
in their separate concrete modules; there is no representation hypothesis. -/
theorem revised_lemma_2_2_finite_atomic_physical_stochastic
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) :
    (∀ q n, TendstoInMeasure canonicalBrownianMeasure
      (fun j => sectionTwoHessianPhysicalBrownianLeftSums Ξ μ hμ
        (sectionTwoPhysicalBrownian Ξ) q n j) atTop
      (sectionTwoHessianPhysicalBrownianInnerLimit Ξ μ hμ (sectionTwoPhysicalBrownian Ξ) q n)) ∧
    (∀ q, TendstoInMeasure canonicalBrownianMeasure
      (fun n => sectionTwoHessianPhysicalBrownianInnerLimit Ξ μ hμ
        (sectionTwoPhysicalBrownian Ξ) q n) atTop (sectionTwoGradientProcess Ξ μ q)) ∧
    (∀ q, sectionTwoHessianPhysicalBrownianIntegral Ξ μ hμ (sectionTwoPhysicalBrownian Ξ) q
      =ᵐ[canonicalBrownianMeasure] sectionTwoGradientProcess Ξ μ q) :=
  ⟨sectionTwoHessianPhysicalBrownianLeftSums_tendsto Ξ μ hμ,
    sectionTwoHessianPhysicalBrownianInnerLimit_tendsto Ξ μ hμ,
    sectionTwoHessianPhysicalBrownianIntegral_eq Ξ μ hμ⟩

end GeneralDepthPaper
