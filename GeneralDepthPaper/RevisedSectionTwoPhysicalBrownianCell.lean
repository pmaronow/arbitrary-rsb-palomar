module

public import GeneralDepthPaper.RevisedSectionTwoPhysicalBrownianIntegral

@[expose] public section

/-! The physical Brownian Hessian comparison on each cropped finite CDF
cell. Its partitions lie in the closed physical interval, so it includes
both endpoint atoms and covariances with zero volatility at the origin. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus Paper
open scoped Topology NNReal ENNReal

namespace GeneralDepthPaper
open FourPapersCommon SpinGlass.Targets

theorem finiteSchemePhysicalHessianCellSum_sub_tendsto
    (Ξ : AdmissibleCovariance) (μ : ParisiMeasure) {k : ℕ}
    (s : RSBScheme k) (t : ℝ≥0) (ht : (t : ℝ) ≤ 1)
    (n i : ℕ) (hi : i ≤ k+1) :
    TendstoInMeasure canonicalBrownianMeasure
      (fun j sample =>
        finiteSchemePhysicalHessianCellSum Ξ μ (sectionTwoPhysicalBrownian Ξ)
          (physicalVolatility Ξ) s t n i j sample -
        finiteSchemePhysicalHessianCellSum Ξ μ (sectionTwoExtendedClockDriver Ξ)
          (fun _ => 1) s t n i j sample) atTop (fun _ => 0) := by
  let a := stochasticClippedNode s t i
  let b := stochasticClippedNode s t (i+1)
  let l := (stochasticCropLeft a b n).toNNReal
  let r := (stochasticCropRight a b n).toNNReal
  by_cases hab : a < b
  · have ha : 0 ≤ a := le_min t.property (s.q_nonneg (by omega))
    obtain ⟨hl0, _hl, hlr, hr⟩ := stochasticCrop_bounds ha hab n
    have hr0 : 0 ≤ stochasticCropRight a b n := hl0.trans hlr
    have hle : (l : ℝ) = stochasticCropLeft a b n := Real.coe_toNNReal _ hl0
    have hre : (r : ℝ) = stochasticCropRight a b n := Real.coe_toNNReal _ hr0
    have hlrN : l ≤ r := by
      exact_mod_cast (show (l : ℝ) ≤ (r : ℝ) by rw [hle, hre]; exact hlr)
    have hr1 : (r : ℝ) ≤ 1 := by
      rw [hre]
      exact hr.le.trans ((min_le_left _ _).trans ht)
    have hunit : l + (r-l) ≤ 1 := by
      rw [add_tsub_cancel_of_le hlrN]
      exact_mod_cast hr1
    have hpart := sectionTwoPhysicalHessianPartitionDifference_tendsto Ξ μ l (r-l) hunit
    change TendstoInMeasure canonicalBrownianMeasure
      (fun j sample => sectionTwoPhysicalHessianPartitionDifference Ξ μ l (r-l) j sample)
      atTop (fun _ => 0) at hpart
    simpa only [finiteSchemePhysicalHessianCellSum,
      sectionTwoPhysicalHessianPartitionDifference, a, b, l, r, ite_eq_left hab] using hpart
  · have hz : TendstoInMeasure canonicalBrownianMeasure
        (fun _ : ℕ => fun _ : BrownianSample => (0 : ℝ)) atTop (fun _ => 0) :=
      tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
        (Eventually.of_forall (fun _ => tendsto_const_nhds))
    simpa only [finiteSchemePhysicalHessianCellSum, a, b, ite_eq_right hab, sub_self] using hz

end GeneralDepthPaper
