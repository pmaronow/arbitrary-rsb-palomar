module

public import FourPapersCommon.AllFieldMoments
public import FourPapersCommon.MixedMeasure
public import FRSB.ParisiControlCovariance
public import FRSB.MomentKernelClamp
public import FRSB.CDFMeasureExt

@[expose] public section

/-! Injectivity of terminal drift with the optimal control held fixed. Unlike
the strict-convexity assembly, the reference order parameter is arbitrary.
This is the mass-direction detection used in the revised Hessian argument. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace DepthPaper
open Paper FourPapersCommon

theorem fixed_feedback_drift_injective (β h : ℝ) (hβ : β ≠ 0)
    (ρ μ ν : Paper.ParisiMeasure)
    (hd : parisiControlDrift β μ (selectedParisiFeedbackControl β h ρ)
      =ᵐ[canonicalBrownianMeasure]
      parisiControlDrift β ν (selectedParisiFeedbackControl β h ρ)) : μ = ν := by
  have hkernel := FRSB.selectedParisi_cdfKernel_zero_of_drift_ae_eq β h hβ ρ μ ν hd
  apply FRSB.eq_of_parisiCDF_tail_integrals_eq_zero μ ν
  apply FRSB.tailIntegral_eq_zero_of_unitMomentKernel_zero
    (fun s => parisiCDF μ s - parisiCDF ν s)
    (selectedParisiSecondMoment β h hβ ρ)
    (fun s => β ^ 2 * fieldCurvatureMoment2 β h hβ ρ s)
    ((parisiCDF_measurable μ).sub (parisiCDF_measurable ν))
    (norm_parisiCDF_sub_le_one μ ν) (β ^ 2).toNNReal
    (continuousOn_selectedParisiSecondMoment β h hβ ρ)
  · intro s hs
    exact FourPapersCommon.hasDerivAt_Gamma β h hβ ρ hs
  · intro s hs
    have hp := fieldCurvatureMoment2_pos β h hβ ρ ⟨hs.1.le, hs.2.le⟩
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg β), Real.norm_of_nonneg hp.le,
      Real.coe_toNNReal _ (sq_nonneg β)]
    exact (mul_le_mul_of_nonneg_left (fieldCurvatureMoment2_le_one β h hβ ρ s)
      (sq_nonneg β)).trans_eq (mul_one _)
  · intro s hs
    exact (mul_pos (sq_pos_of_ne_zero hβ)
      (fieldCurvatureMoment2_pos β h hβ ρ ⟨hs.1.le, hs.2.le⟩)).ne'
  · intro s hs
    exact hkernel s ⟨hs.1.le, hs.2.le⟩

/-- The same detection statement after the genuine mixed-covariance clock
transport. It applies also to covariances with a quadratic interaction. -/
theorem mixed_fixed_feedback_drift_injective (ξ : AdmissibleEvenMixture)
    (h : ℝ) (ρ μ ν : Paper.ParisiMeasure)
    (hd : parisiControlDrift (mixedBeta ξ) (mixedMeasure ξ μ)
        (selectedParisiFeedbackControl (mixedBeta ξ) h (mixedMeasure ξ ρ))
      =ᵐ[canonicalBrownianMeasure]
      parisiControlDrift (mixedBeta ξ) (mixedMeasure ξ ν)
        (selectedParisiFeedbackControl (mixedBeta ξ) h (mixedMeasure ξ ρ))) : μ = ν := by
  exact mixedMeasure_injective ξ
    (fixed_feedback_drift_injective (mixedBeta ξ) h (mixedBeta_ne_zero ξ)
      (mixedMeasure ξ ρ) (mixedMeasure ξ μ) (mixedMeasure ξ ν) hd)

end DepthPaper
