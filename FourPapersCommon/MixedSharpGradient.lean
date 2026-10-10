module

public import FourPapersCommon.ParisiSharpGradient
public import FourPapersCommon.MixedMomentL1

@[expose] public section


/-! The sharp original-overlap gradient estimate for the actual mixed model.
The variance-clock substitution retains every atom of both profiles. -/
noncomputable section
open Set
namespace FourPapersCommon

theorem mixedGradient_sharp_CDF_L1_bound (ξ : AdmissibleEvenMixture)
    (μ ν : ParisiMeasure) (q : ℝ) (hq : q ∈ Icc (0:ℝ) 1) (x : ℝ) :
    ‖mixedGradient ξ ν (q,x) - mixedGradient ξ μ (q,x)‖ ≤
      Real.exp (ξ.first 1) * ξ.second 1 * parisiCDFDistance μ ν := by
  have h := parisiGradient_sharp_CDF_L1_bound (mixedBeta ξ) (mixedBeta_ne_zero ξ)
    (mixedMeasure ξ μ) (mixedMeasure ξ ν) (ξ.clock q) (ξ.clock_mem_unitInterval hq) x
  change ‖mixedGradient ξ ν (q,x) - mixedGradient ξ μ (q,x)‖ ≤ _ at h
  have hc : 0 ≤ Real.exp (mixedBeta ξ ^ 2) * mixedBeta ξ ^ 2 :=
    mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  refine h.trans ((mul_le_mul_of_nonneg_left (mixedMeasure_CDF_L1_bound ξ μ ν) hc).trans_eq ?_)
  rw [mixedBeta_sq]
  have hv : ξ.variance ≠ 0 := ξ.variance_pos.ne'
  calc
    _ = Real.exp ξ.variance * ξ.second 1 * parisiCDFDistance μ ν := by
      field_simp [hv]
      <;> ring
    _ = _ := rfl

end FourPapersCommon
