module

public import FourPapersCommon.ParisiSharpGradientGrid
public import Paper.ParisiHJBBase

set_option backward.privateInPublic true

@[expose] public section


/-! The sharp global CDF-L1 gradient comparison for the actual arbitrary-profile
Parisi solution. The proof passes genuine common-grid comparisons through the
uniform finite-gradient limit; no classical time regularity is imposed at atoms. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace FourPapersCommon
open Paper

private theorem tendsto_sharpGridGradient (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t x : ℝ) :
    Tendsto (fun n => parisiFiniteGradient (parisiGridRSBScheme μ n) β (t,x))
      atTop (𝓝 (parisiGradient β μ (t,x))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => by simpa only [norm_sub_rev] using parisiHJBGradientError_bound β μ n t x)
    (tendsto_parisiHJBGradientError β hβ μ)

/-- The quoted sharp scalar constant, valid for all probability profiles,
including profiles with atoms at any time and both endpoints. -/
theorem parisiGradient_sharp_CDF_L1_bound (β : ℝ) (hβ : β ≠ 0)
    (μ ν : ParisiMeasure) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : ℝ) :
    ‖parisiGradient β ν (t,x) - parisiGradient β μ (t,x)‖ ≤
      Real.exp (β^2) * β^2 * parisiCDFDistance μ ν := by
  have hleft := ((tendsto_sharpGridGradient β hβ ν t x).sub
    (tendsto_sharpGridGradient β hβ μ t x)).norm
  have hright := (tendsto_parisiCDFDistance_grid_pair μ ν).const_mul (Real.exp (β^2) * β^2)
  exact le_of_tendsto_of_tendsto hleft hright (.of_forall fun n => by
    simpa only [Real.norm_eq_abs] using parisiFiniteGradient_grid_sharp_bound β hβ μ ν n t ht x)

end FourPapersCommon
