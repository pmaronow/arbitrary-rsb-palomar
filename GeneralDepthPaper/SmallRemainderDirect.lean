module

public import GeneralDepthPaper.SmallRemainderDerivative

@[expose] public section


/-! Full two-sided small remainders directly construct the derivative; no
prior differentiability is needed. -/
noncomputable section
open Set Filter
open scoped Topology
namespace GeneralDepthPaper

theorem hasDerivAt_of_small_remainder (f : ℝ→ℝ) (d : ℝ) (E : ℝ→ℝ)
    (hE : Tendsto E (𝓝 (0:ℝ)) (𝓝 0))
    (hb : ∀ᶠt in 𝓝 (0:ℝ),‖f t-f 0-d*t‖≤E t*|t|) : HasDerivAt f d 0 := by
  apply HasDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [hb,hE.eventually (eventually_lt_nhds hε)] with t ht hEt
  simpa only [sub_zero,smul_eq_mul,mul_comm t d,Real.norm_eq_abs] using
    ht.trans (mul_le_mul_of_nonneg_right hEt.le (abs_nonneg t))

end GeneralDepthPaper
