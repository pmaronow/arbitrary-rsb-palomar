module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Normed.Field.Lemmas

@[expose] public section


/-! Identify an existing ordinary derivative from a right-sided small
remainder. The ordinary differentiability hypothesis is supplied later by
the actual Gaussian recursion, rather than assuming the desired value. -/
noncomputable section
open Set Filter
open scoped Topology
namespace DepthPaper

theorem hasDerivAt_of_right_small_remainder (f : ℝ→ℝ) (d : ℝ)
    (hf : DifferentiableAt ℝ f 0) (E : ℝ→ℝ)
    (hE : Tendsto E (𝓝[>] (0:ℝ)) (𝓝 0))
    (hb : ∀ᶠt in 𝓝[>] (0:ℝ),‖f t-f 0-d*t‖≤E t*|t|) :
    HasDerivAt f d 0 := by
  let r : ℝ→ℝ := fun t=>f t-f 0-d*t
  have hr : HasDerivAt r (deriv f 0-d) 0 := by
    have hd : HasDerivAt (fun t : ℝ=>d*t) d 0 := by
      convert (hasDerivAt_id (0:ℝ)).const_mul d using 1 <;> simp
    convert (hf.hasDerivAt.sub_const (f 0)).sub hd using 1
  have hlim : Tendsto (fun t=>‖t⁻¹*r t‖) (𝓝[>] (0:ℝ)) (𝓝 ‖deriv f 0-d‖) := by
    simpa only [r,add_zero,zero_add,sub_self,mul_zero,sub_zero,smul_eq_mul] using hr.tendsto_slope_zero_right.norm
  have hle : ∀ᶠt in 𝓝[>] (0:ℝ),‖t⁻¹*r t‖≤E t := by
    filter_upwards [hb,self_mem_nhdsWithin] with t ht htp
    change 0<t at htp
    rw [norm_mul,norm_inv,Real.norm_eq_abs,abs_of_pos htp]
    have hh : ‖r t‖≤E t*t := by
      simpa only [r,abs_of_pos htp] using ht
    calc
      t⁻¹*‖r t‖≤t⁻¹*(E t*t) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr htp.le)
      _=E t := by field_simp [htp.ne']
  have hzero : ‖deriv f 0-d‖=0 := le_antisymm
    (le_of_tendsto_of_tendsto hlim hE hle) (norm_nonneg _)
  have he : deriv f 0=d := sub_eq_zero.mp (norm_eq_zero.mp hzero)
  exact he ▸ hf.hasDerivAt

end DepthPaper
