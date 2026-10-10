module

public import DepthPaper.BranchMassAsymptotics
public import Mathlib.Analysis.Asymptotics.Lemmas

@[expose] public section


/-! The genuine diagonal o(delta) passage for the atom-mass asymptotic. -/
noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace DepthPaper
set_option maxHeartbeats 600000

theorem branch_mass_diagonal_small_o (d e k : ℕ→ℝ) {κ C : ℝ}
    (hκ : 0 < κ) (hC : 0≤C) (hd : Tendsto d atTop (𝓝 0))
    (hk : Tendsto k atTop (𝓝 κ)) (hpos : ∀ᶠj in atTop,0 < d j)
    (herror : ∀ᶠj in atTop,|e j-d j/(2*k j)|≤C*(d j)^2) :
    (fun j=>e j-d j/(2*κ)) =o[atTop] d := by
  let R:ℕ→ℝ:=fun j=>(e j-d j/(2*k j))/d j
  have hnorm : Tendsto (fun j=>‖R j‖) atTop (𝓝 0) := by
    have hu : ∀ᶠj in atTop,‖R j‖≤C*d j := by
      filter_upwards [hpos,herror] with j hp he
      dsimp only [R]
      rw [Real.norm_eq_abs,abs_div,abs_of_pos hp]
      apply (div_le_iff₀ hp).mpr
      convert he using 1 <;> ring
    have hlim:Tendsto (fun j=>C*d j) atTop (𝓝 0):=by simpa only [mul_zero] using hd.const_mul C
    exact squeeze_zero' (.of_forall fun j=>norm_nonneg _) hu hlim
  have hR:Tendsto R atTop (𝓝 0):=tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hrecip:Tendsto (fun j=>(2*k j)⁻¹-(2*κ)⁻¹) atTop (𝓝 0) := by
    have hh:=((hk.const_mul 2).inv₀ (by positivity : (2*κ:ℝ)≠0)).sub
      (tendsto_const_nhds (x:=(2*κ)⁻¹))
    simpa only [sub_self] using hh
  have ht:Tendsto (fun j=>(e j-d j/(2*κ))/d j) atTop (𝓝 0) := by
    have hh:=hR.add hrecip
    simp only [zero_add] at hh
    apply hh.congr'
    filter_upwards [hpos] with j hp
    dsimp only [R]
    field_simp [hp.ne']
    <;> ring
  apply (isLittleO_iff_tendsto' ?_).mpr ht
  filter_upwards [hpos] with j hp hzero
  exact (hp.ne' hzero).elim

end DepthPaper
