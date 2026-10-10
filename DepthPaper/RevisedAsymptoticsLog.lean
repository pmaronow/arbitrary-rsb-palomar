module

public import DepthPaper.StationaryGardnerAsymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! The logarithmic location normalization in Revision (16), Corollary 5.2. -/
noncomputable section
namespace DepthPaper

theorem logarithmic_location_of_two_sided {p x E C : ℝ}
    (hp : 0 < p) (hC : 1 ≤ C)
    (hlower : C⁻¹ * p ^ (-(1 / 2 : ℝ)) * Real.exp (-E) ≤ x)
    (hupper : x ≤ C * p ^ (-(1 / 2 : ℝ)) * Real.exp (-E)) :
    |Real.log (1 / x) - E - (1 / 2 : ℝ) * Real.log p| ≤ C := by
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hpow : 0 < p ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hp _
  have hlowpos : 0 < C⁻¹ * p ^ (-(1 / 2 : ℝ)) * Real.exp (-E) := by positivity
  have hx : 0 < x := hlowpos.trans_le hlower
  have hloglo := Real.log_le_log hlowpos hlower
  have hloghi := Real.log_le_log hx hupper
  rw [Real.log_mul (mul_pos (inv_pos.mpr hCp) hpow).ne' (Real.exp_pos _).ne',
    Real.log_mul (inv_pos.mpr hCp).ne' hpow.ne', Real.log_inv,
    Real.log_rpow hp, Real.log_exp] at hloglo
  rw [Real.log_mul (mul_pos hCp hpow).ne' (Real.exp_pos _).ne',
    Real.log_mul hCp.ne' hpow.ne', Real.log_rpow hp, Real.log_exp] at hloghi
  rw [Real.log_div one_ne_zero hx.ne', Real.log_one, zero_sub]
  have hlogC := Real.log_le_sub_one_of_pos hCp
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end DepthPaper
