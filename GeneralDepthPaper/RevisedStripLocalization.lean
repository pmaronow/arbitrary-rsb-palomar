module

public import GeneralDepthPaper.CutoffRecursionDifferenceBound

@[expose] public section

/-! Localization in the literal Section 4 endpoint strip, obtained from
the two-sided endpoint deficit estimate by absorbing polynomial factors. -/
noncomputable section
open Set Filter
open scoped Topology
namespace GeneralDepthPaper

theorem revised_strip_localization {e lo hi b D : ℝ}
    (he : e ∈ Ioo (0 : ℝ) 1) (hlo : 0 < lo) (hLH : lo ≤ hi)
    (hb : 0 < b) (hD : 0 < D) :
    ∀ᶠ p : ℕ in atTop, ∀ m ∈ Icc e 1, ∀ lam ∈ Icc lo hi, ∀ Q : ℝ,
      b * (p : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-m^2 * lam * (p : ℝ) / 2) ≤ 1-Q →
      1-Q ≤ D * (p : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-m^2 * lam * (p : ℝ) / 2) →
      Q ∈ Ioo (1-Real.exp (-(e^2*lo/4)*(p : ℝ)))
        (1-Real.exp (-hi*(p : ℝ))) := by
  have hhi : 0 < hi := hlo.trans_le hLH
  have he0 : 0 < e := he.1
  have hc : 0 < e^2*lo/4 := by positivity
  have HU : ∀ᶠ p : ℕ in atTop,
      D * Real.exp (-(e^2*lo/4)*(p : ℝ)) < 1 := by
    simpa using (tendsto_nat_polynomial_exp D (e^2*lo/4) 0 hc).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have HL : ∀ᶠ p : ℕ in atTop,
      (p : ℝ)*Real.exp (-(hi/2)*(p : ℝ)) < b := by
    simpa using (tendsto_nat_polynomial_exp 1 (hi/2) 1 (by positivity)).eventually
      (eventually_lt_nhds hb)
  filter_upwards [HU, HL, eventually_ge_atTop (1 : ℕ)] with p hu hl hp
  intro m hm lam hlam Q hlower hupper
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  have hpow0 : 0 < (p : ℝ)^(-(1/2 : ℝ)) := Real.rpow_pos_of_pos hp0 _
  have hpow1 : (p : ℝ)^(-(1/2 : ℝ)) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num : -(1/2 : ℝ) ≤ 0)
  have hinv : (p : ℝ)⁻¹ ≤ (p : ℝ)^(-(1/2 : ℝ)) := by
    simpa only [Real.rpow_neg_one] using
      Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num : (-1 : ℝ) ≤ -(1/2 : ℝ))
  have hm0 : 0 ≤ m := he.1.le.trans hm.1
  have hm2lo : e^2 ≤ m^2 := by nlinarith [hm.1, sq_nonneg (m-e)]
  have hm2hi : m^2 ≤ 1 := by nlinarith [hm.2]
  have hprodlo : e^2*lo ≤ m^2*lam := by
    calc
      e^2*lo ≤ m^2*lo := mul_le_mul_of_nonneg_right hm2lo hlo.le
      _ ≤ m^2*lam := mul_le_mul_of_nonneg_left hlam.1 (sq_nonneg m)
  have hprodhi : m^2*lam ≤ hi := by
    calc
      m^2*lam ≤ 1*lam := mul_le_mul_of_nonneg_right hm2hi (hlo.le.trans hlam.1)
      _ ≤ hi := by simpa using hlam.2
  have hUexp : Real.exp (-m^2*lam*(p : ℝ)/2) ≤
      Real.exp (-(e^2*lo/2)*(p : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hprodlo hp0.le]
  have hLexp : Real.exp (-(hi/2)*(p : ℝ)) ≤
      Real.exp (-m^2*lam*(p : ℝ)/2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hprodhi hp0.le]
  have hU : D*(p : ℝ)^(-(1/2 : ℝ))*Real.exp (-m^2*lam*(p : ℝ)/2) <
      Real.exp (-(e^2*lo/4)*(p : ℝ)) := by
    have hUU := mul_lt_mul_of_pos_right hu
      (Real.exp_pos (-(e^2*lo/4)*(p : ℝ)))
    have hsplit : Real.exp (-(e^2*lo/2)*(p : ℝ)) =
        Real.exp (-(e^2*lo/4)*(p : ℝ))*Real.exp (-(e^2*lo/4)*(p : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      D*(p : ℝ)^(-(1/2 : ℝ))*Real.exp (-m^2*lam*(p : ℝ)/2)
          ≤ D*1*Real.exp (-(e^2*lo/2)*(p : ℝ)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow1 hD.le) hUexp
          (Real.exp_pos _).le (by positivity)
      _ < Real.exp (-(e^2*lo/4)*(p : ℝ)) := by
        rw [hsplit]
        nlinarith
  have hL : Real.exp (-hi*(p : ℝ)) <
      b*(p : ℝ)^(-(1/2 : ℝ))*Real.exp (-m^2*lam*(p : ℝ)/2) := by
    have hl' : Real.exp (-(hi/2)*(p : ℝ)) < b*(p : ℝ)⁻¹ := by
      apply (lt_mul_inv_iff₀ hp0).mpr
      simpa [mul_comm] using hl
    have hLL := mul_lt_mul_of_pos_right hl' (Real.exp_pos (-(hi/2)*(p : ℝ)))
    have hsplit : Real.exp (-hi*(p : ℝ)) =
        Real.exp (-(hi/2)*(p : ℝ))*Real.exp (-(hi/2)*(p : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hsplit] at hLL
    exact hLL.trans_le (mul_le_mul (mul_le_mul_of_nonneg_left hinv hb.le)
      hLexp (Real.exp_pos _).le (by positivity))
  constructor <;> linarith

end GeneralDepthPaper
