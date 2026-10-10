module

public import GeneralDepthPaper.EndpointStrip
public import GeneralDepthPaper.CutoffRecursionDifferenceBound

@[expose] public section


/-! Strict endpoint signs follow from the actual two-sided deficit scale
and the manuscript's strict choices of strip exponents. -/
noncomputable section
open Set Filter
open scoped Topology
namespace GeneralDepthPaper
set_option maxHeartbeats 1000000

theorem deficit_scale_strict_strip_separation {e lo hi cQ CQ b D : ℝ}
    (he : 0 < e) (hlo : 0 < lo) (hD : 0 ≤ D) (hb : 0 < b)
    (hcQ : cQ < e^2*lo/2) (hCQ : hi/2 < CQ) :
    ∀ᶠp:ℕ in atTop,1 ≤ p ∧ ∀m∈Icc e 1,∀lam∈Icc lo hi,
      D*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-m^2*lam*(p:ℝ)/2) < Real.exp (-cQ*(p:ℝ)) ∧
      Real.exp (-CQ*(p:ℝ)) < b*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-m^2*lam*(p:ℝ)/2) := by
  have hdl : 0 < e^2*lo/2-cQ := sub_pos.mpr hcQ
  have hdr : 0 < CQ-hi/2 := sub_pos.mpr hCQ
  have hlimL := tendsto_nat_polynomial_exp D (e^2*lo/2-cQ) 0 hdl
  have hlimR := tendsto_nat_polynomial_exp 1 (CQ-hi/2) 1 hdr
  filter_upwards [hlimL.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1)),
    hlimR.eventually (Iio_mem_nhds hb),eventually_ge_atTop (1:ℕ)] with p hL hR hp
  simp only [pow_zero,mul_one] at hL
  simp only [pow_one,one_mul] at hR
  refine ⟨hp,?_⟩
  intro m hm lam hl
  have hm0 : 0 ≤ m := he.le.trans hm.1
  have hl0 : 0 ≤ lam := hlo.le.trans hl.1
  have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0:ℝ) < p := zero_lt_one.trans_le hpR
  have hrateL : e^2*lo ≤ m^2*lam := mul_le_mul
    (by nlinarith [hm.1] : e^2 ≤ m^2) hl.1 hlo.le (sq_nonneg _)
  have hrateR : m^2*lam ≤ hi := by
    have hh := mul_le_mul_of_nonneg_right (show m^2 ≤ 1 by nlinarith [hm.2]) hl0
    linarith [hl.2]
  have hpowU : (p:ℝ)^(-(1/2:ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hpR (by norm_num)
  have hpowL : (p:ℝ)⁻¹ ≤ (p:ℝ)^(-(1/2:ℝ)) := by
    simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le hpR
      (by norm_num : (-1:ℝ) ≤ -(1/2:ℝ))
  have heL : Real.exp (-(e^2*lo/2)*(p:ℝ))=
      Real.exp (-(e^2*lo/2-cQ)*(p:ℝ))*Real.exp (-cQ*(p:ℝ)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have heR : Real.exp (-CQ*(p:ℝ))=
      Real.exp (-(CQ-hi/2)*(p:ℝ))*Real.exp (-hi*(p:ℝ)/2) := by
    rw [←Real.exp_add]
    congr 1
    ring
  constructor
  · have hbound : D*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-m^2*lam*(p:ℝ)/2) ≤
        D*Real.exp (-(e^2*lo/2)*(p:ℝ)) := by
      apply mul_le_mul
      · simpa only [mul_one] using mul_le_mul_of_nonneg_left hpowU hD
      · apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hrateL hp0.le]
      · exact (Real.exp_pos _).le
      · exact hD
    apply hbound.trans_lt
    rw [heL,←mul_assoc]
    exact (mul_lt_mul_of_pos_right hL (Real.exp_pos _)).trans_eq (one_mul _)
  · have hratio : Real.exp (-(CQ-hi/2)*(p:ℝ)) < b*(p:ℝ)⁻¹ := by
      rw [←div_eq_mul_inv]
      exact (lt_div_iff₀ hp0).mpr (by simpa only [mul_comm] using hR)
    rw [heR]
    apply (mul_lt_mul_of_pos_right hratio (Real.exp_pos _)).trans_le
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpowL hb.le)
      (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hrateR hp0.le]))
      (Real.exp_pos _).le (mul_nonneg hb.le (Real.rpow_nonneg hp0.le _))

end GeneralDepthPaper
