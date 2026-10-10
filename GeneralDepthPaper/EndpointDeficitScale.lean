module

public import GeneralDepthPaper.DoobEndpointAverageBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section


/-! Literal Gaussian endpoint scale and its uniform comparison under a
bounded variance error. Constants retain the full m²λp exponential. -/
noncomputable section
open Set
namespace GeneralDepthPaper
set_option maxHeartbeats 800000

def degreeDeficitScale (m lam:ℝ) (p:ℕ):ℝ :=
  (Real.sqrt (p:ℝ))⁻¹*Real.exp (-m^2*lam*(p:ℝ)/2)

theorem degreeDeficitScale_eq_rpow (m lam:ℝ) (p:ℕ):
    degreeDeficitScale m lam p=(p:ℝ)^(-(1/2:ℝ))*Real.exp (-m^2*lam*(p:ℝ)/2):=by
  unfold degreeDeficitScale
  rw [Real.rpow_neg (Nat.cast_nonneg p),←Real.sqrt_eq_rpow]

theorem variance_endpoint_scale_bounds {m lam W E a C:ℝ} (hm:m∈Icc (0:ℝ) 1)
    (hE:0≤E) (ha:0 < a) (hC:0 < C) (p:ℕ) (hp:1≤p)
    (hlo:a*(p:ℝ)≤W) (hup:W≤C*(p:ℝ)) (herror:|W-lam*(p:ℝ)|≤E):
    (Real.sqrt (2*Real.pi*C))⁻¹*Real.exp (-E/2)*degreeDeficitScale m lam p≤
      (Real.sqrt (2*Real.pi*W))⁻¹*Real.exp (-m^2*W/2) ∧
    (Real.sqrt (2*Real.pi*W))⁻¹*Real.exp (-m^2*W/2)≤
      (Real.sqrt (2*Real.pi*a))⁻¹*Real.exp (E/2)*degreeDeficitScale m lam p := by
  have hpR:0 < (p:ℝ):=by exact_mod_cast (zero_lt_one.trans_le hp)
  have hW:0 < W:=(mul_pos ha hpR).trans_le hlo
  have hpref:0 < Real.sqrt (2*Real.pi*W):=by positivity
  have hsq:m^2≤1:=by nlinarith [sq_nonneg m,hm.1,hm.2]
  have hscaled:|m^2*(W-lam*(p:ℝ))|≤E:=by
    rw [abs_mul,abs_of_nonneg (sq_nonneg m)]
    calc
      m^2*|W-lam*(p:ℝ)|≤m^2*E:=mul_le_mul_of_nonneg_left herror (sq_nonneg _)
      _≤1*E:=mul_le_mul_of_nonneg_right hsq hE
      _=E:=one_mul _
  have helo:Real.exp (-E/2)*Real.exp (-m^2*lam*(p:ℝ)/2)≤Real.exp (-m^2*W/2):=by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [(abs_le.mp hscaled).2]
  have heup:Real.exp (-m^2*W/2)≤Real.exp (E/2)*Real.exp (-m^2*lam*(p:ℝ)/2):=by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [(abs_le.mp hscaled).1]
  have hslo:(Real.sqrt (2*Real.pi*C))⁻¹*(Real.sqrt (p:ℝ))⁻¹≤
      (Real.sqrt (2*Real.pi*W))⁻¹:=by
    have hh:Real.sqrt (2*Real.pi*W)≤Real.sqrt (2*Real.pi*C)*Real.sqrt (p:ℝ):=by
      rw [←Real.sqrt_mul (by positivity : 0≤2*Real.pi*C)]
      exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
    have hi:=inv_anti₀ hpref hh
    rw [mul_inv_rev] at hi
    convert hi using 1 <;> ring
  have hsup:(Real.sqrt (2*Real.pi*W))⁻¹≤
      (Real.sqrt (2*Real.pi*a))⁻¹*(Real.sqrt (p:ℝ))⁻¹:=by
    have hh:Real.sqrt (2*Real.pi*a)*Real.sqrt (p:ℝ)≤Real.sqrt (2*Real.pi*W):=by
      rw [←Real.sqrt_mul (by positivity : 0≤2*Real.pi*a)]
      exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
    have hi:=inv_anti₀ (by positivity : 0 < Real.sqrt (2*Real.pi*a)*Real.sqrt (p:ℝ)) hh
    rw [mul_inv_rev] at hi
    convert hi using 1 <;> ring
  constructor
  · have hh:=mul_le_mul hslo helo (by positivity) (by positivity)
    convert hh using 1 <;> unfold degreeDeficitScale <;> ring
  · have hh:=mul_le_mul hsup heup (by positivity) (by positivity)
    convert hh using 1 <;> unfold degreeDeficitScale <;> ring

end GeneralDepthPaper
