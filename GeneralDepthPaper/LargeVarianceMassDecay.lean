module

public import GeneralDepthPaper.LargeVarianceMassBounds
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section


/-! All actual mass-parameter residual derivatives decay exponentially in
space, uniformly when the mass stays above a fixed positive number. This is a
proved prerequisite for the remaining Gaussian mixed-jet argument in B.1. -/
noncomputable section
namespace GeneralDepthPaper

 theorem polynomial_times_exp_bound (j:ℕ) {ε c u:ℝ} (hε:0<ε) (hc:0≤c) (hu:0≤u) :
     (c+u)^j*Real.exp (-ε*u)≤(j.factorial:ℝ)/ε^j*Real.exp (ε*c) := by
   have hR:0≤c+u:=add_nonneg hc hu
   have hfac:0<(j.factorial:ℝ):=by exact_mod_cast Nat.factorial_pos j
   have hεj:0<ε^j:=pow_pos hε j
   have hh:=Real.pow_div_factorial_le_exp (ε*(c+u)) (mul_nonneg hε.le hR) j
   have hm:=mul_le_mul_of_nonneg_right hh (Real.exp_pos (-ε*u)).le
   have hexp:Real.exp (ε*(c+u))*Real.exp (-ε*u)=Real.exp (ε*c):=by
     rw [←Real.exp_add];congr 1;ring
   rw [hexp,mul_pow,div_mul_eq_mul_div] at hm
   rw [div_mul_eq_mul_div]
   apply (le_div_iff₀ hεj).mpr
   have hn:=(div_le_iff₀ hfac).mp hm
   convert hn using 1 <;> ring

 def largeVarianceMassDecayConstant (ε:ℝ) (j:ℕ):ℝ :=
   ((j:ℝ)+2)*((j.factorial:ℝ)/(ε/2)^j)*Real.exp ((ε/2)*(1+Real.log 2))

 theorem largeVarianceMassDecayConstant_pos {ε:ℝ} (hε:0<ε) (j:ℕ) :
     0<largeVarianceMassDecayConstant ε j := by
   unfold largeVarianceMassDecayConstant
   have hf:0<(j.factorial:ℝ):=by exact_mod_cast Nat.factorial_pos j
   positivity

 theorem largeVarianceResidualMassJet_decay (j:ℕ) {ε m:ℝ} (hε:0<ε) (hεm:ε≤m)
     (hm1:m≤1) (x:ℝ) :
     |largeVarianceResidualMassJet j m x|≤
       largeVarianceMassDecayConstant ε j*Real.exp (-(ε/2)*|x|) := by
   have hbound:|largeVarianceResidualMassJet j m x|≤
       ((j:ℝ)+2)*(1+|x|+Real.log 2)^j*Real.exp (-ε*|x|):=by
     rcases le_total 0 x with hx|hx
     · simpa only [abs_of_nonneg hx] using largeVarianceResidualMassJet_positive_bound j hε hεm hm1 hx
     · have hn:=largeVarianceResidualMassJet_positive_bound j hε hεm hm1 (neg_nonneg.mpr hx)
       simpa only [largeVarianceResidualMassJet_even,abs_of_nonpos hx] using hn
   have hpoly:=polynomial_times_exp_bound j (ε:=ε/2) (c:=1+Real.log 2) (u:=|x|)
     (by positivity) (by have hl:=Real.log_nonneg (by norm_num : (1:ℝ)≤2);linarith) (abs_nonneg x)
   have he:Real.exp (-ε*|x|)=Real.exp (-(ε/2)*|x|)*Real.exp (-(ε/2)*|x|):=by
     rw [←Real.exp_add];congr 1;ring
   apply hbound.trans
   rw [he]
   unfold largeVarianceMassDecayConstant
   have hm:=mul_le_mul_of_nonneg_right
     (mul_le_mul_of_nonneg_left hpoly (by positivity : (0:ℝ)≤(j:ℝ)+2))
     (Real.exp_pos (-(ε/2)*|x|)).le
   convert hm using 1 <;> ring

 theorem iteratedDeriv_largeVarianceResidual_mass_decay (j:ℕ) {ε m:ℝ} (hε:0<ε)
     (hεm:ε≤m) (hm1:m≤1) (x:ℝ) :
     ‖iteratedDeriv j (fun r=>largeVarianceResidual r x) m‖≤
       largeVarianceMassDecayConstant ε j*Real.exp (-(ε/2)*|x|) := by
   rw [iteratedDeriv_largeVarianceResidual_mass,Real.norm_eq_abs]
   exact largeVarianceResidualMassJet_decay j hε hεm hm1 x

end GeneralDepthPaper
