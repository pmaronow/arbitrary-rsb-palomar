module

public import GeneralDepthPaper.UniformMassJetBounds

@[expose] public section


/-! Quantitative estimates for the mass jets of the spatial residual on the
positive half-line. Polynomial factors are retained explicitly before the
uniform exponential bound is proved. -/
noncomputable section
open Set
open scoped ContDiff Polynomial
namespace GeneralDepthPaper

 theorem bivariateValue_mass_uniform_bounds (P:Polynomial (Polynomial ℝ)) (J:ℕ) (a b:ℝ):
     ∃K:ℝ,1≤K ∧ ∀j≤J,∀m∈Icc a b,∀t∈Icc (-1:ℝ) 1,
       ‖iteratedDeriv j (fun r=>bivariateValue P r t) m‖≤K:=by
   obtain ⟨K,hK,hbound⟩:=bivariateMassJet_uniform_bounds P J a b
   refine ⟨K,hK,?_⟩
   intro j hj m hm t ht
   rw [iteratedDeriv_bivariateValue_mass]
   exact hbound j hj m hm t ht

 theorem contDiff_bivariateValue_mass (P:Polynomial (Polynomial ℝ)) (t:ℝ):
     ContDiff ℝ ∞ (fun m=>bivariateValue P m t):=by
   have he:(fun m=>bivariateValue P m t)=fun m=>bivariateMassJet P 0 m t:=by
     funext m;simp [bivariateValue_sum,bivariateMassJet]
   rw [he]
   exact (contDiff_bivariateMassJet P 0).comp (contDiff_id.prodMk contDiff_const)

 theorem tanh_endpoint_gap_bound (x:ℝ):
     ‖Real.tanh x-1‖≤2*Real.exp (-2*x):=by
   have hc:=Real.cosh_pos x
   have he:Real.exp x/2≤Real.cosh x:=by
     rw [Real.cosh_eq]
     linarith [Real.exp_pos (-x)]
   have hgap:1-Real.tanh x=Real.exp (-x)/Real.cosh x:=by
     rw [Real.tanh_eq_sinh_div_cosh,←Real.cosh_sub_sinh]
     field_simp
   rw [Real.norm_eq_abs,abs_sub_comm,hgap,abs_of_pos (div_pos (Real.exp_pos _) hc)]
   apply (div_le_iff₀ hc).mpr
   have hh:=mul_le_mul_of_nonneg_left he (show 0≤2*Real.exp (-2*x) by positivity)
   have he':2*Real.exp (-2*x)*(Real.exp x/2)=Real.exp (-x):=by
     calc
       2*Real.exp (-2*x)*(Real.exp x/2)=Real.exp (-2*x)*Real.exp x:=by ring
       _=Real.exp (-x):=by rw [←Real.exp_add];congr 1;ring
   rw [he'] at hh
   exact hh

 theorem negativeExp_mass_uniform_jets (J:ℕ) {ε m x:ℝ} (hε:0<ε)
     (hm:m∈Icc ε 1) (hx:0≤x):∀j≤J,
       ‖iteratedDeriv j (fun r=>Real.exp (r*(-x-Real.log 2))) m‖≤
         (1+x+Real.log 2)^J*Real.exp (-ε*x):=by
   intro j hj
   have he:(fun r=>Real.exp (r*(-x-Real.log 2)))=
       fun r=>Real.exp ((-x-Real.log 2)*r):=by funext r;rw [mul_comm]
   rw [he,iteratedDeriv_exp_const_mul,norm_mul,norm_pow,Real.norm_eq_abs,
     Real.norm_of_nonneg (Real.exp_pos _).le]
   have hl:0≤Real.log 2:=Real.log_nonneg (by norm_num)
   have hR:1≤1+x+Real.log 2:=by linarith
   have hy:|-x-Real.log 2|≤1+x+Real.log 2:=by
     rw [abs_of_nonpos (by linarith)];linarith
   apply mul_le_mul ((pow_le_pow_left₀ (abs_nonneg _) hy j).trans (pow_le_pow_right₀ hR hj))
     (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by positivity)
   have hm0:0≤m:=hε.le.trans hm.1
   nlinarith [mul_nonneg hm0 hl,mul_le_mul_of_nonneg_right hm.1 hx]

 theorem coshPower_mass_uniform_jets (J:ℕ) {m x:ℝ} (hm:0≤m) (hx:0≤x):∀j≤J,
       ‖iteratedDeriv j (fun r=>coshPower r x) m‖≤
         (1+x+Real.log 2)^J*Real.exp (m*x):=by
   intro j hj
   rw [iteratedDeriv_coshPower_mass,coshPower,norm_mul,norm_pow,Real.norm_eq_abs,
     Real.norm_of_nonneg (Real.exp_pos _).le]
   have hl:0≤Real.log 2:=Real.log_nonneg (by norm_num)
   have hR:1≤1+x+Real.log 2:=by linarith
   have hlog:|Real.log (Real.cosh x)|≤x:=by
     simpa only [Real.norm_eq_abs,abs_of_nonneg hx] using Paper.norm_logcosh_le_abs x
   have hlog':Real.log (Real.cosh x)≤x:=(le_abs_self _).trans hlog
   apply mul_le_mul ((pow_le_pow_left₀ (abs_nonneg _) (hlog.trans (by linarith)) j).trans
       (pow_le_pow_right₀ hR hj)) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog' hm))
       (Real.exp_pos _).le (by positivity)

end GeneralDepthPaper
