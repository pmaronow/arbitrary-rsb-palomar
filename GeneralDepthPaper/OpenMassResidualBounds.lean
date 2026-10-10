module

public import GeneralDepthPaper.LargeVarianceMassDecay

@[expose] public section


/-! Residual mass-jet cancellation on compact subintervals of the open mass
range (0,2). This supplies actual two-sided derivative neighborhoods at m=1. -/
noncomputable section
open Set
namespace GeneralDepthPaper

 theorem norm_expMonomialDeriv_le_two (j:ℕ) {m y x R:ℝ} (hm:m∈Icc (0:ℝ) 2)
     (hR:1≤R) (hy:|y|≤R) (hyx:y≤x) :
     ‖expMonomialDeriv j m y‖≤((j:ℝ)+2)*R^j*Real.exp (m*x) := by
   have hR0:0≤R:=zero_le_one.trans hR
   have he:Real.exp (m*y)≤Real.exp (m*x):=Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hyx hm.1)
   have hp:|y|^j≤R^j:=pow_le_pow_left₀ (abs_nonneg _) hy j
   have hp':|y|^(j-1)≤R^j:=(pow_le_pow_left₀ (abs_nonneg _) hy (j-1)).trans
     (pow_le_pow_right₀ hR (Nat.sub_le _ _))
   unfold expMonomialDeriv
   calc
     ‖(j:ℝ)*y^(j-1)*Real.exp (m*y)+y^j*(Real.exp (m*y)*m)‖
       ≤‖(j:ℝ)*y^(j-1)*Real.exp (m*y)‖+‖y^j*(Real.exp (m*y)*m)‖:=norm_add_le _ _
     _=(j:ℝ)*|y|^(j-1)*Real.exp (m*y)+|y|^j*(Real.exp (m*y)*m):=by
       simp only [norm_mul,norm_pow,Real.norm_eq_abs,abs_of_nonneg (show (0:ℝ)≤(j:ℝ) from Nat.cast_nonneg j),
         abs_of_nonneg (Real.exp_pos _).le,abs_of_nonneg hm.1]
     _≤(j:ℝ)*R^j*Real.exp (m*x)+R^j*(Real.exp (m*x)*2) := by
       gcongr
       all_goals first | exact hm.1 | exact hm.2 | exact mul_nonneg (Real.exp_pos _).le hm.1 | positivity
     _=((j:ℝ)+2)*R^j*Real.exp (m*x):=by ring

 theorem largeVarianceResidualMassJet_positive_open_bound (j:ℕ) {ε m x:ℝ}
     (hε:0<ε) (hεm:ε≤m) (hm2:m≤2-ε) (hx:0≤x) :
     |largeVarianceResidualMassJet j m x|≤
       ((j:ℝ)+3)*(1+x+Real.log 2)^j*Real.exp (-ε*x) := by
   have hm:m∈Icc (0:ℝ) 2:=⟨hε.le.trans hεm,by linarith⟩
   let a:=x-Real.log 2
   let c:=Real.log (Real.cosh x)
   let R:=1+x+Real.log 2
   have hl:0≤Real.log 2:=Real.log_nonneg (by norm_num)
   have hR:1≤R:=by dsimp only [R];linarith
   have hR0:0≤R:=zero_le_one.trans hR
   have hgap:=logCosh_positive_gap_bounds x
   have hac:a≤c:=sub_nonneg.mp hgap.1
   have hcx:c≤x:=by
     have hn:=Paper.norm_logcosh_le_abs x
     rw [Real.norm_eq_abs,abs_of_nonneg hx] at hn
     exact (le_abs_self _).trans hn
   have habsy:∀y∈Icc a c,|y|≤R:=by
     intro y hy
     apply abs_le.mpr
     dsimp only [R,a,c] at *
     constructor <;> linarith [hy.1,hy.2]
   have hdiff:|c^j*Real.exp (m*c)-a^j*Real.exp (m*a)|≤
       ((j:ℝ)+2)*R^j*Real.exp (m*x)*Real.exp (-2*x):=by
     have hh:=norm_image_sub_le_of_norm_deriv_le_segment'
       (a:=a) (b:=c) (f:=fun y=>y^j*Real.exp (m*y))
       (fun y _=>(hasDerivAt_expMonomial j m y).hasDerivWithinAt)
       (fun y hy=>norm_expMonomialDeriv_le_two j hm hR (habsy y ⟨hy.1,hy.2.le⟩) (hy.2.le.trans hcx)) c ⟨hac,le_rfl⟩
     rw [Real.norm_eq_abs] at hh
     exact hh.trans (mul_le_mul_of_nonneg_left hgap.2 (by positivity))
   have hb:|-x-Real.log 2|≤R:=by
     rw [abs_of_nonpos (by linarith)]
     dsimp only [R]
     linarith
   have hsecond:|(-x-Real.log 2)^j*Real.exp (m*(-x-Real.log 2))|≤R^j*Real.exp (-ε*x):=by
     rw [abs_mul,abs_pow,abs_of_pos (Real.exp_pos _)]
     apply mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hb j) (Real.exp_le_exp.mpr ?_)
       (Real.exp_pos _).le (pow_nonneg (zero_le_one.trans hR) _)
     nlinarith [mul_nonneg hm.1 hl,mul_le_mul_of_nonneg_right hεm hx]
   have hfirst:((j:ℝ)+2)*R^j*Real.exp (m*x)*Real.exp (-2*x)≤
       ((j:ℝ)+2)*R^j*Real.exp (-ε*x):=by
     rw [mul_assoc,←Real.exp_add]
     apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
     nlinarith [mul_le_mul_of_nonneg_right hm2 hx]
   have he:largeVarianceResidualMassJet j m x=
       (a^j*Real.exp (m*a)-c^j*Real.exp (m*c))+
         (-x-Real.log 2)^j*Real.exp (m*(-x-Real.log 2)):=by
     unfold largeVarianceResidualMassJet
     dsimp only [a,c]
     ring
   have hdiff':|a^j*Real.exp (m*a)-c^j*Real.exp (m*c)|≤
       ((j:ℝ)+2)*R^j*Real.exp (m*x)*Real.exp (-2*x):=by
     simpa only [abs_sub_comm] using hdiff
   rw [he]
   calc
     _≤|a^j*Real.exp (m*a)-c^j*Real.exp (m*c)|+
         |(-x-Real.log 2)^j*Real.exp (m*(-x-Real.log 2))|:=abs_add_le _ _
     _≤((j:ℝ)+2)*R^j*Real.exp (-ε*x)+R^j*Real.exp (-ε*x):=by
       exact add_le_add (hdiff'.trans hfirst) hsecond
     _=((j:ℝ)+3)*(1+x+Real.log 2)^j*Real.exp (-ε*x):=by dsimp only [R];ring


 def largeVarianceOpenMassDecayConstant (ε:ℝ) (j:ℕ):ℝ :=
   ((j:ℝ)+3)*((j.factorial:ℝ)/(ε/2)^j)*Real.exp ((ε/2)*(1+Real.log 2))

 theorem largeVarianceOpenMassDecayConstant_pos {ε:ℝ} (hε:0<ε) (j:ℕ) :
     0<largeVarianceOpenMassDecayConstant ε j := by
   unfold largeVarianceOpenMassDecayConstant
   have hf:0<(j.factorial:ℝ):=by exact_mod_cast Nat.factorial_pos j
   positivity

 theorem largeVarianceResidualMassJet_open_decay (j:ℕ) {ε m:ℝ} (hε:0<ε) (hεm:ε≤m)
     (hm1:m≤2-ε) (x:ℝ) :
     |largeVarianceResidualMassJet j m x|≤
       largeVarianceOpenMassDecayConstant ε j*Real.exp (-(ε/2)*|x|) := by
   have hbound:|largeVarianceResidualMassJet j m x|≤
       ((j:ℝ)+3)*(1+|x|+Real.log 2)^j*Real.exp (-ε*|x|):=by
     rcases le_total 0 x with hx|hx
     · simpa only [abs_of_nonneg hx] using largeVarianceResidualMassJet_positive_open_bound j hε hεm hm1 hx
     · have hn:=largeVarianceResidualMassJet_positive_open_bound j hε hεm hm1 (neg_nonneg.mpr hx)
       simpa only [largeVarianceResidualMassJet_even,abs_of_nonpos hx] using hn
   have hpoly:=polynomial_times_exp_bound j (ε:=ε/2) (c:=1+Real.log 2) (u:=|x|)
     (by positivity) (by have hl:=Real.log_nonneg (by norm_num : (1:ℝ)≤2);linarith) (abs_nonneg x)
   have he:Real.exp (-ε*|x|)=Real.exp (-(ε/2)*|x|)*Real.exp (-(ε/2)*|x|):=by
     rw [←Real.exp_add];congr 1;ring
   apply hbound.trans
   rw [he]
   unfold largeVarianceOpenMassDecayConstant
   have hm:=mul_le_mul_of_nonneg_right
     (mul_le_mul_of_nonneg_left hpoly (by positivity : (0:ℝ)≤(j:ℝ)+3))
     (Real.exp_pos (-(ε/2)*|x|)).le
   convert hm using 1 <;> ring

 theorem iteratedDeriv_largeVarianceResidual_mass_open_decay (j:ℕ) {ε m:ℝ} (hε:0<ε)
     (hεm:ε≤m) (hm1:m≤2-ε) (x:ℝ) :
     ‖iteratedDeriv j (fun r=>largeVarianceResidual r x) m‖≤
       largeVarianceOpenMassDecayConstant ε j*Real.exp (-(ε/2)*|x|) := by
   rw [iteratedDeriv_largeVarianceResidual_mass,Real.norm_eq_abs]
   exact largeVarianceResidualMassJet_open_decay j hε hεm hm1 x

end GeneralDepthPaper
