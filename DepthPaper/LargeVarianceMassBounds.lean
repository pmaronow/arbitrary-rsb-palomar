module

public import DepthPaper.LargeVarianceMassJets
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section


/-! Cancellation estimates for the actual residual mass derivatives. This
module bounds explicit derivatives, rather than assuming a family of small
mixed jets of the Cole–Hopf error. -/
noncomputable section
open Set
namespace DepthPaper

 def expMonomialDeriv (j:ℕ) (m y:ℝ):ℝ :=
   (j:ℝ)*y^(j-1)*Real.exp (m*y)+y^j*(Real.exp (m*y)*m)

 theorem hasDerivAt_expMonomial (j:ℕ) (m y:ℝ) :
     HasDerivAt (fun r=>r^j*Real.exp (m*r)) (expMonomialDeriv j m y) y := by
   have hh:=((hasDerivAt_id y).pow j).mul (((hasDerivAt_id y).const_mul m).exp)
   convert hh using 1
   · rfl
   · simp only [id_eq,Pi.pow_apply,expMonomialDeriv,one_mul,mul_one]


 theorem norm_expMonomialDeriv_le (j:ℕ) {m y x R:ℝ} (hm:m∈Icc (0:ℝ) 1)
     (hR:1≤R) (hy:|y|≤R) (hyx:y≤x) :
     ‖expMonomialDeriv j m y‖≤((j:ℝ)+1)*R^j*Real.exp (m*x) := by
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
     _≤(j:ℝ)*R^j*Real.exp (m*x)+R^j*(Real.exp (m*x)*1) := by
       gcongr
       all_goals first | exact hm.1 | exact hm.2 | exact mul_nonneg (Real.exp_pos _).le hm.1 | positivity
     _=((j:ℝ)+1)*R^j*Real.exp (m*x):=by ring

 theorem largeVarianceResidualMassJet_positive_bound (j:ℕ) {ε m x:ℝ}
     (hε:0<ε) (hεm:ε≤m) (hm1:m≤1) (hx:0≤x) :
     |largeVarianceResidualMassJet j m x|≤
       ((j:ℝ)+2)*(1+x+Real.log 2)^j*Real.exp (-ε*x) := by
   have hm:m∈Icc (0:ℝ) 1:=⟨hε.le.trans hεm,hm1⟩
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
       ((j:ℝ)+1)*R^j*Real.exp (m*x)*Real.exp (-2*x):=by
     have hh:=norm_image_sub_le_of_norm_deriv_le_segment'
       (a:=a) (b:=c) (f:=fun y=>y^j*Real.exp (m*y))
       (fun y _=>(hasDerivAt_expMonomial j m y).hasDerivWithinAt)
       (fun y hy=>norm_expMonomialDeriv_le j hm hR (habsy y ⟨hy.1,hy.2.le⟩) (hy.2.le.trans hcx)) c ⟨hac,le_rfl⟩
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
   have hfirst:((j:ℝ)+1)*R^j*Real.exp (m*x)*Real.exp (-2*x)≤
       ((j:ℝ)+1)*R^j*Real.exp (-ε*x):=by
     rw [mul_assoc,←Real.exp_add]
     apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
     have hε1:ε≤1:=hεm.trans hm1
     nlinarith [mul_le_mul_of_nonneg_right hm1 hx,mul_le_mul_of_nonneg_right hε1 hx]
   have he:largeVarianceResidualMassJet j m x=
       (a^j*Real.exp (m*a)-c^j*Real.exp (m*c))+
         (-x-Real.log 2)^j*Real.exp (m*(-x-Real.log 2)):=by
     unfold largeVarianceResidualMassJet
     dsimp only [a,c]
     ring
   have hdiff':|a^j*Real.exp (m*a)-c^j*Real.exp (m*c)|≤
       ((j:ℝ)+1)*R^j*Real.exp (m*x)*Real.exp (-2*x):=by
     simpa only [abs_sub_comm] using hdiff
   rw [he]
   calc
     _≤|a^j*Real.exp (m*a)-c^j*Real.exp (m*c)|+
         |(-x-Real.log 2)^j*Real.exp (m*(-x-Real.log 2))|:=abs_add_le _ _
     _≤((j:ℝ)+1)*R^j*Real.exp (-ε*x)+R^j*Real.exp (-ε*x):=by
       exact add_le_add (hdiff'.trans hfirst) hsecond
     _=((j:ℝ)+2)*(1+x+Real.log 2)^j*Real.exp (-ε*x):=by dsimp only [R];ring

end DepthPaper
