module

public import GeneralDepthPaper.NormalizerDifferentialAlgebra

@[expose] public section


/-! All mixed derivatives of the reciprocal leading moment have an explicit
polynomial variance factor and uniform exponential decay. -/
noncomputable section
open Set
namespace GeneralDepthPaper

 theorem inverseCosh_exponential_bound (y:ℝ):
     ‖(Real.cosh y)⁻¹‖≤2*Real.exp (-|y|):=by
   have hc:=Real.cosh_pos y
   have hlo:Real.exp |y|/2≤Real.cosh y:=by
     rw [←Real.cosh_abs,Real.cosh_eq]
     linarith [Real.exp_pos (-|y|)]
   rw [Real.norm_of_nonneg (inv_nonneg.mpr hc.le),←one_div]
   apply (div_le_iff₀ hc).mpr
   have hh:=mul_le_mul_of_nonneg_left hlo (show 0≤2*Real.exp (-|y|) by positivity)
   have he:2*Real.exp (-|y|)*(Real.exp |y|/2)=1:=by
     calc
       _=Real.exp (-|y|)*Real.exp |y|:=by ring
       _=1:=by rw [←Real.exp_add,neg_add_cancel,Real.exp_zero]
   rwa [he] at hh

 theorem normalizerInverse_decay {ε m V:ℝ} (hε:0<ε) (hm:m∈Icc ε 1) (hV:1≤V) (x:ℝ):
     ‖normalizerInverse m V x‖≤2*Real.exp (-(ε^2)*V/2)*Real.exp (-ε*|x|):=by
   have hm0:0≤m:=hε.le.trans hm.1
   have hV0:0≤V:=zero_le_one.trans hV
   have hlog:0≤Real.log 2:=Real.log_nonneg (by norm_num)
   have hs:ε^2≤m^2:=by nlinarith [hm.1]
   have he:Real.exp ((m-1)*Real.log 2-V*m^2/2)≤Real.exp (-(ε^2)*V/2):=by
     apply Real.exp_le_exp.mpr
     nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hm.2) hlog,
       mul_le_mul_of_nonneg_left hs hV0]
   have hx:Real.exp (-|m*x|)≤Real.exp (-ε*|x|):=by
     rw [abs_mul,abs_of_nonneg hm0]
     exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hm.1 (abs_nonneg x)])
   unfold normalizerInverse
   rw [div_eq_mul_inv,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
   have hcosh:‖(Real.cosh (m*x))⁻¹‖≤2*Real.exp (-ε*|x|):=
     (inverseCosh_exponential_bound _).trans (mul_le_mul_of_nonneg_left hx (by norm_num))
   have hh:=mul_le_mul he hcosh (norm_nonneg _) (Real.exp_pos _).le
   exact hh.trans_eq (by ring)

 theorem NormalizerExpr.weighted_exponential_bound (e:NormalizerExpr) {ε:ℝ} (hε:0<ε):
     ∃C:ℝ,0<C ∧ ∃d:ℕ,∀m∈Icc ε 1,∀V≥1,∀x,
       ‖e.weightedEval m V x‖≤C*V^d*Real.exp (-(ε^2)*V/2):=by
   obtain ⟨C,hC,d,hbound⟩:=e.polynomial_bound
   let A:ℝ:=(d.factorial:ℝ)/ε^d*Real.exp ε
   have hA:0<A:=by
     dsimp only [A]
     have hf:0<(d.factorial:ℝ):=by exact_mod_cast Nat.factorial_pos d
     positivity
   refine ⟨2*C*A,by positivity,d,?_⟩
   intro m hm V hV x
   have hm':m∈Icc (0:ℝ) 1:=⟨hε.le.trans hm.1,hm.2⟩
   have hp:(1+|x|)^d*Real.exp (-ε*|x|)≤A:=by
     simpa only [mul_one] using polynomial_times_exp_bound d hε (by norm_num : (0:ℝ)≤1) (abs_nonneg x)
   unfold weightedEval
   rw [norm_mul]
   have hh:=mul_le_mul (hbound m hm' V hV x) (normalizerInverse_decay hε hm hV x)
     (norm_nonneg _) (show 0≤C*V^d*(1+|x|)^d by positivity)
   calc
     ‖e.eval m V x‖*‖normalizerInverse m V x‖
       ≤(2*C*V^d*Real.exp (-(ε^2)*V/2))*((1+|x|)^d*Real.exp (-ε*|x|)):=hh.trans_eq (by ring)
     _≤(2*C*V^d*Real.exp (-(ε^2)*V/2))*A:=
       mul_le_mul_of_nonneg_left hp (by positivity)
     _=(2*C*A)*V^d*Real.exp (-(ε^2)*V/2):=by ring

 theorem NormalizerExpr.iteratedDeriv_weightedEval_space (e:NormalizerExpr) (i:ℕ) (m V x:ℝ):
     iteratedDeriv i (e.weightedEval m V) x=(weightedDx^[i] e).weightedEval m V x:=by
   induction i generalizing x with
   | zero=>simp
   | succ i ih=>
     rw [iteratedDeriv_succ]
     have he:iteratedDeriv i (e.weightedEval m V)=(weightedDx^[i] e).weightedEval m V:=funext ih
     rw [he]
     simpa only [Function.iterate_succ_apply'] using
       ((weightedDx^[i] e).hasDerivAt_weightedEval_space m V x).deriv

 theorem NormalizerExpr.iteratedDeriv_weightedEval_mass (e:NormalizerExpr) (j:ℕ) (m V x:ℝ):
     iteratedDeriv j (fun r=>e.weightedEval r V x) m=(weightedDm^[j] e).weightedEval m V x:=by
   induction j generalizing m with
   | zero=>simp
   | succ j ih=>
     rw [iteratedDeriv_succ]
     have he:iteratedDeriv j (fun r=>e.weightedEval r V x)=
       fun r=>(weightedDm^[j] e).weightedEval r V x:=funext ih
     rw [he]
     simpa only [Function.iterate_succ_apply'] using
       ((weightedDm^[j] e).hasDerivAt_weightedEval_mass m V x).deriv

 theorem NormalizerExpr.iteratedDeriv_weightedEval_variance (e:NormalizerExpr) (k:ℕ) (m V x:ℝ):
     iteratedDeriv k (fun v=>e.weightedEval m v x) V=(weightedDV^[k] e).weightedEval m V x:=by
   induction k generalizing V with
   | zero=>simp
   | succ k ih=>
     rw [iteratedDeriv_succ]
     have he:iteratedDeriv k (fun v=>e.weightedEval m v x)=
       fun v=>(weightedDV^[k] e).weightedEval m v x:=funext ih
     rw [he]
     simpa only [Function.iterate_succ_apply'] using
       ((weightedDV^[k] e).hasDerivAt_weightedEval_variance m V x).deriv

 theorem normalizerInverse_mixed_exponential_bound (i j k:ℕ) {ε:ℝ} (hε:0<ε):
     ∃C:ℝ,0<C ∧ ∃d:ℕ,∀m∈Icc ε 1,∀V≥1,∀x,
       ‖iteratedDeriv j (fun r=>iteratedDeriv k
         (fun v=>iteratedDeriv i (normalizerInverse r v) x) V) m‖≤
           C*V^d*Real.exp (-(ε^2)*V/2):=by
   let e:NormalizerExpr:=NormalizerExpr.weightedDm^[j]
     (NormalizerExpr.weightedDV^[k] (NormalizerExpr.weightedDx^[i] (.const 1)))
   have he:(fun m V x=>iteratedDeriv j (fun r=>iteratedDeriv k
       (fun v=>iteratedDeriv i (normalizerInverse r v) x) V) m)=e.weightedEval:=by
     funext m V x
     have hbase:normalizerInverse=(NormalizerExpr.const 1).weightedEval:=by
       funext m V x;simp [NormalizerExpr.weightedEval,NormalizerExpr.eval]
     rw [hbase]
     simp only [NormalizerExpr.iteratedDeriv_weightedEval_space,
       NormalizerExpr.iteratedDeriv_weightedEval_variance,NormalizerExpr.iteratedDeriv_weightedEval_mass,e]
   obtain ⟨C,hC,d,hbound⟩:=e.weighted_exponential_bound hε
   refine ⟨C,hC,d,?_⟩
   intro m hm V hV x
   have hep:=congrFun (congrFun (congrFun he m) V) x
   rw [hep]
   exact hbound m hm V hV x

end GeneralDepthPaper
