module

public import GeneralDepthPaper.LogDeficitAlgebra

@[expose] public section


/-! Uniform polynomial bounds for every expression in the logarithmic
normalized-deficit differential algebra. -/
noncomputable section
open Set
namespace GeneralDepthPaper

 def LogDeficitExpr.physicalEval (e:LogDeficitExpr MassResidualNormalizerExpr) (m V x:ℝ):ℝ:=
   e.eval (fun a=>a.eval m V x) m (normalizedDeficit m V x)

 theorem LogDeficitExpr.polynomial_bound
     (e:LogDeficitExpr MassResidualNormalizerExpr) {ε:ℝ} (hε:0<ε):
     ∃C:ℝ,0<C ∧ ∃d:ℕ,∀m∈Icc ε 1,∀V≥1,∀x,
       ‖e.physicalEval m V x‖≤C*V^d:=by
   induction e with
   | const c=>
     refine ⟨‖c‖+1,by positivity,0,?_⟩
     intro m hm V hV x
     simp only [physicalEval,eval,pow_zero,mul_one]
     linarith
   | atom a=>
     obtain ⟨C,hC,d,ha⟩:=a.exponential_bound hε
     refine ⟨C,hC,d,?_⟩
     intro m hm V hV x
     have hexp:Real.exp (-(ε^2)*V/2)≤1:=Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ε])
     exact (ha m hm V hV x).trans
       (mul_le_mul_of_nonneg_left hexp (by positivity) |>.trans_eq (mul_one _))
   | invden=>
     refine ⟨2,by norm_num,0,?_⟩
     intro m hm V hV x
     have hb:=normalizedDeficit_bounds (hε.trans_le hm.1) hm.2 V x (zero_le_one.trans hV)
     change ‖(1-normalizedDeficit m V x)⁻¹‖≤2*V^0
     have hp:0<1-normalizedDeficit m V x:=by linarith
     rw [Real.norm_of_nonneg (inv_nonneg.mpr hp.le),pow_zero,mul_one]
     have hh:1/2≤1-normalizedDeficit m V x:=by linarith
     have hi:=inv_le_inv₀ hp (by norm_num : (0:ℝ)<1/2) |>.mpr hh
     norm_num at hi ⊢
     exact hi
   | logden=>
     refine ⟨1,by norm_num,0,?_⟩
     intro m hm V hV x
     have hb:=normalizedDeficit_bounds (hε.trans_le hm.1) hm.2 V x (zero_le_one.trans hV)
     have hh:=norm_log_one_sub_normalizedDeficit (hε.trans_le hm.1) hm.2 V x (zero_le_one.trans hV)
     rw [Real.norm_of_nonneg hb.1] at hh
     change ‖Real.log (1-normalizedDeficit m V x)‖≤1*V^0
     simp only [pow_zero,mul_one]
     linarith
   | massInv=>
     refine ⟨ε⁻¹,inv_pos.mpr hε,0,?_⟩
     intro m hm V hV x
     have hm0:=hε.trans_le hm.1
     change ‖m⁻¹‖≤ε⁻¹*V^0
     rw [Real.norm_of_nonneg (inv_nonneg.mpr hm0.le),pow_zero,mul_one]
     exact (inv_le_inv₀ hm0 hε).mpr hm.1
   | add a b ha hb=>
     obtain ⟨A,hA,d,ha⟩:=ha
     obtain ⟨B,hB,e,hb⟩:=hb
     refine ⟨A+B,add_pos hA hB,max d e,?_⟩
     intro m hm V hV x
     change ‖a.physicalEval m V x+b.physicalEval m V x‖≤_
     calc
       _≤‖a.physicalEval m V x‖+‖b.physicalEval m V x‖:=norm_add_le _ _
       _≤A*V^d+B*V^e:=add_le_add (ha m hm V hV x) (hb m hm V hV x)
       _≤A*V^(max d e)+B*V^(max d e):=add_le_add
         (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hV (le_max_left _ _)) hA.le)
         (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hV (le_max_right _ _)) hB.le)
       _=(A+B)*V^(max d e):=by ring
   | mul a b ha hb=>
     obtain ⟨A,hA,d,ha⟩:=ha
     obtain ⟨B,hB,e,hb⟩:=hb
     refine ⟨A*B,mul_pos hA hB,d+e,?_⟩
     intro m hm V hV x
     change ‖a.physicalEval m V x*b.physicalEval m V x‖≤_
     rw [norm_mul]
     have hh:=mul_le_mul (ha m hm V hV x) (hb m hm V hV x) (norm_nonneg _) (by positivity)
     exact hh.trans_eq (by rw [pow_add];ring)

end GeneralDepthPaper
