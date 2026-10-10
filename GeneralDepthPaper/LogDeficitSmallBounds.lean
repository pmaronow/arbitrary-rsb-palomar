module

public import GeneralDepthPaper.LogDeficitPolynomialBounds

@[expose] public section


/-! Every small logarithmic differential expression has the genuine uniform
exponential bound retained by its normalized-deficit factor. -/
noncomputable section
open Set
namespace GeneralDepthPaper

 theorem normalizedDeficit_exponential_bound {ε:ℝ} (hε:0<ε):
     ∃C:ℝ,0<C ∧ ∃d:ℕ,∀m∈Icc ε 1,∀V≥1,∀x,
       ‖normalizedDeficit m V x‖≤C*V^d*Real.exp (-(ε^2)*V/2):=by
   simpa only [iteratedDeriv_zero] using normalizedDeficit_mixed_exponential_bound 0 0 0 hε

 theorem LogDeficitExpr.small_exponential_bound
     (e:LogDeficitExpr MassResidualNormalizerExpr) {ε:ℝ} (hε:0<ε) (he:e.Small):
     ∃C:ℝ,0<C ∧ ∃d:ℕ,∀m∈Icc ε 1,∀V≥1,∀x,
       ‖e.physicalEval m V x‖≤C*V^d*Real.exp (-(ε^2)*V/2):=by
   revert he
   induction e with
   | const c=>
     intro he
     have hc:c=0:=he
     refine ⟨1,by norm_num,0,?_⟩
     intro m hm V hV x
     simp only [physicalEval,eval,hc,norm_zero,pow_zero,one_mul]
     exact (Real.exp_pos _).le
   | atom a=>
     intro _
     exact a.exponential_bound hε
   | invden=>intro he;exact False.elim he
   | logden=>
     intro _
     obtain ⟨C,hC,d,hδ⟩:=normalizedDeficit_exponential_bound hε
     refine ⟨2*C,by positivity,d,?_⟩
     intro m hm V hV x
     change ‖Real.log (1-normalizedDeficit m V x)‖≤_
     exact (norm_log_one_sub_normalizedDeficit (hε.trans_le hm.1) hm.2 V x
       (zero_le_one.trans hV)).trans
         (mul_le_mul_of_nonneg_left (hδ m hm V hV x) (by norm_num) |>.trans_eq (by ring))
   | massInv=>intro he;exact False.elim he
   | add a b ha hb=>
     intro he
     obtain ⟨A,hA,d,ha⟩:=ha he.1
     obtain ⟨B,hB,e,hb⟩:=hb he.2
     refine ⟨A+B,add_pos hA hB,max d e,?_⟩
     intro m hm V hV x
     change ‖a.physicalEval m V x+b.physicalEval m V x‖≤_
     calc
       _≤‖a.physicalEval m V x‖+‖b.physicalEval m V x‖:=norm_add_le _ _
       _≤A*V^d*Real.exp (-(ε^2)*V/2)+B*V^e*Real.exp (-(ε^2)*V/2):=add_le_add (ha m hm V hV x) (hb m hm V hV x)
       _≤A*V^(max d e)*Real.exp (-(ε^2)*V/2)+B*V^(max d e)*Real.exp (-(ε^2)*V/2):=add_le_add
         (mul_le_mul_of_nonneg_right
           (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hV (le_max_left _ _)) hA.le) (Real.exp_pos _).le)
         (mul_le_mul_of_nonneg_right
           (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hV (le_max_right _ _)) hB.le) (Real.exp_pos _).le)
       _=(A+B)*V^(max d e)*Real.exp (-(ε^2)*V/2):=by ring
   | mul a b ha hb=>
     intro he
     rcases he with he|he
     · obtain ⟨A,hA,d,ha⟩:=ha he
       obtain ⟨B,hB,e,hb⟩:=b.polynomial_bound hε
       refine ⟨A*B,mul_pos hA hB,d+e,?_⟩
       intro m hm V hV x
       change ‖a.physicalEval m V x*b.physicalEval m V x‖≤_
       rw [norm_mul]
       have hh:=mul_le_mul (ha m hm V hV x) (hb m hm V hV x)
         (norm_nonneg _) (by positivity)
       exact hh.trans_eq (by rw [pow_add];ring)
     · obtain ⟨A,hA,d,ha⟩:=a.polynomial_bound hε
       obtain ⟨B,hB,e,hb⟩:=hb he
       refine ⟨A*B,mul_pos hA hB,d+e,?_⟩
       intro m hm V hV x
       change ‖a.physicalEval m V x*b.physicalEval m V x‖≤_
       rw [norm_mul]
       have hh:=mul_le_mul (ha m hm V hV x) (hb m hm V hV x)
         (norm_nonneg _) (by positivity)
       exact hh.trans_eq (by rw [pow_add];ring)

end GeneralDepthPaper
