module

public import GeneralDepthPaper.NormalizerExpressions

@[expose] public section


/-! Actual derivatives of the reciprocal leading Gaussian moment. -/
noncomputable section
open Set
open scoped NNReal
namespace GeneralDepthPaper

 def normalizerInverse (m V x:ℝ):ℝ :=
   Real.exp ((m-1)*Real.log 2-V*m^2/2)/Real.cosh (m*x)

 theorem hasDerivAt_normalizerInverse_space (m V x:ℝ):
     HasDerivAt (normalizerInverse m V) (normalizerInverse m V x*(-m*Real.tanh (m*x))) x:=by
   have hd:=(Real.hasDerivAt_cosh (m*x)).comp x ((hasDerivAt_id x).const_mul m)
   have hh:=(hasDerivAt_const x (Real.exp ((m-1)*Real.log 2-V*m^2/2))).div hd (Real.cosh_pos _).ne'
   convert hh using 1
   · rfl
   · simp only [normalizerInverse,Real.tanh_eq_sinh_div_cosh,id_eq,mul_one,one_mul,Function.comp_apply,Pi.sub_apply,Pi.pow_apply]
     field_simp [(Real.cosh_pos (m*x)).ne'] <;> ring

 theorem hasDerivAt_normalizerInverse_mass (m V x:ℝ):
     HasDerivAt (fun r=>normalizerInverse r V x)
       (normalizerInverse m V x*(Real.log 2-V*m-x*Real.tanh (m*x))) m:=by
   have hn:=(((hasDerivAt_id m).sub_const 1).mul_const (Real.log 2) |>.sub
     (((hasDerivAt_id m).pow 2).const_mul V |>.div_const 2)).exp
   have hd:=(Real.hasDerivAt_cosh (m*x)).comp m ((hasDerivAt_id m).mul_const x)
   have hh:=hn.div hd (Real.cosh_pos _).ne'
   convert hh using 1
   · rfl
   · simp only [normalizerInverse,Real.tanh_eq_sinh_div_cosh,id_eq,pow_one,mul_one,one_mul,Function.comp_apply,Pi.sub_apply,Pi.pow_apply,Nat.reduceSub,Nat.cast_ofNat]
     field_simp [(Real.cosh_pos (m*x)).ne'] <;> ring

 theorem hasDerivAt_normalizerInverse_variance (m V x:ℝ):
     HasDerivAt (fun v=>normalizerInverse m v x) (normalizerInverse m V x*(-m^2/2)) V:=by
   have hn:=((hasDerivAt_const V ((m-1)*Real.log 2)).sub
     (((hasDerivAt_id V).mul_const (m^2)).div_const 2)).exp.div_const (Real.cosh (m*x))
   convert hn using 1
   · rfl
   · simp only [normalizerInverse,id_eq,mul_one,one_mul,Function.comp_apply,Pi.sub_apply,Pi.pow_apply]
     ring

 def normalizerSpaceGenerator:NormalizerExpr:=.mul (.const (-1)) (.mul .mass .tangent)
 def normalizerMassGenerator:NormalizerExpr:=.add (.const (Real.log 2))
   (.add (.mul (.const (-1)) (.mul .variance .mass)) (.mul (.const (-1)) (.mul .space .tangent)))
 def normalizerVarianceGenerator:NormalizerExpr:=.mul (.const (-1/2)) (.mul .mass .mass)

 def NormalizerExpr.weightedEval (e:NormalizerExpr) (m V x:ℝ):ℝ:=e.eval m V x*normalizerInverse m V x
 def NormalizerExpr.weightedDx (e:NormalizerExpr):NormalizerExpr:=.add e.dx (.mul e normalizerSpaceGenerator)
 def NormalizerExpr.weightedDm (e:NormalizerExpr):NormalizerExpr:=.add e.dm (.mul e normalizerMassGenerator)
 def NormalizerExpr.weightedDV (e:NormalizerExpr):NormalizerExpr:=.add e.dV (.mul e normalizerVarianceGenerator)

 theorem NormalizerExpr.hasDerivAt_weightedEval_space (e:NormalizerExpr) (m V x:ℝ):
     HasDerivAt (e.weightedEval m V) (e.weightedDx.weightedEval m V x) x:=by
   have hh:=(e.hasDerivAt_space m V x).mul (hasDerivAt_normalizerInverse_space m V x)
   convert hh using 1
   · rfl
   · simp only [weightedEval,weightedDx,eval,normalizerSpaceGenerator]
     ring

 theorem NormalizerExpr.hasDerivAt_weightedEval_mass (e:NormalizerExpr) (m V x:ℝ):
     HasDerivAt (fun r=>e.weightedEval r V x) (e.weightedDm.weightedEval m V x) m:=by
   have hh:=(e.hasDerivAt_mass m V x).mul (hasDerivAt_normalizerInverse_mass m V x)
   convert hh using 1
   · rfl
   · simp only [weightedEval,weightedDm,eval,normalizerMassGenerator]
     ring

 theorem NormalizerExpr.hasDerivAt_weightedEval_variance (e:NormalizerExpr) (m V x:ℝ):
     HasDerivAt (fun v=>e.weightedEval m v x) (e.weightedDV.weightedEval m V x) V:=by
   have hh:=(e.hasDerivAt_variance m V x).mul (hasDerivAt_normalizerInverse_variance m V x)
   convert hh using 1
   · rfl
   · simp only [weightedEval,weightedDV,eval,normalizerVarianceGenerator]
     ring

 theorem normalizerInverse_eq_inv_main (m:ℝ) (V:ℝ≥0) (x:ℝ):
     normalizerInverse m V x=(largeVarianceMain m V x)⁻¹:=by
   unfold normalizerInverse largeVarianceMain
   have he:(m-1)*Real.log 2-(V:ℝ)*m^2/2=-((1-m)*Real.log 2+(V:ℝ)*m^2/2):=by ring
   rw [he,Real.exp_neg,mul_inv_rev]
   ring

end GeneralDepthPaper
