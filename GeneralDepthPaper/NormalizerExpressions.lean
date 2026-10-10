module

public import GeneralDepthPaper.ResidualHeatMixedBounds

@[expose] public section


/-! A concrete differential algebra for the large-variance normalizing factor.
Expressions are built from mass, variance, space and tanh(mass*space), with
actual derivatives and polynomial growth bounds proved by induction. -/
noncomputable section
open Set
namespace GeneralDepthPaper

 inductive NormalizerExpr where
 | const (c:ℝ)
 | mass
 | variance
 | space
 | tangent
 | add (a b:NormalizerExpr)
 | mul (a b:NormalizerExpr)

 def NormalizerExpr.eval : NormalizerExpr→ℝ→ℝ→ℝ→ℝ
 | .const c,_,_,_=>c
 | .mass,m,_,_=>m
 | .variance,_,V,_=>V
 | .space,_,_,x=>x
 | .tangent,m,_,x=>Real.tanh (m*x)
 | .add a b,m,V,x=>a.eval m V x+b.eval m V x
 | .mul a b,m,V,x=>a.eval m V x*b.eval m V x

 def NormalizerExpr.dx : NormalizerExpr→NormalizerExpr
 | .const _=>.const 0
 | .mass=>.const 0
 | .variance=>.const 0
 | .space=>.const 1
 | .tangent=>.mul .mass (.add (.const 1) (.mul (.const (-1)) (.mul .tangent .tangent)))
 | .add a b=>.add a.dx b.dx
 | .mul a b=>.add (.mul a.dx b) (.mul a b.dx)

 def NormalizerExpr.dm : NormalizerExpr→NormalizerExpr
 | .const _=>.const 0
 | .mass=>.const 1
 | .variance=>.const 0
 | .space=>.const 0
 | .tangent=>.mul .space (.add (.const 1) (.mul (.const (-1)) (.mul .tangent .tangent)))
 | .add a b=>.add a.dm b.dm
 | .mul a b=>.add (.mul a.dm b) (.mul a b.dm)

 def NormalizerExpr.dV : NormalizerExpr→NormalizerExpr
 | .const _=>.const 0
 | .mass=>.const 0
 | .variance=>.const 1
 | .space=>.const 0
 | .tangent=>.const 0
 | .add a b=>.add a.dV b.dV
 | .mul a b=>.add (.mul a.dV b) (.mul a b.dV)

 theorem NormalizerExpr.hasDerivAt_space (e:NormalizerExpr) (m V x:ℝ):
     HasDerivAt (fun y=>e.eval m V y) (e.dx.eval m V x) x:=by
   induction e with
   | const c=>exact hasDerivAt_const x c
   | mass=>exact hasDerivAt_const x m
   | variance=>exact hasDerivAt_const x V
   | space=>exact hasDerivAt_id x
   | tangent=>
     have hh:=(Paper.hasDerivAt_tanh (m*x)).comp x ((hasDerivAt_id x).const_mul m)
     have hs:Paper.sech (m*x)^2=1-Real.tanh (m*x)^2:=by nlinarith [Paper.tanh_sq_add_sech_sq (m*x)]
     rw [hs] at hh
     convert hh using 1
     · rfl
     · simp only [dx,eval,id_eq];ring
   | add a b ha hb=>exact ha.add hb
   | mul a b ha hb=>exact ha.mul hb

 theorem NormalizerExpr.hasDerivAt_mass (e:NormalizerExpr) (m V x:ℝ):
     HasDerivAt (fun r=>e.eval r V x) (e.dm.eval m V x) m:=by
   induction e with
   | const c=>exact hasDerivAt_const m c
   | mass=>exact hasDerivAt_id m
   | variance=>exact hasDerivAt_const m V
   | space=>exact hasDerivAt_const m x
   | tangent=>
     have hh:=(Paper.hasDerivAt_tanh (m*x)).comp m ((hasDerivAt_id m).mul_const x)
     have hs:Paper.sech (m*x)^2=1-Real.tanh (m*x)^2:=by nlinarith [Paper.tanh_sq_add_sech_sq (m*x)]
     rw [hs] at hh
     convert hh using 1
     · rfl
     · simp only [dm,eval,id_eq];ring
   | add a b ha hb=>exact ha.add hb
   | mul a b ha hb=>exact ha.mul hb

 theorem NormalizerExpr.hasDerivAt_variance (e:NormalizerExpr) (m V x:ℝ):
     HasDerivAt (fun v=>e.eval m v x) (e.dV.eval m V x) V:=by
   induction e with
   | const c=>exact hasDerivAt_const V c
   | mass=>exact hasDerivAt_const V m
   | variance=>exact hasDerivAt_id V
   | space=>exact hasDerivAt_const V x
   | tangent=>exact hasDerivAt_const V (Real.tanh (m*x))
   | add a b ha hb=>exact ha.add hb
   | mul a b ha hb=>exact ha.mul hb

 theorem NormalizerExpr.polynomial_bound (e:NormalizerExpr):
     ∃C:ℝ,1≤C ∧ ∃d:ℕ,∀m∈Icc (0:ℝ) 1,∀V≥1,∀x,
       ‖e.eval m V x‖≤C*V^d*(1+|x|)^d:=by
   induction e with
   | const c=>refine ⟨max ‖c‖ 1,le_max_right _ _,0,?_⟩;intro m hm V hV x;simp only [eval,pow_zero,mul_one];exact le_max_left _ _
   | mass=>refine ⟨1,le_rfl,0,?_⟩;intro m hm V hV x;simp only [eval,pow_zero,mul_one,Real.norm_of_nonneg hm.1];exact hm.2
   | variance=>refine ⟨1,le_rfl,1,?_⟩;intro m hm V hV x;simp only [eval,pow_one,one_mul,Real.norm_of_nonneg (zero_le_one.trans hV)];nlinarith [abs_nonneg x]
   | space=>refine ⟨1,le_rfl,1,?_⟩;intro m hm V hV x;simp only [eval,pow_one,one_mul,Real.norm_eq_abs];nlinarith [abs_nonneg x]
   | tangent=>refine ⟨1,le_rfl,0,?_⟩;intro m hm V hV x;simp only [eval,pow_zero,mul_one,Real.norm_eq_abs];exact (Real.abs_tanh_lt_one _).le
   | add a b ha hb=>
     obtain ⟨Ca,hCa,da,ha⟩:=ha
     obtain ⟨Cb,hCb,db,hb⟩:=hb
     refine ⟨Ca+Cb,by linarith,max da db,?_⟩
     intro m hm V hV x
     have hR:1≤1+|x|:=by linarith [abs_nonneg x]
     have ha':Ca*V^da*(1+|x|)^da≤Ca*V^(max da db)*(1+|x|)^(max da db):=by
       gcongr
       · exact le_max_left _ _
       · exact le_max_left _ _
     have hb':Cb*V^db*(1+|x|)^db≤Cb*V^(max da db)*(1+|x|)^(max da db):=by
       gcongr
       · exact le_max_right _ _
       · exact le_max_right _ _
     change ‖a.eval m V x+b.eval m V x‖≤_
     exact (norm_add_le _ _).trans ((add_le_add ((ha m hm V hV x).trans ha')
       ((hb m hm V hV x).trans hb')).trans_eq (by ring))
   | mul a b ha hb=>
     obtain ⟨Ca,hCa,da,ha⟩:=ha
     obtain ⟨Cb,hCb,db,hb⟩:=hb
     refine ⟨Ca*Cb,by nlinarith [mul_le_mul_of_nonneg_left hCb (zero_le_one.trans hCa)],da+db,?_⟩
     intro m hm V hV x
     simp only [eval,norm_mul]
     have hh:=mul_le_mul (ha m hm V hV x) (hb m hm V hV x) (norm_nonneg _)
       (show 0≤Ca*V^da*(1+|x|)^da by positivity)
     convert hh using 1 <;> rw [pow_add,pow_add] <;> ring

end GeneralDepthPaper
