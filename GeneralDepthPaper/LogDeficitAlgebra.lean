module

public import GeneralDepthPaper.NormalizedDeficitIdentity

@[expose] public section


/-! A finite algebra for derivatives of log(1-deficit)/mass. Every logarithmic
expression keeps an actual small deficit factor under differentiation. -/
noncomputable section
namespace GeneralDepthPaper

 inductive LogDeficitExpr (α:Type) where
 | const (c:ℝ)
 | atom (a:α)
 | invden
 | logden
 | massInv
 | add (a b:LogDeficitExpr α)
 | mul (a b:LogDeficitExpr α)

 def LogDeficitExpr.eval {α:Type} (A:α→ℝ) (m z:ℝ):LogDeficitExpr α→ℝ
 | .const c=>c
 | .atom a=>A a
 | .invden=>(1-z)⁻¹
 | .logden=>Real.log (1-z)
 | .massInv=>m⁻¹
 | .add a b=>a.eval A m z+b.eval A m z
 | .mul a b=>a.eval A m z*b.eval A m z

 def LogDeficitExpr.map {α γ:Type} (f:α→γ):LogDeficitExpr α→LogDeficitExpr γ
 | .const c=>.const c
 | .atom a=>.atom (f a)
 | .invden=>.invden
 | .logden=>.logden
 | .massInv=>.massInv
 | .add a b=>.add (a.map f) (b.map f)
 | .mul a b=>.mul (a.map f) (b.map f)

 theorem LogDeficitExpr.eval_map {α γ:Type} (e:LogDeficitExpr α) (f:α→γ)
     (A:γ→ℝ) (m z:ℝ):
     (e.map f).eval A m z=e.eval (A ∘ f) m z:=by
   induction e <;> simp_all only [map,eval,Function.comp_apply]

 def LogDeficitExpr.differentiate {α:Type} (da:α→α) (dz:α) (dm:ℝ):
     LogDeficitExpr α→LogDeficitExpr α
 | .const _=>.const 0
 | .atom a=>.atom (da a)
 | .invden=>.mul (.atom dz) (.mul .invden .invden)
 | .logden=>.mul (.const (-1)) (.mul (.atom dz) .invden)
 | .massInv=>.mul (.const (-dm)) (.mul .massInv .massInv)
 | .add a b=>.add (a.differentiate da dz dm) (b.differentiate da dz dm)
 | .mul a b=>.add (.mul (a.differentiate da dz dm) b) (.mul a (b.differentiate da dz dm))

 def LogDeficitExpr.Small {α:Type}:LogDeficitExpr α→Prop
 | .const c=>c=0
 | .atom _=>True
 | .invden=>False
 | .logden=>True
 | .massInv=>False
 | .add a b=>a.Small ∧ b.Small
 | .mul a b=>a.Small ∨ b.Small

 theorem LogDeficitExpr.small_map {α γ:Type} (e:LogDeficitExpr α) (f:α→γ):
     (e.map f).Small↔e.Small:=by
   induction e <;> simp_all only [map,Small]

 theorem LogDeficitExpr.small_differentiate {α:Type} (e:LogDeficitExpr α)
     (da:α→α) (dz:α) (dm:ℝ) (he:e.Small):
     (e.differentiate da dz dm).Small:=by
   induction e <;> simp_all only [differentiate,Small] <;> tauto

 theorem LogDeficitExpr.hasDerivAt_eval {α:Type} (e:LogDeficitExpr α)
     (A:α→ℝ→ℝ) (M Z:ℝ→ℝ) (da:α→α) (dz:α) (dm t:ℝ)
     (hA:∀a,HasDerivAt (A a) (A (da a) t) t)
     (hM:HasDerivAt M dm t) (hZ:HasDerivAt Z (A dz t) t)
     (hm:M t≠0) (hz:1-Z t≠0):
     HasDerivAt (fun r=>e.eval (fun a=>A a r) (M r) (Z r))
       ((e.differentiate da dz dm).eval (fun a=>A a t) (M t) (Z t)) t:=by
   induction e with
   | const c=>exact hasDerivAt_const t c
   | atom a=>exact hA a
   | invden=>
     have hd:=((hasDerivAt_const t 1).sub hZ).inv hz
     convert hd using 1
     · rfl
     · simp only [differentiate,eval,Pi.sub_apply]
       field_simp [hz,hm] <;> ring
   | logden=>
     have hd:=((hasDerivAt_const t 1).sub hZ).log hz
     convert hd using 1
     · rfl
     · simp only [differentiate,eval,Pi.sub_apply]
       ring
   | massInv=>
     have hd:=hM.inv hm
     convert hd using 1
     · rfl
     · simp only [differentiate,eval,Pi.sub_apply]
       field_simp [hz,hm] <;> ring
   | add a b ha hb=>exact ha.add hb
   | mul a b ha hb=>exact ha.mul hb

end GeneralDepthPaper
