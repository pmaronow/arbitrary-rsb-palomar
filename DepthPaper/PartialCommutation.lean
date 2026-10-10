module

public import DepthPaper.JointMassJets
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

@[expose] public section


/-! Ordinary mixed scalar partial derivatives of genuine smooth functions commute. -/
noncomputable section
open scoped ContDiff
namespace DepthPaper

 theorem mixed_scalar_partials_commute {F:ℝ×ℝ→ℝ} (hF:ContDiff ℝ ∞ F) (m x:ℝ):
     deriv (fun y=>deriv (fun r=>F (r,y)) m) x=
       deriv (fun r=>deriv (fun y=>F (r,y)) x) m:=by
   have hd1 (r y:ℝ):deriv (fun a=>F (a,y)) r=fderiv ℝ F (r,y) (1,0):=by
     exact (((hF.differentiable (by simp) (r,y)).hasFDerivAt).comp_hasDerivAt r
       ((hasDerivAt_id r).prodMk (hasDerivAt_const r y))).deriv
   have hd2 (r y:ℝ):deriv (fun a=>F (r,a)) y=fderiv ℝ F (r,y) (0,1):=by
     exact (((hF.differentiable (by simp) (r,y)).hasFDerivAt).comp_hasDerivAt y
       ((hasDerivAt_const y r).prodMk (hasDerivAt_id y))).deriv
   simp only [hd1,hd2]
   have hdf:=((hF.fderiv_right (m:=∞) (by simp)).differentiable (by simp) (m,x)).hasFDerivAt
   have h1:HasDerivAt (fun y=>fderiv ℝ F (m,y) (1,0))
       (fderiv ℝ (fderiv ℝ F) (m,x) (0,1) (1,0)) x:=by
     convert (hdf.clm_apply (hasFDerivAt_const ((1,0):ℝ×ℝ) (m,x))).comp_hasDerivAt x
       ((hasDerivAt_const x m).prodMk (hasDerivAt_id x)) using 1 <;> first | rfl | simp [Function.comp_def]
   have h2:HasDerivAt (fun r=>fderiv ℝ F (r,x) (0,1))
       (fderiv ℝ (fderiv ℝ F) (m,x) (1,0) (0,1)) m:=by
     convert (hdf.clm_apply (hasFDerivAt_const ((0,1):ℝ×ℝ) (m,x))).comp_hasDerivAt m
       ((hasDerivAt_id m).prodMk (hasDerivAt_const m x)) using 1 <;> first | rfl | simp [Function.comp_def]
   rw [h1.deriv,h2.deriv]
   exact (hF.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

end DepthPaper
