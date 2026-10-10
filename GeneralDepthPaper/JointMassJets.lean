module

public import GeneralDepthPaper.ResidualMixedDecay
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section


/-! Actual mass derivatives retain joint smoothness; in particular their
spatial sections are measurable continuous functions for Gaussian integration. -/
noncomputable section
open scoped ContDiff
namespace GeneralDepthPaper

 def jointMassJet (F:ℝ×ℝ→ℝ) (j:ℕ) (p:ℝ×ℝ):ℝ :=
   iteratedDeriv j (fun m=>F (m,p.2)) p.1

 theorem contDiff_jointMassJet {F:ℝ×ℝ→ℝ} (hF:ContDiff ℝ ∞ F) (j:ℕ):
     ContDiff ℝ ∞ (jointMassJet F j):=by
   induction j with
   | zero=>
     change ContDiff ℝ ∞ (fun p:ℝ×ℝ=>F (p.1,p.2))
     simpa only [Prod.mk.eta] using hF
   | succ j ih=>
     have hd (m x:ℝ):HasDerivAt (fun r=>jointMassJet F j (r,x))
         (fderiv ℝ (jointMassJet F j) (m,x) (1,0)) m:=by
       exact ((ih.differentiable (by simp)) (m,x)).hasFDerivAt.comp_hasDerivAt m
         ((hasDerivAt_id m).prodMk (hasDerivAt_const m x))
     have he:jointMassJet F (j+1)=fun p=>fderiv ℝ (jointMassJet F j) p (1,0):=by
       funext p
       unfold jointMassJet
       rw [iteratedDeriv_succ]
       exact (hd p.1 p.2).deriv
     rw [he]
     exact (ih.contDiff_fderiv_apply (m:=∞) (by simp)).comp
       (contDiff_id.prodMk (contDiff_const (c:=(1,0))))

 theorem contDiff_coshPower_joint:ContDiff ℝ ∞ (fun p:ℝ×ℝ=>coshPower p.1 p.2):=by
   unfold coshPower
   exact (contDiff_fst.mul ((Real.contDiff_cosh.comp contDiff_snd).log
     (fun p=>(Real.cosh_pos p.2).ne'))).exp

 theorem contDiff_bivariateValue (P:Polynomial (Polynomial ℝ)):
     ContDiff ℝ ∞ (fun p:ℝ×ℝ=>bivariateValue P p.1 p.2):=by
   have he:(fun p:ℝ×ℝ=>bivariateValue P p.1 p.2)=fun p=>bivariateMassJet P 0 p.1 p.2:=by
     funext p;simp [bivariateValue_sum,bivariateMassJet]
   rw [he]
   exact contDiff_bivariateMassJet P 0

 theorem contDiff_residualSpatial_joint (i:ℕ):
     ContDiff ℝ ∞ (fun p:ℝ×ℝ=>largeVarianceResidualSpatialJet i p.1 p.2):=by
   have ht:ContDiff ℝ ∞ Real.tanh:=by
     have he:Real.tanh=(fun x=>Real.sinh x/Real.cosh x):=funext Real.tanh_eq_sinh_div_cosh
     rw [he]
     exact Real.contDiff_sinh.div Real.contDiff_cosh (fun x=>(Real.cosh_pos x).ne')
   have hq:ContDiff ℝ ∞ (fun p:ℝ×ℝ=>bivariateValue (coshPowerPolynomial i) p.1 (Real.tanh p.2)):=
     (contDiff_bivariateValue _).comp (contDiff_fst.prodMk (ht.comp contDiff_snd))
   unfold largeVarianceResidualSpatialJet coshPowerSpatialJet coshPowerPolynomialAt
   exact (((contDiff_fst.pow i).mul
     (contDiff_fst.mul (contDiff_snd.sub contDiff_const)).exp).add
       ((contDiff_fst.neg.pow i).mul
         (contDiff_fst.mul (contDiff_snd.neg.sub contDiff_const)).exp)).sub
           (hq.mul contDiff_coshPower_joint)

 theorem contDiff_residualSpatialMass_joint (i j:ℕ):
     ContDiff ℝ ∞ (fun p:ℝ×ℝ=>
       iteratedDeriv j (fun r=>largeVarianceResidualSpatialJet i r p.2) p.1):=
   contDiff_jointMassJet (contDiff_residualSpatial_joint i) j

end GeneralDepthPaper
