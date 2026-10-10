module

public import DepthPaper.PartialCommutation
public import DepthPaper.ResidualHeatSectionSmooth

@[expose] public section


/-! Actual mass and spatial residual derivatives commute at every order. -/
noncomputable section
open scoped ContDiff
namespace DepthPaper
set_option maxHeartbeats 1000000

 theorem hasDerivAt_residualSpatialMass_space (i j:ℕ) (m x:ℝ):
     HasDerivAt (fun y=>iteratedDeriv j (fun r=>largeVarianceResidualSpatialJet i r y) m)
       (iteratedDeriv j (fun r=>largeVarianceResidualSpatialJet (i+1) r x) m) x:=by
   induction j generalizing m x with
   | zero=>simpa only [iteratedDeriv_zero] using hasDerivAt_largeVarianceResidualSpatialJet i m x
   | succ j ih=>
     let F:ℝ×ℝ→ℝ:=fun p=>iteratedDeriv j (fun r=>largeVarianceResidualSpatialJet i r p.2) p.1
     have hF:ContDiff ℝ ∞ F:=contDiff_residualSpatialMass_joint i j
     have hdM (r y:ℝ):deriv (fun a=>F (a,y)) r=
         iteratedDeriv (j+1) (fun a=>largeVarianceResidualSpatialJet i a y) r:=by
       exact (congrFun (iteratedDeriv_succ (n:=j) (f:=fun a=>largeVarianceResidualSpatialJet i a y)) r).symm
     have hdX (r y:ℝ):deriv (fun a=>F (r,a)) y=
         iteratedDeriv j (fun a=>largeVarianceResidualSpatialJet (i+1) a y) r:=
       (ih r y).deriv
     have hc:=mixed_scalar_partials_commute hF m x
     simp only [hdM,hdX] at hc
     rw [←iteratedDeriv_succ] at hc
     have hJ:=contDiff_residualSpatialMass_joint i (j+1)
     have hraw:=((hJ.differentiable (by simp) (m,x)).hasFDerivAt).comp_hasDerivAt x
       ((hasDerivAt_const x m).prodMk (hasDerivAt_id x))
     have hdiff:DifferentiableAt ℝ (fun y=>iteratedDeriv (j+1)
         (fun r=>largeVarianceResidualSpatialJet i r y) m) x:=hraw.differentiableAt
     have hd:=hdiff.hasDerivAt
     rwa [hc] at hd

 theorem iteratedDeriv_residualSpatialMass_space (i j k:ℕ) (m x:ℝ):
     iteratedDeriv k (fun y=>iteratedDeriv j (fun r=>largeVarianceResidualSpatialJet i r y) m) x=
       iteratedDeriv j (fun r=>largeVarianceResidualSpatialJet (i+k) r x) m:=by
   induction k generalizing x with
   | zero=>simp
   | succ k ih=>
     rw [iteratedDeriv_succ]
     have he:iteratedDeriv k (fun y=>iteratedDeriv j (fun r=>largeVarianceResidualSpatialJet i r y) m)=
         fun y=>iteratedDeriv j (fun r=>largeVarianceResidualSpatialJet (i+k) r y) m:=funext ih
     rw [he]
     have hd:=(hasDerivAt_residualSpatialMass_space (i+k) j m x).deriv
     convert hd using 1 <;> congr 2 <;> omega

end DepthPaper
