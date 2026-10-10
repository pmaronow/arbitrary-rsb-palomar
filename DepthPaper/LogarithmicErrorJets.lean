module

public import DepthPaper.LogDeficitSmallBounds

@[expose] public section


/-! Exact mixed derivatives of the actual logarithmic Cole–Hopf error. -/
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace DepthPaper

 def logarithmicError (m V x:ℝ):ℝ:=m⁻¹*Real.log (1-normalizedDeficit m V x)
 def deficitBaseExpr:ResidualNormalizerExpr:=.atom 0 (.const 1)
 def errorBaseExpr:LogDeficitExpr ResidualNormalizerExpr:=.mul .massInv .logden

 theorem deficitBaseExpr_eval (m V x:ℝ):deficitBaseExpr.eval m V x=normalizedDeficit m V x:=by
   simp [deficitBaseExpr,ResidualNormalizerExpr.eval,normalizedDeficit,
     NormalizerExpr.weightedEval,NormalizerExpr.eval]

 def LogDeficitExpr.residualEval (e:LogDeficitExpr ResidualNormalizerExpr) (m V x:ℝ):ℝ:=
   e.eval (fun a=>a.eval m V x) m (normalizedDeficit m V x)
 def LogDeficitExpr.dx (e:LogDeficitExpr ResidualNormalizerExpr):LogDeficitExpr ResidualNormalizerExpr:=
   e.differentiate ResidualNormalizerExpr.dx deficitBaseExpr.dx 0
 def LogDeficitExpr.dV (e:LogDeficitExpr ResidualNormalizerExpr):LogDeficitExpr ResidualNormalizerExpr:=
   e.differentiate ResidualNormalizerExpr.dV deficitBaseExpr.dV 0
 def LogDeficitExpr.dm (e:LogDeficitExpr MassResidualNormalizerExpr):LogDeficitExpr MassResidualNormalizerExpr:=
   e.differentiate MassResidualNormalizerExpr.dm deficitBaseExpr.lift.dm 1

 theorem LogDeficitExpr.residualEval_map (e:LogDeficitExpr ResidualNormalizerExpr) (m V x:ℝ):
     (e.map ResidualNormalizerExpr.lift).physicalEval m V x=e.residualEval m V x:=by
   unfold physicalEval residualEval
   rw [eval_map]
   congr 1
   funext a
   exact a.eval_lift m V x

 theorem LogDeficitExpr.hasDerivAt_residualEval_space (e:LogDeficitExpr ResidualNormalizerExpr)
     {m V:ℝ} (hm:m∈Ioo (0:ℝ) 2) (hV:0<V) (x:ℝ):
     HasDerivAt (e.residualEval m V) (e.dx.residualEval m V x) x:=by
   have hδ:deficitBaseExpr.eval m V=normalizedDeficit m V:=funext (deficitBaseExpr_eval m V)
   have hd:=deficitBaseExpr.hasDerivAt_space hm V x
   rw [hδ] at hd
   exact e.hasDerivAt_eval (fun a y=>a.eval m V y) (fun _=>m) (normalizedDeficit m V)
     ResidualNormalizerExpr.dx deficitBaseExpr.dx 0 x
     (fun a=>a.hasDerivAt_space hm V x) (hasDerivAt_const x m) hd hm.1.ne'
       (one_sub_normalizedDeficit_pos hm V x hV.le).ne'

 theorem LogDeficitExpr.hasDerivAt_residualEval_variance (e:LogDeficitExpr ResidualNormalizerExpr)
     {m V:ℝ} (hm:m∈Ioo (0:ℝ) 2) (hV:0<V) (x:ℝ):
     HasDerivAt (fun v=>e.residualEval m v x) (e.dV.residualEval m V x) V:=by
   have hδ:(fun v=>deficitBaseExpr.eval m v x)=fun v=>normalizedDeficit m v x:=
     funext (fun v=>deficitBaseExpr_eval m v x)
   have hd:=deficitBaseExpr.hasDerivAt_variance hm hV x
   rw [hδ] at hd
   exact e.hasDerivAt_eval (fun a v=>a.eval m v x) (fun _=>m) (fun v=>normalizedDeficit m v x)
     ResidualNormalizerExpr.dV deficitBaseExpr.dV 0 V
     (fun a=>a.hasDerivAt_variance hm hV x) (hasDerivAt_const V m) hd hm.1.ne'
       (one_sub_normalizedDeficit_pos hm V x hV.le).ne'

 theorem LogDeficitExpr.hasDerivAt_physicalEval_mass (e:LogDeficitExpr MassResidualNormalizerExpr)
     {m V:ℝ} (hm:m∈Ioo (0:ℝ) 2) (hV:0<V) (x:ℝ):
     HasDerivAt (fun r=>e.physicalEval r V x) (e.dm.physicalEval m V x) m:=by
   have hδ:(fun r=>deficitBaseExpr.lift.eval r V x)=fun r=>normalizedDeficit r V x:=by
     funext r
     rw [ResidualNormalizerExpr.eval_lift,deficitBaseExpr_eval]
   have hd:=deficitBaseExpr.lift.hasDerivAt_mass hm V x
   rw [hδ] at hd
   exact e.hasDerivAt_eval (fun a r=>a.eval r V x) id (fun r=>normalizedDeficit r V x)
     MassResidualNormalizerExpr.dm deficitBaseExpr.lift.dm 1 m
     (fun a=>a.hasDerivAt_mass hm V x) (hasDerivAt_id m) hd hm.1.ne'
       (one_sub_normalizedDeficit_pos hm V x hV.le).ne'

 theorem LogDeficitExpr.iteratedDeriv_residualEval_space (e:LogDeficitExpr ResidualNormalizerExpr)
     (i:ℕ) {m V:ℝ} (hm:m∈Ioo (0:ℝ) 2) (hV:0<V) (x:ℝ):
     iteratedDeriv i (e.residualEval m V) x=(dx^[i] e).residualEval m V x:=by
   induction i generalizing x with
   | zero=>simp
   | succ i hi=>
     rw [iteratedDeriv_succ]
     have he:iteratedDeriv i (e.residualEval m V)=(dx^[i] e).residualEval m V:=funext hi
     rw [he]
     simpa only [Function.iterate_succ_apply'] using
       ((dx^[i] e).hasDerivAt_residualEval_space hm hV x).deriv

 theorem LogDeficitExpr.iteratedDeriv_residualEval_variance (e:LogDeficitExpr ResidualNormalizerExpr)
     (k:ℕ) {m V:ℝ} (hm:m∈Ioo (0:ℝ) 2) (hV:0<V) (x:ℝ):
     iteratedDeriv k (fun v=>e.residualEval m v x) V=(dV^[k] e).residualEval m V x:=by
   induction k generalizing V with
   | zero=>simp
   | succ k hi=>
     rw [iteratedDeriv_succ]
     have he:iteratedDeriv k (fun v=>e.residualEval m v x)=ᶠ[𝓝 V]
         (fun v=>(dV^[k] e).residualEval m v x):=
       Filter.Eventually.mono (isOpen_Ioi.mem_nhds hV) (fun v hv=>hi hv)
     rw [he.deriv_eq]
     simpa only [Function.iterate_succ_apply'] using
       ((dV^[k] e).hasDerivAt_residualEval_variance hm hV x).deriv

 theorem LogDeficitExpr.iteratedDeriv_physicalEval_mass (e:LogDeficitExpr MassResidualNormalizerExpr)
     (j:ℕ) {m V:ℝ} (hm:m∈Ioo (0:ℝ) 2) (hV:0<V) (x:ℝ):
     iteratedDeriv j (fun r=>e.physicalEval r V x) m=(dm^[j] e).physicalEval m V x:=by
   induction j generalizing m with
   | zero=>simp
   | succ j hi=>
     rw [iteratedDeriv_succ]
     have he:iteratedDeriv j (fun r=>e.physicalEval r V x)=ᶠ[𝓝 m]
         (fun r=>(dm^[j] e).physicalEval r V x):=
       Filter.Eventually.mono (isOpen_Ioo.mem_nhds hm) (fun r hr=>hi hr)
     rw [he.deriv_eq]
     simpa only [Function.iterate_succ_apply'] using
       ((dm^[j] e).hasDerivAt_physicalEval_mass hm hV x).deriv

 theorem LogDeficitExpr.small_iterate_differentiate {α:Type} (e:LogDeficitExpr α)
     (da:α→α) (dz:α) (dm:ℝ) (n:ℕ) (he:e.Small):
     ((differentiate da dz dm)^[n] e).Small:=by
   induction n with
   | zero=>exact he
   | succ n hn=>
     rw [Function.iterate_succ_apply']
     exact small_differentiate _ _ _ _ hn

 theorem logarithmicError_mixed_eq (i j k:ℕ) {m V:ℝ} (hm:m∈Ioo (0:ℝ) 2)
     (hV:0<V) (x:ℝ):
     iteratedDeriv j (fun r=>iteratedDeriv k
       (fun v=>iteratedDeriv i (logarithmicError r v) x) V) m=
       (LogDeficitExpr.dm^[j]
         ((LogDeficitExpr.dV^[k] (LogDeficitExpr.dx^[i] errorBaseExpr)).map
           ResidualNormalizerExpr.lift)).physicalEval m V x:=by
   have hb:logarithmicError=errorBaseExpr.residualEval:=by
     funext m V x
     rfl
   have he:(fun r=>iteratedDeriv k
       (fun v=>iteratedDeriv i (logarithmicError r v) x) V)=ᶠ[𝓝 m]
         (fun r=>((LogDeficitExpr.dV^[k] (LogDeficitExpr.dx^[i] errorBaseExpr)).map
           ResidualNormalizerExpr.lift).physicalEval r V x):=by
     refine Filter.Eventually.mono (isOpen_Ioo.mem_nhds hm) ?_
     intro r hr
     rw [hb]
     have he':(fun v=>iteratedDeriv i (errorBaseExpr.residualEval r v) x)=ᶠ[𝓝 V]
         (fun v=>(LogDeficitExpr.dx^[i] errorBaseExpr).residualEval r v x):=
       Filter.Eventually.mono (isOpen_Ioi.mem_nhds hV)
         (fun v hv=>LogDeficitExpr.iteratedDeriv_residualEval_space _ _ hr hv x)
     change iteratedDeriv k (fun v=>iteratedDeriv i (errorBaseExpr.residualEval r v) x) V=
       ((LogDeficitExpr.dV^[k] (LogDeficitExpr.dx^[i] errorBaseExpr)).map
         ResidualNormalizerExpr.lift).physicalEval r V x
     rw [he'.iteratedDeriv_eq k,LogDeficitExpr.iteratedDeriv_residualEval_variance _ _ hr hV,
       LogDeficitExpr.residualEval_map]
   rw [he.iteratedDeriv_eq j,LogDeficitExpr.iteratedDeriv_physicalEval_mass _ _ hm hV]

end DepthPaper
