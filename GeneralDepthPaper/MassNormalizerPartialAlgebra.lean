module

public import GeneralDepthPaper.ResidualHeatAllPartialJets
public import GeneralDepthPaper.LogarithmicErrorBounds

@[expose] public section


/-! The normalized differential algebra supports the literal source order
variance, mass, then spatial derivatives. -/
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace GeneralDepthPaper

 def MassResidualNormalizerExpr.dx :MassResidualNormalizerExpr→MassResidualNormalizerExpr
 | .atom i j e=>.add (.atom (i+1) j e) (.atom i j e.weightedDx)
 | .add a b=>.add a.dx b.dx
 | .scale c a=>.scale c a.dx

 def MassResidualNormalizerExpr.dV :MassResidualNormalizerExpr→MassResidualNormalizerExpr
 | .atom i j e=>.add (.scale (1/2) (.atom (i+2) j e)) (.atom i j e.weightedDV)
 | .add a b=>.add a.dV b.dV
 | .scale c a=>.scale c a.dV

 theorem MassResidualNormalizerExpr.hasDerivAt_space (a:MassResidualNormalizerExpr) {m:ℝ}
     (hm:m∈Ioo (0:ℝ) 2) (V x:ℝ):
     HasDerivAt (fun y=>a.eval m V y) (a.dx.eval m V x) x:=by
   induction a with
   | atom i j e=>
     have hd:=(hasDerivAt_residualHeatMassJet_space i j hm V.toNNReal x).mul
       (e.hasDerivAt_weightedEval_space m V x)
     convert hd using 1 <;> rfl
   | add a b ha hb=>exact ha.add hb
   | scale c a ha=>exact ha.const_mul c

 theorem MassResidualNormalizerExpr.hasDerivAt_variance (a:MassResidualNormalizerExpr) {m V:ℝ}
     (hm:m∈Ioo (0:ℝ) 2) (hV:0<V) (x:ℝ):
     HasDerivAt (fun v=>a.eval m v x) (a.dV.eval m V x) V:=by
   induction a with
   | atom i j e=>
     have hd:=(hasDerivAt_residualHeatMassJet_variance_all i j hm hV x).mul
       (e.hasDerivAt_weightedEval_variance m V x)
     convert hd using 1
     · rfl
     · simp only [dV,eval]
       ring
   | add a b ha hb=>exact ha.add hb
   | scale c a ha=>exact ha.const_mul c

 def LogDeficitExpr.massDx (e:LogDeficitExpr MassResidualNormalizerExpr):LogDeficitExpr MassResidualNormalizerExpr:=
   e.differentiate MassResidualNormalizerExpr.dx deficitBaseExpr.lift.dx 0
 def LogDeficitExpr.massDV (e:LogDeficitExpr MassResidualNormalizerExpr):LogDeficitExpr MassResidualNormalizerExpr:=
   e.differentiate MassResidualNormalizerExpr.dV deficitBaseExpr.lift.dV 0
 def errorMassBaseExpr:LogDeficitExpr MassResidualNormalizerExpr:=errorBaseExpr.map ResidualNormalizerExpr.lift

 theorem errorMassBaseExpr_eval (m V x:ℝ):errorMassBaseExpr.physicalEval m V x=logarithmicError m V x:=rfl

 theorem LogDeficitExpr.hasDerivAt_physicalEval_space (e:LogDeficitExpr MassResidualNormalizerExpr)
     {m V:ℝ} (hm:m∈Ioo (0:ℝ) 2) (hV:0<V) (x:ℝ):
     HasDerivAt (fun y=>e.physicalEval m V y) (e.massDx.physicalEval m V x) x:=by
   have hδ:(fun y=>deficitBaseExpr.lift.eval m V y)=normalizedDeficit m V:=by
     funext y
     rw [ResidualNormalizerExpr.eval_lift,deficitBaseExpr_eval]
   have hd:=deficitBaseExpr.lift.hasDerivAt_space hm V x
   rw [hδ] at hd
   exact e.hasDerivAt_eval (fun a y=>a.eval m V y) (fun _=>m) (normalizedDeficit m V)
     MassResidualNormalizerExpr.dx deficitBaseExpr.lift.dx 0 x
     (fun a=>a.hasDerivAt_space hm V x) (hasDerivAt_const x m) hd hm.1.ne'
       (one_sub_normalizedDeficit_pos hm V x hV.le).ne'

 theorem LogDeficitExpr.hasDerivAt_physicalEval_variance (e:LogDeficitExpr MassResidualNormalizerExpr)
     {m V:ℝ} (hm:m∈Ioo (0:ℝ) 2) (hV:0<V) (x:ℝ):
     HasDerivAt (fun v=>e.physicalEval m v x) (e.massDV.physicalEval m V x) V:=by
   have hδ:(fun v=>deficitBaseExpr.lift.eval m v x)=fun v=>normalizedDeficit m v x:=by
     funext v
     rw [ResidualNormalizerExpr.eval_lift,deficitBaseExpr_eval]
   have hd:=deficitBaseExpr.lift.hasDerivAt_variance hm hV x
   rw [hδ] at hd
   exact e.hasDerivAt_eval (fun a v=>a.eval m v x) (fun _=>m) (fun v=>normalizedDeficit m v x)
     MassResidualNormalizerExpr.dV deficitBaseExpr.lift.dV 0 V
     (fun a=>a.hasDerivAt_variance hm hV x) (hasDerivAt_const V m) hd hm.1.ne'
       (one_sub_normalizedDeficit_pos hm V x hV.le).ne'

 theorem LogDeficitExpr.iteratedDeriv_physicalEval_space (e:LogDeficitExpr MassResidualNormalizerExpr)
     (i:ℕ) {m V:ℝ} (hm:m∈Ioo (0:ℝ) 2) (hV:0<V) (x:ℝ):
     iteratedDeriv i (fun y=>e.physicalEval m V y) x=(massDx^[i] e).physicalEval m V x:=by
   induction i generalizing x with
   | zero=>simp
   | succ i hi=>
     rw [iteratedDeriv_succ]
     have he:iteratedDeriv i (fun y=>e.physicalEval m V y)=(massDx^[i] e).physicalEval m V:=funext hi
     rw [he]
     simpa only [Function.iterate_succ_apply'] using
       ((massDx^[i] e).hasDerivAt_physicalEval_space hm hV x).deriv

 theorem LogDeficitExpr.iteratedDeriv_physicalEval_variance (e:LogDeficitExpr MassResidualNormalizerExpr)
     (k:ℕ) {m V:ℝ} (hm:m∈Ioo (0:ℝ) 2) (hV:0<V) (x:ℝ):
     iteratedDeriv k (fun v=>e.physicalEval m v x) V=(massDV^[k] e).physicalEval m V x:=by
   induction k generalizing V with
   | zero=>simp
   | succ k hi=>
     rw [iteratedDeriv_succ]
     have he:iteratedDeriv k (fun v=>e.physicalEval m v x)=ᶠ[𝓝 V]
         (fun v=>(massDV^[k] e).physicalEval m v x):=
       Filter.Eventually.mono (isOpen_Ioi.mem_nhds hV) (fun v hv=>hi hv)
     rw [he.deriv_eq]
     simpa only [Function.iterate_succ_apply'] using
       ((massDV^[k] e).hasDerivAt_physicalEval_variance hm hV x).deriv

 theorem logarithmicError_source_mixed_eq (i j k:ℕ) {m V:ℝ} (hm:m∈Ioo (0:ℝ) 2)
     (hV:0<V) (x:ℝ):
     iteratedDeriv i (fun y=>iteratedDeriv j (fun r=>iteratedDeriv k
       (fun v=>logarithmicError r v y) V) m) x=
       (LogDeficitExpr.massDx^[i] (LogDeficitExpr.dm^[j]
         (LogDeficitExpr.massDV^[k] errorMassBaseExpr))).physicalEval m V x:=by
   have he:(fun y=>iteratedDeriv j (fun r=>iteratedDeriv k
       (fun v=>logarithmicError r v y) V) m)=
         fun y=>(LogDeficitExpr.dm^[j] (LogDeficitExpr.massDV^[k] errorMassBaseExpr)).physicalEval m V y:=by
     funext y
     have hmEq:(fun r=>iteratedDeriv k (fun v=>logarithmicError r v y) V)=ᶠ[𝓝 m]
         (fun r=>(LogDeficitExpr.massDV^[k] errorMassBaseExpr).physicalEval r V y):=by
       refine Filter.Eventually.mono (isOpen_Ioo.mem_nhds hm) ?_
       intro r hr
       change iteratedDeriv k (fun v=>logarithmicError r v y) V=_
       have hb:(fun v=>logarithmicError r v y)=fun v=>errorMassBaseExpr.physicalEval r v y:=rfl
       rw [hb,LogDeficitExpr.iteratedDeriv_physicalEval_variance _ _ hr hV]
     rw [hmEq.iteratedDeriv_eq j,LogDeficitExpr.iteratedDeriv_physicalEval_mass _ _ hm hV]
   rw [he,LogDeficitExpr.iteratedDeriv_physicalEval_space _ _ hm hV]

end GeneralDepthPaper
