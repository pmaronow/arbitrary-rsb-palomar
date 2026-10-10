module

public import DepthPaper.ResidualHeatSectionSmooth

@[expose] public section


/-! A finite differential algebra for the actual normalized Gaussian deficit.
No derivative bound is encoded as an assumption in the expressions. -/
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace DepthPaper

 inductive ResidualNormalizerExpr where
 | atom (i:ℕ) (e:NormalizerExpr)
 | add (a b:ResidualNormalizerExpr)
 | scale (c:ℝ) (a:ResidualNormalizerExpr)

 inductive MassResidualNormalizerExpr where
 | atom (i j:ℕ) (e:NormalizerExpr)
 | add (a b:MassResidualNormalizerExpr)
 | scale (c:ℝ) (a:MassResidualNormalizerExpr)

 def ResidualNormalizerExpr.eval :ResidualNormalizerExpr→ℝ→ℝ→ℝ→ℝ
 | .atom i e,m,V,x=>residualHeatMassJet i 0 m V.toNNReal x*e.weightedEval m V x
 | .add a b,m,V,x=>a.eval m V x+b.eval m V x
 | .scale c a,m,V,x=>c*a.eval m V x

 def MassResidualNormalizerExpr.eval :MassResidualNormalizerExpr→ℝ→ℝ→ℝ→ℝ
 | .atom i j e,m,V,x=>residualHeatMassJet i j m V.toNNReal x*e.weightedEval m V x
 | .add a b,m,V,x=>a.eval m V x+b.eval m V x
 | .scale c a,m,V,x=>c*a.eval m V x

 def ResidualNormalizerExpr.dx :ResidualNormalizerExpr→ResidualNormalizerExpr
 | .atom i e=>.add (.atom (i+1) e) (.atom i e.weightedDx)
 | .add a b=>.add a.dx b.dx
 | .scale c a=>.scale c a.dx

 def ResidualNormalizerExpr.dV :ResidualNormalizerExpr→ResidualNormalizerExpr
 | .atom i e=>.add (.scale (1/2) (.atom (i+2) e)) (.atom i e.weightedDV)
 | .add a b=>.add a.dV b.dV
 | .scale c a=>.scale c a.dV

 def ResidualNormalizerExpr.lift :ResidualNormalizerExpr→MassResidualNormalizerExpr
 | .atom i e=>.atom i 0 e
 | .add a b=>.add a.lift b.lift
 | .scale c a=>.scale c a.lift

 def MassResidualNormalizerExpr.dm :MassResidualNormalizerExpr→MassResidualNormalizerExpr
 | .atom i j e=>.add (.atom i (j+1) e) (.atom i j e.weightedDm)
 | .add a b=>.add a.dm b.dm
 | .scale c a=>.scale c a.dm

 theorem ResidualNormalizerExpr.eval_lift (a:ResidualNormalizerExpr) (m V x:ℝ):
     a.lift.eval m V x=a.eval m V x:=by
   induction a with
   | atom i e=>rfl
   | add a b ha hb=>simp only [lift,MassResidualNormalizerExpr.eval,eval,ha,hb]
   | scale c a ha=>simp only [lift,MassResidualNormalizerExpr.eval,eval,ha]

 theorem ResidualNormalizerExpr.hasDerivAt_space (a:ResidualNormalizerExpr) {m:ℝ}
     (hm:m∈Ioo (0:ℝ) 2) (V x:ℝ):
     HasDerivAt (a.eval m V) (a.dx.eval m V x) x:=by
   induction a with
   | atom i e=>
     have hd:=(hasDerivAt_residualHeat_space i hm V.toNNReal x).mul
       (e.hasDerivAt_weightedEval_space m V x)
     convert hd using 1 <;> rfl
   | add a b ha hb=>exact ha.add hb
   | scale c a ha=>exact ha.const_mul c

 theorem ResidualNormalizerExpr.hasDerivAt_variance (a:ResidualNormalizerExpr) {m V:ℝ}
     (hm:m∈Ioo (0:ℝ) 2) (hV:0<V) (x:ℝ):
     HasDerivAt (fun v=>a.eval m v x) (a.dV.eval m V x) V:=by
   induction a with
   | atom i e=>
     have hd:=(hasDerivAt_residualHeatMassJet_variance i hm hV x).mul
       (e.hasDerivAt_weightedEval_variance m V x)
     convert hd using 1
     · rfl
     · simp only [dV,eval]
       ring
   | add a b ha hb=>exact ha.add hb
   | scale c a ha=>exact ha.const_mul c

 theorem MassResidualNormalizerExpr.hasDerivAt_mass (a:MassResidualNormalizerExpr) {m:ℝ}
     (hm:m∈Ioo (0:ℝ) 2) (V x:ℝ):
     HasDerivAt (fun r=>a.eval r V x) (a.dm.eval m V x) m:=by
   induction a with
   | atom i j e=>
     have hd:=(hasDerivAt_residualHeatMassJet_mass i j hm V.toNNReal x).mul
       (e.hasDerivAt_weightedEval_mass m V x)
     convert hd using 1 <;> rfl
   | add a b ha hb=>exact ha.add hb
   | scale c a ha=>exact ha.const_mul c

 theorem ResidualNormalizerExpr.iteratedDeriv_space (a:ResidualNormalizerExpr) (i:ℕ)
     {m:ℝ} (hm:m∈Ioo (0:ℝ) 2) (V x:ℝ):
     iteratedDeriv i (a.eval m V) x=(dx^[i] a).eval m V x:=by
   induction i generalizing x with
   | zero=>simp
   | succ i hi=>
     rw [iteratedDeriv_succ]
     have he:iteratedDeriv i (a.eval m V)=(dx^[i] a).eval m V:=funext hi
     rw [he]
     simpa only [Function.iterate_succ_apply'] using
       ((dx^[i] a).hasDerivAt_space hm V x).deriv

 theorem ResidualNormalizerExpr.iteratedDeriv_variance (a:ResidualNormalizerExpr) (k:ℕ)
     {m V:ℝ} (hm:m∈Ioo (0:ℝ) 2) (hV:0<V) (x:ℝ):
     iteratedDeriv k (fun v=>a.eval m v x) V=(dV^[k] a).eval m V x:=by
   induction k generalizing V with
   | zero=>simp
   | succ k hi=>
     rw [iteratedDeriv_succ]
     have he:iteratedDeriv k (fun v=>a.eval m v x)=ᶠ[𝓝 V]
         (fun v=>(dV^[k] a).eval m v x):=
       Filter.Eventually.mono (isOpen_Ioi.mem_nhds hV) (fun v hv=>hi hv)
     rw [he.deriv_eq]
     simpa only [Function.iterate_succ_apply'] using
       ((dV^[k] a).hasDerivAt_variance hm hV x).deriv

 theorem MassResidualNormalizerExpr.iteratedDeriv_mass (a:MassResidualNormalizerExpr) (j:ℕ)
     {m:ℝ} (hm:m∈Ioo (0:ℝ) 2) (V x:ℝ):
     iteratedDeriv j (fun r=>a.eval r V x) m=(dm^[j] a).eval m V x:=by
   induction j generalizing m with
   | zero=>simp
   | succ j hi=>
     rw [iteratedDeriv_succ]
     have he:iteratedDeriv j (fun r=>a.eval r V x)=ᶠ[𝓝 m]
         (fun r=>(dm^[j] a).eval r V x):=
       Filter.Eventually.mono (isOpen_Ioo.mem_nhds hm) (fun r hr=>hi hr)
     rw [he.deriv_eq]
     simpa only [Function.iterate_succ_apply'] using
       ((dm^[j] a).hasDerivAt_mass hm V x).deriv

 def normalizedDeficit (m V x:ℝ):ℝ:=
   residualHeatMassJet 0 0 m V.toNNReal x*normalizerInverse m V x

 theorem normalizedDeficit_mixed_eq (i j k:ℕ) {m V:ℝ} (hm:m∈Ioo (0:ℝ) 2)
     (hV:0<V) (x:ℝ):
     iteratedDeriv j (fun r=>iteratedDeriv k
       (fun v=>iteratedDeriv i (normalizedDeficit r v) x) V) m=
       (MassResidualNormalizerExpr.dm^[j]
         ((ResidualNormalizerExpr.dV^[k]
           (ResidualNormalizerExpr.dx^[i] (.atom 0 (.const 1)))).lift)).eval m V x:=by
   let a:ResidualNormalizerExpr:=.atom 0 (.const 1)
   have hb:normalizedDeficit=a.eval:=by
     funext m V x
     simp [normalizedDeficit,a,ResidualNormalizerExpr.eval,NormalizerExpr.weightedEval,NormalizerExpr.eval]
   have he:(fun r=>iteratedDeriv k
       (fun v=>iteratedDeriv i (normalizedDeficit r v) x) V)=ᶠ[𝓝 m]
         (fun r=>(ResidualNormalizerExpr.dV^[k] (ResidualNormalizerExpr.dx^[i] a)).lift.eval r V x):=by
     refine Filter.Eventually.mono (isOpen_Ioo.mem_nhds hm) ?_
     intro r hr
     rw [hb]
     simp only [ResidualNormalizerExpr.iteratedDeriv_space _ _ hr,
       ResidualNormalizerExpr.iteratedDeriv_variance _ _ hr hV,
       ResidualNormalizerExpr.eval_lift]
   rw [he.iteratedDeriv_eq j,MassResidualNormalizerExpr.iteratedDeriv_mass _ _ hm]

end DepthPaper
