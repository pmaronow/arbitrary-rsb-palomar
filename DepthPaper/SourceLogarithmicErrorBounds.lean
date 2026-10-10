module

public import DepthPaper.MassNormalizerPartialAlgebra

@[expose] public section


/-! Literal source-order all mixed derivatives of the actual Cole–Hopf error. -/
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace DepthPaper

 theorem logarithmicError_source_mixed_exponential_bound (i j k:ℕ) {ε:ℝ} (hε:0<ε):
     ∃C:ℝ,0<C ∧ ∃d:ℕ,∀m∈Icc ε 1,∀V≥1,∀x,
       ‖iteratedDeriv i (fun y=>iteratedDeriv j (fun r=>iteratedDeriv k
         (fun v=>logarithmicError r v y) V) m) x‖≤C*V^d*Real.exp (-(ε^2)*V/2):=by
   let a:=LogDeficitExpr.massDx^[i] (LogDeficitExpr.dm^[j]
     (LogDeficitExpr.massDV^[k] errorMassBaseExpr))
   have hbase:errorMassBaseExpr.Small:=by exact Or.inr trivial
   have hk:=LogDeficitExpr.small_iterate_differentiate errorMassBaseExpr
     MassResidualNormalizerExpr.dV deficitBaseExpr.lift.dV 0 k hbase
   have hj:=LogDeficitExpr.small_iterate_differentiate _
     MassResidualNormalizerExpr.dm deficitBaseExpr.lift.dm 1 j hk
   have ha:a.Small:=LogDeficitExpr.small_iterate_differentiate _
     MassResidualNormalizerExpr.dx deficitBaseExpr.lift.dx 0 i hj
   obtain ⟨C,hC,d,hbound⟩:=a.small_exponential_bound hε ha
   refine ⟨C,hC,d,?_⟩
   intro m hm V hV x
   have hm':m∈Ioo (0:ℝ) 2:=⟨hε.trans_le hm.1,hm.2.trans_lt (by norm_num)⟩
   rw [logarithmicError_source_mixed_eq i j k hm' (zero_lt_one.trans_le hV)]
   exact hbound m hm V hV x

 theorem largeVarianceError_source_mixed_eq_logarithmicError (i j k:ℕ) {m V:ℝ}
     (hm:m∈Ioo (0:ℝ) 2) (hV:0<V) (x:ℝ):
     iteratedDeriv i (fun y=>iteratedDeriv j (fun r=>iteratedDeriv k
       (fun v=>largeVarianceError r v.toNNReal y) V) m) x=
       iteratedDeriv i (fun y=>iteratedDeriv j (fun r=>iteratedDeriv k
         (fun v=>logarithmicError r v y) V) m) x:=by
   have he:(fun y=>iteratedDeriv j (fun r=>iteratedDeriv k
       (fun v=>largeVarianceError r v.toNNReal y) V) m)=
         fun y=>iteratedDeriv j (fun r=>iteratedDeriv k
           (fun v=>logarithmicError r v y) V) m:=by
     funext y
     have hmEq:(fun r=>iteratedDeriv k (fun v=>largeVarianceError r v.toNNReal y) V)=ᶠ[𝓝 m]
         (fun r=>iteratedDeriv k (fun v=>logarithmicError r v y) V):=by
       refine Filter.Eventually.mono (isOpen_Ioo.mem_nhds hm) ?_
       intro r hr
       have hVEq:(fun v=>largeVarianceError r v.toNNReal y)=ᶠ[𝓝 V]
           (fun v=>logarithmicError r v y):=
         Filter.Eventually.mono (isOpen_Ioi.mem_nhds hV)
           (fun v hv=>largeVarianceError_real_eq_logarithmicError hr hv.le y)
       exact hVEq.iteratedDeriv_eq k
     exact hmEq.iteratedDeriv_eq j
   exact congrFun (congrArg (iteratedDeriv i) he) x

 theorem largeVarianceError_source_mixed_exponential_bound (i j k:ℕ) {ε:ℝ} (hε:0<ε):
     ∃C:ℝ,0<C ∧ ∃d:ℕ,∀m∈Icc ε 1,∀V≥1,∀x,
       ‖iteratedDeriv i (fun y=>iteratedDeriv j (fun r=>iteratedDeriv k
         (fun v=>largeVarianceError r v.toNNReal y) V) m) x‖≤
           C*V^d*Real.exp (-(ε^2)*V/2):=by
   obtain ⟨C,hC,d,hbound⟩:=logarithmicError_source_mixed_exponential_bound i j k hε
   refine ⟨C,hC,d,?_⟩
   intro m hm V hV x
   have hm':m∈Ioo (0:ℝ) 2:=⟨hε.trans_le hm.1,hm.2.trans_lt (by norm_num)⟩
   rw [largeVarianceError_source_mixed_eq_logarithmicError i j k hm' (zero_lt_one.trans_le hV)]
   exact hbound m hm V hV x

end DepthPaper
