module

public import GeneralDepthPaper.LogarithmicErrorJets

@[expose] public section


/-! Uniform all-order bounds for actual mass/variance/space mixed derivatives
of the logarithmic Cole–Hopf error. -/
noncomputable section
open Set Filter
open scoped NNReal Topology
namespace GeneralDepthPaper

 theorem logarithmicError_mixed_exponential_bound (i j k:ℕ) {ε:ℝ} (hε:0<ε):
     ∃C:ℝ,0<C ∧ ∃d:ℕ,∀m∈Icc ε 1,∀V≥1,∀x,
       ‖iteratedDeriv j (fun r=>iteratedDeriv k
         (fun v=>iteratedDeriv i (logarithmicError r v) x) V) m‖≤
           C*V^d*Real.exp (-(ε^2)*V/2):=by
   let a:=LogDeficitExpr.dm^[j]
     ((LogDeficitExpr.dV^[k] (LogDeficitExpr.dx^[i] errorBaseExpr)).map
       ResidualNormalizerExpr.lift)
   have hbase:errorBaseExpr.Small:=Or.inr trivial
   have hi:=LogDeficitExpr.small_iterate_differentiate errorBaseExpr
     ResidualNormalizerExpr.dx deficitBaseExpr.dx 0 i hbase
   have hk:=LogDeficitExpr.small_iterate_differentiate _
     ResidualNormalizerExpr.dV deficitBaseExpr.dV 0 k hi
   have hmap:((LogDeficitExpr.dV^[k] (LogDeficitExpr.dx^[i] errorBaseExpr)).map
       ResidualNormalizerExpr.lift).Small:=(LogDeficitExpr.small_map _ _).mpr hk
   have ha:a.Small:=LogDeficitExpr.small_iterate_differentiate _
     MassResidualNormalizerExpr.dm deficitBaseExpr.lift.dm 1 j hmap
   obtain ⟨C,hC,d,hbound⟩:=a.small_exponential_bound hε ha
   refine ⟨C,hC,d,?_⟩
   intro m hm V hV x
   have hm':m∈Ioo (0:ℝ) 2:=⟨hε.trans_le hm.1,hm.2.trans_lt (by norm_num)⟩
   rw [logarithmicError_mixed_eq i j k hm' (zero_lt_one.trans_le hV)]
   exact hbound m hm V hV x

 theorem largeVarianceError_real_eq_logarithmicError {m V:ℝ}
     (hm:m∈Ioo (0:ℝ) 2) (hV:0≤V) (x:ℝ):
     largeVarianceError m V.toNNReal x=logarithmicError m V x:=by
   rw [largeVarianceError_eq_log_deficit hm]
   simp only [Real.coe_toNNReal V hV,one_div,logarithmicError]

 theorem largeVarianceError_mixed_eq_logarithmicError (i j k:ℕ) {m V:ℝ}
     (hm:m∈Ioo (0:ℝ) 2) (hV:0<V) (x:ℝ):
     iteratedDeriv j (fun r=>iteratedDeriv k
       (fun v=>iteratedDeriv i (largeVarianceError r v.toNNReal) x) V) m=
         iteratedDeriv j (fun r=>iteratedDeriv k
           (fun v=>iteratedDeriv i (logarithmicError r v) x) V) m:=by
   have hmEq:(fun r=>iteratedDeriv k
       (fun v=>iteratedDeriv i (largeVarianceError r v.toNNReal) x) V)=ᶠ[𝓝 m]
         (fun r=>iteratedDeriv k (fun v=>iteratedDeriv i (logarithmicError r v) x) V):=by
     refine Filter.Eventually.mono (isOpen_Ioo.mem_nhds hm) ?_
     intro r hr
     have hVEq:(fun v=>iteratedDeriv i (largeVarianceError r v.toNNReal) x)=ᶠ[𝓝 V]
         (fun v=>iteratedDeriv i (logarithmicError r v) x):=by
       refine Filter.Eventually.mono (isOpen_Ioi.mem_nhds hV) ?_
       intro v hv
       have he:largeVarianceError r v.toNNReal=logarithmicError r v:=
         funext (largeVarianceError_real_eq_logarithmicError hr hv.le)
       exact congrFun (congrArg (iteratedDeriv i) he) x
     exact hVEq.iteratedDeriv_eq k
   exact hmEq.iteratedDeriv_eq j

 theorem largeVarianceError_mixed_exponential_bound (i j k:ℕ) {ε:ℝ} (hε:0<ε):
     ∃C:ℝ,0<C ∧ ∃d:ℕ,∀m∈Icc ε 1,∀V≥1,∀x,
       ‖iteratedDeriv j (fun r=>iteratedDeriv k
         (fun v=>iteratedDeriv i (largeVarianceError r v.toNNReal) x) V) m‖≤
           C*V^d*Real.exp (-(ε^2)*V/2):=by
   obtain ⟨C,hC,d,hbound⟩:=logarithmicError_mixed_exponential_bound i j k hε
   refine ⟨C,hC,d,?_⟩
   intro m hm V hV x
   have hm':m∈Ioo (0:ℝ) 2:=⟨hε.trans_le hm.1,hm.2.trans_lt (by norm_num)⟩
   rw [largeVarianceError_mixed_eq_logarithmicError i j k hm' (zero_lt_one.trans_le hV)]
   exact hbound m hm V hV x

end GeneralDepthPaper
