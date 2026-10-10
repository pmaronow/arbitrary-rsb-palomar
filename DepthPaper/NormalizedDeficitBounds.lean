module

public import DepthPaper.NormalizedDeficitAlgebra

@[expose] public section


/-! Actual mixed normalized-deficit derivatives are exponentially small,
uniformly in space and on compact positive mass ranges. -/
noncomputable section
open Set
namespace DepthPaper

 theorem MassResidualNormalizerExpr.exponential_bound (a:MassResidualNormalizerExpr)
     {ε:ℝ} (hε:0<ε):
     ∃C:ℝ,0<C ∧ ∃d:ℕ,∀m∈Icc ε 1,∀V≥1,∀x,
       ‖a.eval m V x‖≤C*V^d*Real.exp (-(ε^2)*V/2):=by
   induction a with
   | atom i j e=>
     let δ:ℝ:=min ε (1/2)
     have hδ:0<δ:=lt_min hε (by norm_num)
     obtain ⟨K,hK,hheat⟩:=residualHeatMassJet_uniform_bound i j hδ
     obtain ⟨C,hC,d,he⟩:=e.weighted_exponential_bound hε
     refine ⟨K*C,mul_pos hK hC,d,?_⟩
     intro m hm V hV x
     have hmδ:m∈Icc δ (2-δ):=by
       constructor
       · exact (min_le_left _ _).trans hm.1
       · have hd:δ≤1/2:=min_le_right _ _
         linarith [hm.2]
     change ‖residualHeatMassJet i j m V.toNNReal x*e.weightedEval m V x‖≤_
     rw [norm_mul]
     have hh:=mul_le_mul (hheat m hmδ V.toNNReal x) (he m hm V hV x)
       (norm_nonneg _) hK.le
     exact hh.trans_eq (by ring)
   | add a b ha hb=>
     obtain ⟨A,hA,d,ha⟩:=ha
     obtain ⟨B,hB,e,hb⟩:=hb
     refine ⟨A+B,add_pos hA hB,max d e,?_⟩
     intro m hm V hV x
     have hvd:V^d≤V^(max d e):=pow_le_pow_right₀ hV (le_max_left _ _)
     have hve:V^e≤V^(max d e):=pow_le_pow_right₀ hV (le_max_right _ _)
     change ‖a.eval m V x+b.eval m V x‖≤_
     calc
       _≤‖a.eval m V x‖+‖b.eval m V x‖:=norm_add_le _ _
       _≤A*V^d*Real.exp (-(ε^2)*V/2)+B*V^e*Real.exp (-(ε^2)*V/2):=add_le_add (ha m hm V hV x) (hb m hm V hV x)
       _≤A*V^(max d e)*Real.exp (-(ε^2)*V/2)+B*V^(max d e)*Real.exp (-(ε^2)*V/2):=by
         exact add_le_add
           (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvd hA.le) (Real.exp_pos _).le)
           (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hve hB.le) (Real.exp_pos _).le)
       _=(A+B)*V^(max d e)*Real.exp (-(ε^2)*V/2):=by ring
   | scale c a ha=>
     obtain ⟨A,hA,d,ha⟩:=ha
     refine ⟨(‖c‖+1)*A,by positivity,d,?_⟩
     intro m hm V hV x
     change ‖c*a.eval m V x‖≤_
     rw [norm_mul]
     have hh:=mul_le_mul_of_nonneg_left (ha m hm V hV x) (norm_nonneg c)
     have hv:0≤A*V^d*Real.exp (-(ε^2)*V/2):=by positivity
     calc
       _≤‖c‖*(A*V^d*Real.exp (-(ε^2)*V/2)):=hh
       _≤(‖c‖+1)*(A*V^d*Real.exp (-(ε^2)*V/2)):=mul_le_mul_of_nonneg_right (by linarith) hv
       _=(‖c‖+1)*A*V^d*Real.exp (-(ε^2)*V/2):=by ring

 theorem normalizedDeficit_mixed_exponential_bound (i j k:ℕ) {ε:ℝ} (hε:0<ε):
     ∃C:ℝ,0<C ∧ ∃d:ℕ,∀m∈Icc ε 1,∀V≥1,∀x,
       ‖iteratedDeriv j (fun r=>iteratedDeriv k
         (fun v=>iteratedDeriv i (normalizedDeficit r v) x) V) m‖≤
           C*V^d*Real.exp (-(ε^2)*V/2):=by
   let a:=MassResidualNormalizerExpr.dm^[j]
     ((ResidualNormalizerExpr.dV^[k]
       (ResidualNormalizerExpr.dx^[i] (.atom 0 (.const 1)))).lift)
   obtain ⟨C,hC,d,hbound⟩:=a.exponential_bound hε
   refine ⟨C,hC,d,?_⟩
   intro m hm V hV x
   have hm':m∈Ioo (0:ℝ) 2:=⟨hε.trans_le hm.1,hm.2.trans_lt (by norm_num)⟩
   rw [normalizedDeficit_mixed_eq i j k hm' (zero_lt_one.trans_le hV)]
   exact hbound m hm V hV x

end DepthPaper
