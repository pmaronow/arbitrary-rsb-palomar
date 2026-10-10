module

public import GeneralDepthPaper.ResidualHeatVarianceJets

@[expose] public section


/-! Genuine all-order uniformly bounded mixed derivatives of the convolved
residual. This is the analytic numerator estimate in Appendix B.1; the
normalized logarithmic error still requires separate estimates. -/
noncomputable section
open Set
open scoped NNReal
namespace GeneralDepthPaper

 theorem residualHeat_mixed_uniform_bound (i j k:ℕ) {ε:ℝ} (hε:0<ε):
     ∃K:ℝ,0<K ∧ ∀m∈Icc ε (2-ε),∀(V:ℝ),0<V→∀x:ℝ,
       ‖iteratedDeriv j (fun r=>iteratedDeriv k
         (fun v=>iteratedDeriv i (fun y=>residualHeatMassJet 0 0 r v.toNNReal y) x) V) m‖≤K:=by
   obtain ⟨K,hK,hbound⟩:=residualHeatMassJet_uniform_bound (i+2*k) j hε
   refine ⟨K,hK,?_⟩
   intro m hm V hV x
   have hm':m∈Ioo (0:ℝ) 2:=⟨hε.trans_le hm.1,by linarith [hm.2]⟩
   rw [iteratedDeriv_residualHeat_spatial_variance_mass i j k hm' hV,norm_mul,norm_pow,
     Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
   have hp:(1/2:ℝ)^k≤1:=pow_le_one₀ (by norm_num) (by norm_num)
   exact (mul_le_mul hp (hbound m hm V.toNNReal x) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

end GeneralDepthPaper
