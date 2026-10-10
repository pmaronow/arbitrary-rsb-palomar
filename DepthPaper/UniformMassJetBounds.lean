module

public import DepthPaper.ResidualSpatialJets
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section


/-! Genuine uniform finite-order mass-jet estimates and Leibniz bounds.
No derivative bound is inferred merely from formal differentiation. -/
noncomputable section
open Set
open scoped ContDiff Polynomial
namespace DepthPaper

 theorem norm_iteratedDeriv_mul_le (j:ℕ) {f g:ℝ→ℝ} {m A B:ℝ}
     (hf:ContDiff ℝ ∞ f) (hg:ContDiff ℝ ∞ g) (hA:0≤A) (hB:0≤B)
     (hfa:∀k≤j,‖iteratedDeriv k f m‖≤A) (hgb:∀k≤j,‖iteratedDeriv k g m‖≤B):
     ‖iteratedDeriv j (fun r=>f r*g r) m‖≤(2:ℝ)^j*A*B:=by
   rw [iteratedDeriv_fun_mul (hf.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp))]
   apply (norm_sum_le _ _).trans
   calc
     ∑k∈Finset.range (j+1),‖(j.choose k:ℝ)*iteratedDeriv k f m*iteratedDeriv (j-k) g m‖
       ≤ ∑k∈Finset.range (j+1),(j.choose k:ℝ)*A*B:=by
         apply Finset.sum_le_sum
         intro k hk
         have hkj:k≤j:=by have hh:=Finset.mem_range.mp hk;omega
         rw [norm_mul,norm_mul,Real.norm_of_nonneg (Nat.cast_nonneg _)]
         exact mul_le_mul (mul_le_mul_of_nonneg_left (hfa k hkj) (Nat.cast_nonneg _))
           (hgb (j-k) (Nat.sub_le _ _)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA)
     _=(2:ℝ)^j*A*B:=by
       rw [←Finset.sum_mul,←Finset.sum_mul,←Nat.cast_sum,Nat.sum_range_choose,Nat.cast_pow]
       norm_num

 theorem bivariateMassJet_uniform_bounds (P:Polynomial (Polynomial ℝ)) (J:ℕ) (a b:ℝ):
     ∃K:ℝ,1≤K ∧ ∀j≤J,∀m∈Icc a b,∀t∈Icc (-1:ℝ) 1,‖bivariateMassJet P j m t‖≤K:=by
   induction J with
   | zero=>
     obtain ⟨K,hK,hbound⟩:=bivariateMassJet_uniform_bound P 0 a b
     refine ⟨max K 1,le_max_right _ _,?_⟩
     intro j hj m hm t ht
     have hj0:j=0:=by omega
     subst j
     exact (hbound m hm t ht).trans (le_max_left _ _)
   | succ J ih=>
     obtain ⟨K,hK,hbound⟩:=ih
     obtain ⟨K',hK',hbound'⟩:=bivariateMassJet_uniform_bound P (J+1) a b
     refine ⟨max K K',hK.trans (le_max_left _ _),?_⟩
     intro j hj m hm t ht
     by_cases hj':j≤J
     · exact (hbound j hj' m hm t ht).trans (le_max_left _ _)
     · have he:j=J+1:=by omega
       subst j
       exact (hbound' m hm t ht).trans (le_max_right _ _)

 theorem residual_mass_uniform_jets (J:ℕ) {ε:ℝ} (hε:0<ε):
     ∃K:ℝ,0<K ∧ ∀j≤J,∀m∈Icc ε 1,∀x,
       ‖iteratedDeriv j (fun r=>largeVarianceResidual r x) m‖≤K*Real.exp (-(ε/2)*|x|):=by
   induction J with
   | zero=>
     refine ⟨largeVarianceMassDecayConstant ε 0,largeVarianceMassDecayConstant_pos hε 0,?_⟩
     intro j hj m hm x
     have he:j=0:=by omega
     subst j
     exact iteratedDeriv_largeVarianceResidual_mass_decay 0 hε hm.1 hm.2 x
   | succ J ih=>
     obtain ⟨K,hK,hbound⟩:=ih
     let K':=largeVarianceMassDecayConstant ε (J+1)
     refine ⟨max K K',hK.trans_le (le_max_left _ _),?_⟩
     intro j hj m hm x
     by_cases hj':j≤J
     · exact (hbound j hj' m hm x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
         (Real.exp_pos _).le)
     · have he:j=J+1:=by omega
       subst j
       exact (iteratedDeriv_largeVarianceResidual_mass_decay (J+1) hε hm.1 hm.2 x).trans
         (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)

 theorem iteratedDeriv_coshPower_mass (j:ℕ) (m x:ℝ):
     iteratedDeriv j (fun r=>coshPower r x) m=Real.log (Real.cosh x)^j*coshPower m x:=by
   have he:(fun r=>coshPower r x)=fun r=>Real.exp (Real.log (Real.cosh x)*r):=by
     funext r;simp only [coshPower,mul_comm]
   rw [he,iteratedDeriv_exp_const_mul]
   simp only [coshPower,mul_comm]

end DepthPaper
