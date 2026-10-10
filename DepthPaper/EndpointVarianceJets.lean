module

public import DepthPaper.EndpointStrip
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section


/-! Actual total parameter derivatives of the endpoint variance. Bounds
hold on the entire unit square, hence on the exponentially thin strip.
Every derivative of total order k is at most C_k p^(k+1). -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace DepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

theorem norm_iteratedFDeriv_comp_contraction {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (L : E→L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    (f : ℝ→ℝ) (hf : ContDiff ℝ ∞ f) (j : ℕ) (w : E) :
    ‖iteratedFDeriv ℝ j (fun y=>f (L y)) w‖ ≤ ‖iteratedDeriv j f (L w)‖ := by
  change ‖iteratedFDeriv ℝ j (f ∘ L) w‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hf w (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hp : (∏i:Fin j,‖L‖) ≤ 1:=
    Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun _ _=>hL)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (norm_nonneg (iteratedDeriv j f (L w)))

theorem norm_iteratedDeriv_pow_unit (p j : ℕ) {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    ‖iteratedDeriv j (fun y:ℝ=>y^p) x‖ ≤ (p:ℝ)^j := by
  rw [iteratedDeriv_pow,norm_mul,norm_pow,
    Real.norm_of_nonneg (show 0 ≤ (p.descFactorial j:ℝ) from Nat.cast_nonneg _),
    Real.norm_of_nonneg hx.1]
  have hd : (p.descFactorial j:ℝ) ≤ (p:ℝ)^j:=by exact_mod_cast Nat.descFactorial_le_pow p j
  exact (mul_le_mul hd (pow_le_one₀ hx.1 hx.2) (pow_nonneg hx.1 _) (pow_nonneg (Nat.cast_nonneg p) _)).trans_eq
    (mul_one _)

theorem norm_iteratedFDeriv_fst_window (j : ℕ) {lam L : ℝ} (hlam : lam∈Icc (0:ℝ) L)
    (Q : ℝ) : ‖iteratedFDeriv ℝ j (fun w:ℝ×ℝ=>w.1) (lam,Q)‖ ≤ max L 1 := by
  have h:=norm_iteratedFDeriv_comp_contraction (ContinuousLinearMap.fst ℝ ℝ ℝ)
    (ContinuousLinearMap.norm_fst_le ..) id contDiff_id j (lam,Q)
  apply h.trans
  rw [iteratedDeriv_id]
  split_ifs
  · change ‖lam‖ ≤ max L 1
    rw [Real.norm_of_nonneg hlam.1]
    exact hlam.2.trans (le_max_left _ _)
  · norm_num only [norm_one]
    exact le_max_right _ _
  · simp only [norm_zero]
    exact zero_le_one.trans (le_max_right _ _)

theorem norm_iteratedFDeriv_snd_pow_unit (p j : ℕ) {w : ℝ×ℝ} (hw : w.2∈Icc (0:ℝ) 1) :
    ‖iteratedFDeriv ℝ j (fun y:ℝ×ℝ=>y.2^p) w‖ ≤ (p:ℝ)^j :=
  (norm_iteratedFDeriv_comp_contraction (ContinuousLinearMap.snd ℝ ℝ ℝ)
    (ContinuousLinearMap.norm_snd_le ..) (fun x=>x^p) (contDiff_id.pow p) j w).trans
      (norm_iteratedDeriv_pow_unit p j hw)

theorem norm_iteratedFDeriv_const_le_power (p j : ℕ) (hp : 1 ≤ p) {c : ℝ} (hc : ‖c‖ ≤ 1)
    (w : ℝ×ℝ) : ‖iteratedFDeriv ℝ j (fun _:ℝ×ℝ=>c) w‖ ≤ (p:ℝ)^j := by
  cases j with
  | zero=>simpa only [norm_iteratedFDeriv_zero,pow_zero] using hc
  | succ j=>simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero];positivity

theorem norm_iteratedFDeriv_snd_pow_difference (p j : ℕ) (hp : 1 ≤ p)
    {qc : ℝ} (hc : qc∈Icc (0:ℝ) 1) {w : ℝ×ℝ} (hw : w.2∈Icc (0:ℝ) 1) :
    ‖iteratedFDeriv ℝ j (fun y:ℝ×ℝ=>y.2^(p-1)-qc^(p-1)) w‖ ≤ 2*(p:ℝ)^j := by
  have hpow : ‖iteratedFDeriv ℝ j (fun y:ℝ×ℝ=>y.2^(p-1)) w‖ ≤ (p:ℝ)^j :=
    (norm_iteratedFDeriv_snd_pow_unit (p-1) j hw).trans
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le p 1) j)
  have hconst := norm_iteratedFDeriv_const_le_power p j hp
    (c:=qc^(p-1)) (by rw [Real.norm_of_nonneg (pow_nonneg hc.1 _)];exact pow_le_one₀ hc.1 hc.2) w
  change ‖iteratedFDeriv ℝ j ((fun y:ℝ×ℝ=>y.2^(p-1))-(fun _=>qc^(p-1))) w‖ ≤ _
  have hq : ContDiff ℝ ∞ (fun y : ℝ × ℝ => y.2^(p-1)) := contDiff_snd.pow (p-1)
  have hcst : ContDiff ℝ ∞ (fun _ : ℝ × ℝ => qc^(p-1)) := contDiff_const
  rw [iteratedFDeriv_sub_apply (hq.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt
    (hcst.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt]
  exact (norm_sub_le _ _).trans (by linarith)

theorem norm_iteratedFDeriv_endpoint_polynomial_le (p j : ℕ) (hp : 1 ≤ p)
    {qc L : ℝ} (hc : qc∈Icc (0:ℝ) 1) {w : ℝ×ℝ}
    (hlam : w.1∈Icc (0:ℝ) L) (hQ : w.2∈Icc (0:ℝ) 1) :
    ‖iteratedFDeriv ℝ j (fun y:ℝ×ℝ=>y.1*(p:ℝ)*(y.2^(p-1)-qc^(p-1))) w‖ ≤ 
      2*max L 1*(2:ℝ)^j*(p:ℝ)^(j+1) := by
  let f:ℝ×ℝ→ℝ:=fun y=>y.1
  let g:ℝ×ℝ→ℝ:=fun y=>y.2^(p-1)-qc^(p-1)
  have hf : ContDiff ℝ ∞ f:=contDiff_fst
  have hg : ContDiff ℝ ∞ g:=(contDiff_snd.pow (p-1)).sub contDiff_const
  have hm0 : 0 ≤ max L 1:=zero_le_one.trans (le_max_right _ _)
  have hb : ‖iteratedFDeriv ℝ j (fun y=>f y*g y) w‖ ≤ 
      (2:ℝ)^j*max L 1*(2*(p:ℝ)^j) := by
    apply (norm_iteratedFDeriv_mul_le hf hg w (by simp)).trans
    have hsum : (∑i∈Finset.range (j+1),(j.choose i:ℝ)*max L 1*(2*(p:ℝ)^j))=
        (2:ℝ)^j*max L 1*(2*(p:ℝ)^j) := by
      rw [←Finset.sum_mul,←Finset.sum_mul,←Nat.cast_sum,Nat.sum_range_choose,Nat.cast_pow,Nat.cast_ofNat]
    rw [←hsum]
    apply Finset.sum_le_sum
    intro i hi
    have hgB : ‖iteratedFDeriv ℝ (j-i) g w‖ ≤ 2*(p:ℝ)^j :=
      (norm_iteratedFDeriv_snd_pow_difference p (j-i) hp hc hQ).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by exact_mod_cast hp : (1:ℝ) ≤ p)
          (Nat.sub_le _ _)) (by norm_num))
    have hh:=mul_le_mul (norm_iteratedFDeriv_fst_window i hlam w.2) hgB (norm_nonneg _) hm0
    simpa only [mul_assoc,f] using mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (j.choose i))
  have he : (fun y:ℝ×ℝ=>y.1*(p:ℝ)*(y.2^(p-1)-qc^(p-1)))=
      (fun y=>(p:ℝ) • (f y*g y)) := by funext y;dsimp only [f,g];simp only [smul_eq_mul];ring
  rw [he,iteratedFDeriv_const_smul_apply' ((hf.mul hg).of_le (by simp)).contDiffAt,norm_smul,
    Real.norm_of_nonneg (Nat.cast_nonneg p)]
  have h:=mul_le_mul_of_nonneg_left hb (show 0 ≤ (p:ℝ) from Nat.cast_nonneg p)
  convert! h using 1 <;> rw [pow_succ] <;> ring

theorem endpointVarianceExpression_jet_bound (Ξ : AdmissibleCovariance) {qc L : ℝ}
    (hc : qc∈Icc (0:ℝ) 1) (j : ℕ) :
    ∃C:ℝ,0 ≤ C ∧ ∀p:ℕ,1 ≤ p→∀w:ℝ×ℝ,w.1∈Icc (0:ℝ) L→w.2∈Icc (0:ℝ) 1→
      ‖iteratedFDeriv ℝ j (endpointVarianceExpression Ξ p qc) w‖ ≤ C*(p:ℝ)^(j+1) := by
  let f:ℝ→ℝ:=fun x=>Ξ.first x-Ξ.first qc
  have hf : ContDiff ℝ ∞ f:=Ξ.contDiff_first.sub contDiff_const
  obtain ⟨B,hB⟩:=isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuous_iteratedDeriv j (by simp)).continuousOn
  let D:ℝ:=max B 0
  have hD : 0 ≤ D:=le_max_right _ _
  refine ⟨D+2*max L 1*(2:ℝ)^j,by dsimp only [D];positivity,?_⟩
  intro p hp w hlam hQ
  have hfB : ‖iteratedFDeriv ℝ j (fun y:ℝ×ℝ=>f y.2) w‖ ≤ D :=
    (norm_iteratedFDeriv_comp_contraction (ContinuousLinearMap.snd ℝ ℝ ℝ)
      (ContinuousLinearMap.norm_snd_le ..) f hf j w).trans ((hB w.2 hQ).trans (le_max_left _ _))
  change ‖iteratedFDeriv ℝ j ((fun y:ℝ×ℝ=>f y.2)+
    (fun y=>y.1*(p:ℝ)*(y.2^(p-1)-qc^(p-1)))) w‖ ≤ _
  have hbase : ContDiff ℝ ∞ (fun y : ℝ × ℝ => f y.2) := hf.comp contDiff_snd
  have hpert : ContDiff ℝ ∞ (fun y : ℝ × ℝ => y.1*(p:ℝ)*(y.2^(p-1)-qc^(p-1))) :=
    (contDiff_fst.mul contDiff_const).mul ((contDiff_snd.pow (p-1)).sub contDiff_const)
  rw [iteratedFDeriv_add_apply (hbase.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt
    (hpert.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)).contDiffAt]
  apply (norm_add_le _ _).trans
  have hgB:=norm_iteratedFDeriv_endpoint_polynomial_le p j hp hc hlam hQ
  have hDp : D ≤ D*(p:ℝ)^(j+1):=by
    have hpow : (1:ℝ) ≤ (p:ℝ)^(j+1):=one_le_pow₀ (by exact_mod_cast hp)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hD
  nlinarith

end DepthPaper
