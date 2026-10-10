module

public import GeneralDepthPaper.EndpointVarianceJets

@[expose] public section


/-! Actual mixed parameter jets of the high-spin term on a fixed cutoff.
The cutoff power supplies the exponential smallness, with no limiting
statement or derivative bound postulated as an input. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 800000

 theorem norm_iteratedDeriv_pow_cutoff (p j : ℕ) {qc x : ℝ}
    (hc : 0 ≤ qc) (hx : x∈Icc (0:ℝ) qc) :
    ‖iteratedDeriv j (fun y : ℝ => y^p) x‖ ≤ (p:ℝ)^j*qc^(p-j) := by
  rw [iteratedDeriv_pow,norm_mul,norm_pow,
    Real.norm_of_nonneg (show 0 ≤ (p.descFactorial j:ℝ) from Nat.cast_nonneg _),
    Real.norm_of_nonneg hx.1]
  have hd : (p.descFactorial j:ℝ) ≤ (p:ℝ)^j := by
    exact_mod_cast Nat.descFactorial_le_pow p j
  exact mul_le_mul hd (pow_le_pow_left₀ hx.1 hx.2 _) (pow_nonneg hx.1 _)
    (pow_nonneg (Nat.cast_nonneg _) _)

 theorem norm_iteratedFDeriv_snd_pow_cutoff (p j : ℕ) {qc : ℝ}
    (hc : 0 ≤ qc) {w : ℝ×ℝ} (hx : w.2∈Icc (0:ℝ) qc) :
    ‖iteratedFDeriv ℝ j (fun y : ℝ×ℝ => y.2^p) w‖ ≤ (p:ℝ)^j*qc^(p-j) :=
  (norm_iteratedFDeriv_comp_contraction (ContinuousLinearMap.snd ℝ ℝ ℝ)
    (ContinuousLinearMap.norm_snd_le ..) (fun x => x^p) (contDiff_id.pow p) j w).trans
      (norm_iteratedDeriv_pow_cutoff p j hc hx)

 theorem norm_iteratedFDeriv_highDegree_value_cutoff (p j : ℕ) (hp : 1 ≤ p)
    {qc L : ℝ} (hc : qc∈Icc (0:ℝ) 1) {w : ℝ×ℝ}
    (hlam : w.1∈Icc (0:ℝ) L) (hx : w.2∈Icc (0:ℝ) qc) :
    ‖iteratedFDeriv ℝ j (fun y : ℝ×ℝ => y.1*y.2^p) w‖ ≤
      (2:ℝ)^j*max L 1*(p:ℝ)^j*qc^(p-j) := by
  have hbase : ContDiff ℝ ∞ (fun y : ℝ×ℝ => y.1) := contDiff_fst
  have hpow : ContDiff ℝ ∞ (fun y : ℝ×ℝ => y.2^p) := contDiff_snd.pow p
  apply (norm_iteratedFDeriv_mul_le hbase hpow w (by simp)).trans
  have hm : 0 ≤ max L 1 := zero_le_one.trans (le_max_right _ _)
  have hs : (∑i∈Finset.range (j+1),(j.choose i:ℝ)*max L 1*((p:ℝ)^j*qc^(p-j)))=
      (2:ℝ)^j*max L 1*(p:ℝ)^j*qc^(p-j) := by
    rw [←Finset.sum_mul,←Finset.sum_mul,←Nat.cast_sum,Nat.sum_range_choose,Nat.cast_pow,Nat.cast_ofNat]
    ring
  rw [←hs]
  apply Finset.sum_le_sum
  intro i hi
  have hpp : (p:ℝ)^(j-i) ≤ (p:ℝ)^j :=
    pow_le_pow_right₀ (by exact_mod_cast hp) (Nat.sub_le _ _)
  have hqc : qc^(p-(j-i)) ≤ qc^(p-j) :=
    pow_right_anti₀ hc.1 hc.2 (by omega)
  have hb := (norm_iteratedFDeriv_snd_pow_cutoff p (j-i) hc.1 hx).trans
    (mul_le_mul hpp hqc (pow_nonneg hc.1 _) (pow_nonneg (Nat.cast_nonneg _) _))
  have hh := mul_le_mul (norm_iteratedFDeriv_fst_window i hlam w.2) hb (norm_nonneg _) hm
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (j.choose i))

 theorem pow_cutoff_exponential {qc : ℝ} (hc : 0 < qc) (p j : ℕ) (hp : j ≤ p) :
    qc^(p-j) = qc^(- (j:ℤ))*Real.exp (Real.log qc*(p:ℝ)) := by
  have he : Real.exp (Real.log qc*(p:ℝ))=qc^p := by
    rw [mul_comm (Real.log qc),Real.exp_nat_mul,Real.exp_log hc]
  rw [he,zpow_neg,zpow_natCast,pow_sub₀ qc hc.ne' hp]
  ring

 theorem highDegree_value_mixed_exponential_bound {qc L : ℝ} (hc : qc∈Ioo (0:ℝ) 1)
    (j : ℕ) : ∃C c : ℝ,0 ≤ C ∧ 0 < c ∧ ∀p:ℕ,1 ≤ p → j ≤ p →
      ∀w:ℝ×ℝ,w.1∈Icc (0:ℝ) L → w.2∈Icc (0:ℝ) qc →
      ‖iteratedFDeriv ℝ j (fun y : ℝ×ℝ => y.1*y.2^p) w‖ ≤
        C*(p:ℝ)^j*Real.exp (-c*(p:ℝ)) := by
  refine ⟨(2:ℝ)^j*max L 1*qc^(- (j:ℤ)),-Real.log qc,
    mul_nonneg (mul_nonneg (by positivity) (zero_le_one.trans (le_max_right _ _)))
      (le_of_lt (zpow_pos hc.1 _)),
    neg_pos.mpr (Real.log_neg hc.1 hc.2),?_⟩
  intro p hp hj w hlam hx
  have H := norm_iteratedFDeriv_highDegree_value_cutoff p j hp ⟨hc.1.le,hc.2.le⟩ hlam hx
  rw [pow_cutoff_exponential hc.1 p j hj] at H
  convert H using 1 <;> ring


theorem highDegree_first_mixed_exponential_bound {qc L : ℝ} (hc : qc∈Ioo (0:ℝ) 1)
    (j : ℕ) : ∃C c : ℝ,0 ≤ C ∧ 0 < c ∧ ∀p:ℕ,2 ≤ p → j+1 ≤ p →
      ∀w:ℝ×ℝ,w.1∈Icc (0:ℝ) L → w.2∈Icc (0:ℝ) qc →
      ‖iteratedFDeriv ℝ j (fun y : ℝ×ℝ => y.1*(p:ℝ)*y.2^(p-1)) w‖ ≤
        C*(p:ℝ)^(j+1)*Real.exp (-c*(p:ℝ)) := by
  refine ⟨(2:ℝ)^j*max L 1*qc^(- ((j+1):ℤ)),-Real.log qc,
    mul_nonneg (mul_nonneg (by positivity) (zero_le_one.trans (le_max_right _ _)))
      (le_of_lt (zpow_pos hc.1 _)),neg_pos.mpr (Real.log_neg hc.1 hc.2),?_⟩
  intro p hp hj w hlam hx
  have H := norm_iteratedFDeriv_highDegree_value_cutoff (p-1) j (by omega)
    ⟨hc.1.le,hc.2.le⟩ hlam hx
  have hpow : ((p-1:ℕ):ℝ)^j ≤ (p:ℝ)^j :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le p 1) j
  have H' := H.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow
      (mul_nonneg (pow_nonneg (by norm_num) _) (zero_le_one.trans (le_max_right _ _))))
    (pow_nonneg hc.1.le _))
  have he : (fun y : ℝ×ℝ => y.1*(p:ℝ)*y.2^(p-1))=
      (fun y : ℝ×ℝ => (p:ℝ) • (y.1*y.2^(p-1))) := by funext y;simp only [smul_eq_mul];ring
  have hf : ContDiff ℝ ∞ (fun y : ℝ×ℝ => y.1*y.2^(p-1)) :=
    contDiff_fst.mul (contDiff_snd.pow (p-1))
  rw [he,iteratedFDeriv_const_smul_apply' (hf.of_le (show (j:ℕ∞ω) ≤ ∞ by simp)).contDiffAt,
    norm_smul,Real.norm_of_nonneg (show 0 ≤ (p:ℝ) from Nat.cast_nonneg _)]
  have heq : p-1-j=p-(j+1) := by omega
  rw [heq,pow_cutoff_exponential hc.1 p (j+1) hj] at H'
  have H'' := mul_le_mul_of_nonneg_left H' (show 0 ≤ (p:ℝ) from Nat.cast_nonneg _)
  simp only [Nat.cast_add,Nat.cast_one] at H'' ⊢
  convert H'' using 1 <;> rw [pow_succ] <;> ring

end GeneralDepthPaper
