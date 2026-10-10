module

public import DepthPaper.LogarithmicTailCost

@[expose] public section


/-! Uniform convergence of the actual logarithmic overlap cutoff to one. -/
noncomputable section
open Set Filter
open scoped Topology
namespace DepthPaper
set_option maxHeartbeats 700000

theorem tendstoUniformlyOn_logarithmicOverlapThreshold {lamlo lamhi L : ℝ}
    (hlo : 0 < lamlo) (hLH : lamlo≤lamhi) (hL : 0 < L) :
    TendstoUniformlyOn (fun p:ℕ=>fun lam:ℝ=>logarithmicOverlapThreshold p lam L)
      (fun _=>1) atTop (Icc lamlo lamhi) := by
  have hratio : Tendsto (fun p:ℕ=>Real.log (p:ℝ)/(p:ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hgap : Tendsto (fun p:ℕ=>2*(|Real.log lamhi|+Real.log (p:ℝ))/(p:ℝ)) atTop (𝓝 0) := by
    have hh:=((tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
      Tendsto (fun p:ℕ=>|Real.log lamhi|/(p:ℝ)) atTop (𝓝 0)).add hratio).const_mul 2
    simp only [add_zero,mul_zero] at hh
    apply hh.congr'
    exact .of_forall fun p=>by ring
  have hlog : ∀ᶠp:ℕ in atTop,1≤L*Real.log (p:ℝ) :=
    ((tendsto_const_mul_atTop_of_pos hL).mpr
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop 1
  have hsmall : ∀ᶠp:ℕ in atTop,L*(Real.log (p:ℝ)/(p:ℝ))<lamlo := by
    have hh:Tendsto (fun p:ℕ=>L*(Real.log (p:ℝ)/(p:ℝ))) atTop (𝓝 0):=by
      simpa only [mul_zero] using hratio.const_mul L
    exact hh.eventually (Iio_mem_nhds hlo)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro e he
  filter_upwards [eventually_ge_atTop (2:ℕ),hlog,hsmall,hgap.eventually (Iio_mem_nhds he)]
    with p hp hl hs hg
  intro lam hlam
  have hpn:0 < (p:ℝ):=by exact_mod_cast (show 0<p by omega)
  have hs' : L*Real.log (p:ℝ)<lam*(p:ℝ) := by
    rw [←mul_div_assoc] at hs
    have hh:=(div_lt_iff₀ hpn).mp hs
    exact hh.trans_le (mul_le_mul_of_nonneg_right hlam.1 hpn.le)
  have ht:=logarithmicOverlapThreshold_lt_one hp (hlo.trans_le hlam.1) hL hs'
  have hb:=logarithmicOverlapThreshold_gap_bound hp (hlo.trans_le hlam.1) hlam.2 hL hl
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr ht.le)]
  exact hb.trans_lt hg

end DepthPaper
