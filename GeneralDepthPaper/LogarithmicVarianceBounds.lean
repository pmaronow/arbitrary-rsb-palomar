module

public import GeneralDepthPaper.LogarithmicOverlapThreshold
public import GeneralDepthPaper.EndpointDeficitTwoSided

@[expose] public section


/-! Actual elapsed and remaining variance at the logarithmic overlap.
The cutoff-state law does not enter these uniform polynomial estimates. -/
noncomputable section
open Set Filter
open scoped Topology
namespace GeneralDepthPaper
set_option maxHeartbeats 800000

theorem logarithmic_elapsed_variance_lower (Ξ : AdmissibleCovariance)
    {qc lamhi L : ℝ} (hc : qc∈Ioo (0:ℝ) 1) (hL : 0 < L)
    (p : ℕ) (hp : 4≤p) (he : Even p) (hn : p∉Ξ.degrees)
    {lam : ℝ} (hlam : 0 < lam) (hhi : lam≤lamhi) :
    L*Real.log (p:ℝ)-cutoffDriverVarianceBound Ξ qc lamhi≤
      (Ξ.addHighDegree p hp he hn lam hlam).first (logarithmicOverlapThreshold p lam L)-
        (Ξ.addHighDegree p hp he hn lam hlam).first qc := by
  have hvar:=highDegree_cutoff_variance_le Ξ hc (hlam.le.trans hhi) p hp he hn lam hlam hhi
  have hq0:0≤logarithmicOverlapThreshold p lam L:=(logarithmicOverlapThreshold_pos ..).le
  have hb:=Ξ.first_nonneg hq0
  rw [Ξ.addHighDegree_first]
  have ht:=logarithmicOverlapThreshold_power (by omega : 2≤p) hlam hL
  linarith

theorem logarithmic_remaining_variance_lower (Ξ : AdmissibleCovariance)
    {cQ CQ lam L : ℝ} (hcQ : 0 < cQ) (hlam : 0 < lam) (hL : 0 < L)
    (p : ℕ) (hp : 4≤p) (he : Even p) (hn : p∉Ξ.degrees) {Q : ℝ}
    (hQ : Q∈endpointStrip cQ CQ p)
    (hsmall : L*Real.log (p:ℝ)<lam*(p:ℝ)/4)
    (hgap : (p:ℝ)*Real.exp (-cQ*(p:ℝ))<1/2) :
    lam*(p:ℝ)/4 <
      (Ξ.addHighDegree p hp he hn lam hlam).first Q-
        (Ξ.addHighDegree p hp he hn lam hlam).first (logarithmicOverlapThreshold p lam L) := by
  have hpn : 0 < (p:ℝ) := by exact_mod_cast (show 0<p by omega)
  have hqQ:=logarithmicOverlapThreshold_below_strip (by omega : 2≤p) hcQ hlam hL hQ
    (by nlinarith) hgap
  have hQu:=endpointStrip_mem_unit hcQ p hQ
  have hbase:=Ξ.first_strictMonoOn.monotoneOn
    (logarithmicOverlapThreshold_pos p lam L).le hQu.1 hqQ.le
  have hpow : 1/2<Q^(p-1) := by
    have hh:=one_sub_pow_bound ⟨hQu.1,hQu.2.le⟩ (p-1)
    have hn' : ((p-1:ℕ):ℝ)≤(p:ℝ) := by exact_mod_cast Nat.sub_le p 1
    have hb:=mul_le_mul hn' (endpointStrip_distance_bound p hQ)
      (sub_nonneg.mpr hQu.2.le) (Nat.cast_nonneg p)
    linarith
  rw [Ξ.addHighDegree_first,Ξ.addHighDegree_first]
  have ht:=logarithmicOverlapThreshold_power (by omega : 2≤p) hlam hL
  have hm:=mul_lt_mul_of_pos_left hpow (mul_pos hlam hpn)
  nlinarith

theorem logarithmic_variance_bounds_eventually (Ξ : AdmissibleCovariance)
    {qc cQ CQ lamlo lamhi L : ℝ} (hc : qc∈Ioo (0:ℝ) 1) (hcQ : 0 < cQ)
    (hlo : 0 < lamlo) (hLH : lamlo≤lamhi) (hL : 0 < L) :
    ∀ᶠp:ℕ in atTop,∀hp:4≤p,
      ∀he:Even p,∀hn:p∉Ξ.degrees,∀lam:ℝ,∀hlam:lam∈Icc lamlo lamhi,∀Q:ℝ,
        Q∈endpointStrip cQ CQ p→
          L*Real.log (p:ℝ)-cutoffDriverVarianceBound Ξ qc lamhi≤
            (Ξ.addHighDegree p hp he hn lam (hlo.trans_le hlam.1)).first
              (logarithmicOverlapThreshold p lam L)-
            (Ξ.addHighDegree p hp he hn lam (hlo.trans_le hlam.1)).first qc ∧
          lamlo*(p:ℝ)/4 <
            (Ξ.addHighDegree p hp he hn lam (hlo.trans_le hlam.1)).first Q-
            (Ξ.addHighDegree p hp he hn lam (hlo.trans_le hlam.1)).first
              (logarithmicOverlapThreshold p lam L) := by
  have hratio : Tendsto (fun p:ℕ=>L*(Real.log (p:ℝ)/(p:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def,id_eq] using
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul L
  have hs:=hratio.eventually (Iio_mem_nhds (by positivity : (0:ℝ)<lamlo/4))
  have hg : ∀ᶠp:ℕ in atTop,(p:ℝ)*Real.exp (-cQ*(p:ℝ))<1/2 := by
    simpa only [one_mul,pow_one] using
      (tendsto_nat_polynomial_exp 1 cQ 1 hcQ).eventually
        (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2))
  filter_upwards [eventually_ge_atTop (4:ℕ),hs,hg] with p hp hs hg
  intro hp' he hn lam hlam Q hQ
  have hpn : 0 < (p:ℝ) := by exact_mod_cast (show 0<p by omega)
  have hs' : L*Real.log (p:ℝ)<lam*(p:ℝ)/4 := by
    rw [←mul_div_assoc] at hs
    have hd := (div_lt_iff₀ hpn).mp hs
    have hh:=mul_le_mul_of_nonneg_right hlam.1 hpn.le
    nlinarith
  have hh:=logarithmic_remaining_variance_lower Ξ hcQ (hlo.trans_le hlam.1) hL
    p hp he hn hQ hs' hg
  exact ⟨logarithmic_elapsed_variance_lower Ξ hc hL p hp he hn (hlo.trans_le hlam.1) hlam.2,
    lt_of_le_of_lt (by gcongr;exact hlam.1) hh⟩

end GeneralDepthPaper
