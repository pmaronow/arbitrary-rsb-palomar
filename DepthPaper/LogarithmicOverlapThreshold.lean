module

public import DepthPaper.EndpointStrip
public import DepthPaper.CutoffRecursionDifferenceBound
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section


/-! The actual logarithmic upper-overlap cutoff of Section 4.4.
Its defining power identity and endpoint geometry are uniform in the positive
coefficient window. No stationary-point equation is used. -/
noncomputable section
open Set Filter
open scoped Topology
namespace DepthPaper
set_option maxHeartbeats 900000

def logarithmicOverlapThreshold (p : ℕ) (lam L : ℝ) : ℝ :=
  Real.exp (-Real.log (lam*(p:ℝ)/(L*Real.log (p:ℝ)))/((p-1:ℕ):ℝ))

theorem logarithmicOverlapThreshold_pos (p : ℕ) (lam L : ℝ) :
    0 < logarithmicOverlapThreshold p lam L := Real.exp_pos _

theorem logarithmicOverlapThreshold_power {p : ℕ} (hp : 2≤p)
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L) :
    lam*(p:ℝ)*(logarithmicOverlapThreshold p lam L)^(p-1)=L*Real.log (p:ℝ) := by
  have hn : ((p-1:ℕ):ℝ)≠0 := by exact_mod_cast (show p-1≠0 by omega)
  have hpn : 0 < (p:ℝ) := by exact_mod_cast (show 0<p by omega)
  have hlog : 0 < Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast (show 1<p by omega))
  have hratio : 0 < lam*(p:ℝ)/(L*Real.log (p:ℝ)) := by positivity
  unfold logarithmicOverlapThreshold
  rw [←Real.exp_nat_mul]
  have he : ((p-1:ℕ):ℝ)*(-Real.log (lam*(p:ℝ)/(L*Real.log (p:ℝ)))/((p-1:ℕ):ℝ))=
      -Real.log (lam*(p:ℝ)/(L*Real.log (p:ℝ))) := by field_simp
  rw [he,Real.exp_neg,Real.exp_log hratio]
  field_simp

theorem logarithmicOverlapThreshold_lt_one {p : ℕ} (hp : 2≤p)
    {lam L : ℝ} (hlam : 0 < lam) (hL : 0 < L)
    (hsmall : L*Real.log (p:ℝ)<lam*(p:ℝ)) :
    logarithmicOverlapThreshold p lam L<1 := by
  have hn : 0 < ((p-1:ℕ):ℝ) := by exact_mod_cast (show 0<p-1 by omega)
  have hlog : 0 < Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast (show 1<p by omega))
  have hr : 1<lam*(p:ℝ)/(L*Real.log (p:ℝ)) := (lt_div_iff₀ (by positivity)).mpr (by simpa using hsmall)
  unfold logarithmicOverlapThreshold
  exact Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos (Real.log_pos hr)) hn)

theorem logarithmicOverlapThreshold_above_cutoff {p : ℕ} (hp : 2≤p)
    {qc lam L : ℝ} (hc : 0≤qc) (hlam : 0 < lam) (hL : 0 < L)
    (hcut : lam*(p:ℝ)*qc^(p-1)<L*Real.log (p:ℝ)) :
    qc<logarithmicOverlapThreshold p lam L := by
  apply lt_of_pow_lt_pow_left₀ (p-1) (logarithmicOverlapThreshold_pos p lam L).le
  have he:=logarithmicOverlapThreshold_power hp hlam hL
  have hpn : 0 < lam*(p:ℝ) := by positivity
  nlinarith

theorem logarithmicOverlapThreshold_below_strip {p : ℕ} (hp : 2≤p)
    {cQ CQ lam L Q : ℝ} (hcQ : 0 < cQ) (hlam : 0 < lam) (hL : 0 < L)
    (hQ : Q∈endpointStrip cQ CQ p)
    (hsmall : L*Real.log (p:ℝ)<lam*(p:ℝ)/2)
    (hgap : (p:ℝ)*Real.exp (-cQ*(p:ℝ))<1/2) :
    logarithmicOverlapThreshold p lam L<Q := by
  have hQu:=endpointStrip_mem_unit hcQ p hQ
  have hpow : 1/2<Q^(p-1) := by
    have hh:=one_sub_pow_bound ⟨hQu.1,hQu.2.le⟩ (p-1)
    have hn : ((p-1:ℕ):ℝ)≤(p:ℝ) := by exact_mod_cast Nat.sub_le p 1
    have hb:=mul_le_mul hn (endpointStrip_distance_bound p hQ)
      (sub_nonneg.mpr hQu.2.le) (Nat.cast_nonneg p)
    linarith
  have hth : (logarithmicOverlapThreshold p lam L)^(p-1)<1/2 := by
    have he:=logarithmicOverlapThreshold_power hp hlam hL
    have hpn : 0 < lam*(p:ℝ) := by positivity
    nlinarith
  exact lt_of_pow_lt_pow_left₀ (p-1) hQu.1 (hth.trans hpow)

theorem logarithmicOverlapThreshold_geometry_eventually {qc cQ CQ lamlo lamhi L : ℝ}
    (hc : qc∈Ioo (0:ℝ) 1) (hcQ : 0 < cQ) (hlo : 0 < lamlo)
    (hLH : lamlo≤lamhi) (hL : 0 < L) :
    ∀ᶠp:ℕ in atTop,∀lam∈Icc lamlo lamhi,∀Q:ℝ,Q∈endpointStrip cQ CQ p→
      qc<logarithmicOverlapThreshold p lam L ∧ logarithmicOverlapThreshold p lam L<Q := by
  have hlog : Tendsto (fun p:ℕ=>Real.log (p:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun p:ℕ=>Real.log (p:ℝ)/(p:ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠp:ℕ in atTop,L*(Real.log (p:ℝ)/(p:ℝ))<lamlo/2 := by
    have hh:=hratio.const_mul L
    have hh':Tendsto (fun p:ℕ=>L*(Real.log (p:ℝ)/(p:ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using hh
    exact hh'.eventually (Iio_mem_nhds (by positivity : (0:ℝ)<lamlo/2))
  have hcut : ∀ᶠp:ℕ in atTop,
      lamhi*(Real.exp (-Real.log qc)/(-Real.log qc))<L*Real.log (p:ℝ) :=
    ((tendsto_const_mul_atTop_of_pos hL).mpr hlog).eventually_gt_atTop _
  have hgap : ∀ᶠp:ℕ in atTop,(p:ℝ)*Real.exp (-cQ*(p:ℝ))<1/2 := by
    have hh:=tendsto_nat_polynomial_exp 1 cQ 1 hcQ
    simpa only [one_mul,pow_one] using hh.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2))
  filter_upwards [eventually_ge_atTop (2:ℕ),hsmall,hcut,hgap] with p hp hs hc' hg
  intro lam hlam Q hQ
  have hpn : 0 < (p:ℝ) := by exact_mod_cast (show 0<p by omega)
  have hs' : L*Real.log (p:ℝ)<lam*(p:ℝ)/2 := by
    have hl := mul_le_mul_of_nonneg_right hlam.1 hpn.le
    rw [←mul_div_assoc] at hs
    have hd := (div_lt_iff₀ hpn).mp hs
    nlinarith
  have hc'' : lam*(p:ℝ)*qc^(p-1)<L*Real.log (p:ℝ) := by
    have hb:=nat_mul_pow_sub_one_bound hc p (by omega)
    have h0 : 0≤(p:ℝ)*qc^(p-1) := mul_nonneg (Nat.cast_nonneg p) (pow_nonneg hc.1.le _)
    have hh := mul_le_mul_of_nonneg_left hb (hlo.le.trans hLH)
    have hl := mul_le_mul_of_nonneg_right hlam.2 h0
    nlinarith
  exact ⟨logarithmicOverlapThreshold_above_cutoff hp hc.1.le (hlo.trans_le hlam.1) hL hc'',
    logarithmicOverlapThreshold_below_strip hp hcQ (hlo.trans_le hlam.1) hL hQ hs' hg⟩

end DepthPaper
