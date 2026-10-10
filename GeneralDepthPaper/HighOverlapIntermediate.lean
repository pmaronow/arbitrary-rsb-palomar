module

public import GeneralDepthPaper.LogarithmicTailCost
public import GeneralDepthPaper.WeakVariationContinuity

@[expose] public section


/-! The literal intermediate-region first-variation estimate. Its only
candidate-specific input is the negative cutoff value supplied by the lower
geometry lemma; the selected-state and polynomial integration inputs are proved. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace GeneralDepthPaper
set_option maxHeartbeats 1200000

def highDegreeTailPrimitive (p : ℕ) (q : ℝ) : ℝ :=
  (p:ℝ)*q^(p-1)-((p-1:ℕ):ℝ)*q^p

theorem hasDerivAt_highDegreeTailPrimitive (p : ℕ) (hp : 2≤p) (q : ℝ) :
    HasDerivAt (highDegreeTailPrimitive p)
      ((p:ℝ)*((p-1:ℕ):ℝ)*q^(p-2)*(1-q)) q := by
  have hd:=(((hasDerivAt_id q).pow (p-1)).const_mul (p:ℝ)).sub
    (((hasDerivAt_id q).pow p).const_mul ((p-1:ℕ):ℝ))
  simp only [id_eq,mul_one] at hd
  have hpow : q^(p-1)=q^(p-2)*q := by rw [show p-1=p-2+1 by omega,pow_succ]
  convert hd using 1
  · rfl
  · rw [show p-1-1=p-2 by omega]
    rw [hpow]
    ring

theorem highDegreeTailPrimitive_nonneg {p : ℕ} (hp : 1≤p) {q : ℝ}
    (hq : q∈Icc (0:ℝ) 1) : 0≤highDegreeTailPrimitive p q := by
  have he : p=p-1+1 := by omega
  have hn : ((p-1:ℕ):ℝ)≤(p:ℝ) := by exact_mod_cast Nat.sub_le p 1
  have hc:=mul_le_mul_of_nonneg_left hq.2 (Nat.cast_nonneg (p-1))
  have hpq : 0≤q^(p-1) := pow_nonneg hq.1 _
  have hfactor : 0≤(p:ℝ)-((p-1:ℕ):ℝ)*q := by linarith
  have hh:=mul_nonneg hpq hfactor
  unfold highDegreeTailPrimitive
  have hpow : q^p=q^(p-1)*q := by conv_lhs => rw [he,pow_succ]
  rw [hpow]
  nlinarith

theorem firstVariation_high_degree_increment_bound (Ξ : AdmissibleCovariance)
    (p : ℕ) (hp : 4≤p) (he : Even p) (hn : p∉Ξ.degrees)
    {lam : ℝ} (hlam : 0 < lam) (μ : ParisiMeasure) {a b : ℝ}
    (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc a 1) :
    firstVariation (Ξ.addHighDegree p hp he hn lam hlam) μ b≤
      firstVariation (Ξ.addHighDegree p hp he hn lam hlam) μ a+
        (1/2:ℝ)*(∫s in a..1,(1-s)*Ξ.second s)+
          (lam/2)*highDegreeTailPrimitive p b := by
  let X:=Ξ.addHighDegree p hp he hn lam hlam
  have hbu : b∈Icc (0:ℝ) 1:=⟨ha.1.trans hb.1,hb.2⟩
  have hi : IntervalIntegrable (firstVariationDerivative X μ) volume a b :=
    ((contDiffOn_firstVariationDerivative X μ).continuousOn.mono
      (Icc_subset_Icc ha.1 hb.2)).intervalIntegrable_of_Icc hb.1
  have hiu : IntervalIntegrable (fun s=>(1/2:ℝ)*X.second s*(1-s)) volume a b := by
    have hc:Continuous (fun s=>(1/2:ℝ)*X.second s*(1-s)) :=
      (continuous_const.mul X.continuous_second).mul (continuous_const.sub continuous_id)
    exact hc.intervalIntegrable _ _
  have him:=intervalIntegral.integral_mono_on hb.1 hi hiu (fun s hs=>by
    have hsu : s∈Icc (0:ℝ) 1:=⟨ha.1.trans hs.1,hs.2.trans hb.2⟩
    unfold firstVariationDerivative
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right (Gamma_le_one X μ s) s)
      (mul_nonneg (by norm_num) (X.second_nonneg hsu.1)))
  have hdecomp : (∫s in a..b,(1/2:ℝ)*X.second s*(1-s))=
      (1/2:ℝ)*(∫s in a..b,(1-s)*Ξ.second s)+
        (lam/2)*(highDegreeTailPrimitive p b-highDegreeTailPrimitive p a) := by
    have hid : (∫s in a..b,(p:ℝ)*((p-1:ℕ):ℝ)*s^(p-2)*(1-s))=
        highDegreeTailPrimitive p b-highDegreeTailPrimitive p a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s _=>hasDerivAt_highDegreeTailPrimitive p (by omega) s)
        (by have hc:Continuous (fun s=>(p:ℝ)*((p-1:ℕ):ℝ)*s^(p-2)*(1-s)):=by fun_prop
            exact hc.intervalIntegrable _ _)
    have hc1:Continuous (fun s=>(1/2:ℝ)*((1-s)*Ξ.second s)):=
      continuous_const.mul ((continuous_const.sub continuous_id).mul Ξ.continuous_second)
    have hc2:Continuous (fun s=>(lam/2)*((p:ℝ)*((p-1:ℕ):ℝ)*s^(p-2)*(1-s))):=by fun_prop
    calc
      _=(∫s in a..b,(1/2:ℝ)*((1-s)*Ξ.second s)+(lam/2)*((p:ℝ)*((p-1:ℕ):ℝ)*s^(p-2)*(1-s))):=by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp only [X]
        rw [Ξ.addHighDegree_second]
        ring
      _=_:=by
        rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,hid]
  have hib : IntervalIntegrable (fun s=>(1-s)*Ξ.second s) volume a 1 := by
    have hc:Continuous (fun s=>(1-s)*Ξ.second s):=
      (continuous_const.sub continuous_id).mul Ξ.continuous_second
    exact hc.intervalIntegrable _ _
  have hbase := intervalIntegral.integral_mono_interval (a:=a) (b:=b) (c:=a) (d:=1)
    le_rfl hb.1 hb.2
    (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact mul_nonneg (sub_nonneg.mpr hs.2) (Ξ.second_nonneg (ha.1.trans hs.1.le))) hib
  have hpa:=highDegreeTailPrimitive_nonneg (by omega : 1≤p) ha
  rw [←firstVariation_difference_eq_integral X μ ha hbu,hdecomp] at him
  have hh:=mul_le_mul_of_nonneg_left hbase (by norm_num : (0:ℝ)≤1/2)
  have hl:=mul_nonneg (div_nonneg hlam.le (by norm_num : (0:ℝ)≤2)) hpa
  linarith

theorem high_overlap_intermediate_bound (Ξ : AdmissibleCovariance)
    {qc lamlo lamhi L γ : ℝ} (hc : qc∈Ioo (0:ℝ) 1)
    (hlo : 0 < lamlo) (hLH : lamlo≤lamhi) (hL : 0 < L) (hγ : 0 < γ)
    (hcut : (1/2:ℝ)*(∫s in qc..1,(1-s)*Ξ.second s)≤γ) :
    ∀ᶠp:ℕ in atTop,∀hp:4≤p,∀he:Even p,∀hn:p∉Ξ.degrees,
      ∀lam:ℝ,∀hlam:lam∈Icc lamlo lamhi,∀μ:ParisiMeasure,
        firstVariation (Ξ.addHighDegree p hp he hn lam (hlo.trans_le hlam.1)) μ qc≤-3*γ→
          ∀q∈Icc qc (logarithmicOverlapThreshold p lam L),
            firstVariation (Ξ.addHighDegree p hp he hn lam (hlo.trans_le hlam.1)) μ q≤-γ := by
  have hs:=(tendsto_logarithmicTailBudget lamhi L).eventually
    (Iio_mem_nhds (by positivity : (0:ℝ)<2*γ))
  have hl : ∀ᶠp:ℕ in atTop,1≤L*Real.log (p:ℝ) :=
    ((tendsto_const_mul_atTop_of_pos hL).mpr
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop 1
  have hr : ∀ᶠp:ℕ in atTop,L*(Real.log (p:ℝ)/(p:ℝ))<lamlo := by
    have hh:Tendsto (fun p:ℕ=>L*(Real.log (p:ℝ)/(p:ℝ))) atTop (𝓝 0):=by
      simpa only [mul_zero,Function.comp_def,id_eq] using
        (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul L
    exact hh.eventually (Iio_mem_nhds hlo)
  filter_upwards [eventually_ge_atTop (4:ℕ),hs,hl,hr] with p hp hs hl hr
  intro hp' he hn lam hlam μ hneg q hq
  have hpn:0 < (p:ℝ):=by exact_mod_cast (show 0<p by omega)
  have hsmall : L*Real.log (p:ℝ)<lam*(p:ℝ) := by
    rw [←mul_div_assoc] at hr
    have hd:=(div_lt_iff₀ hpn).mp hr
    exact hd.trans_le (mul_le_mul_of_nonneg_right hlam.1 hpn.le)
  have hth : logarithmicOverlapThreshold p lam L<1 :=
    logarithmicOverlapThreshold_lt_one (by omega) (hlo.trans_le hlam.1) hL hsmall
  have hb:=firstVariation_high_degree_increment_bound Ξ p hp' he hn (hlo.trans_le hlam.1) μ
    ⟨hc.1.le,hc.2.le⟩ ⟨hq.1,hq.2.trans hth.le⟩
  have hpmono : MonotoneOn (highDegreeTailPrimitive p) (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (by unfold highDegreeTailPrimitive;fun_prop)
      (f':=fun s=>(p:ℝ)*((p-1:ℕ):ℝ)*s^(p-2)*(1-s))
    · intro s _;exact (hasDerivAt_highDegreeTailPrimitive p (by omega) s).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg (p-1)))
        (pow_nonneg hs.1.le _)) (sub_nonneg.mpr hs.2.le)
  have hprim:=hpmono ⟨hc.1.le.trans hq.1,hq.2.trans hth.le⟩
    ⟨(logarithmicOverlapThreshold_pos ..).le,hth.le⟩ hq.2
  have hcost:=logarithmic_high_degree_cost_bound (by omega) (hlo.trans_le hlam.1) hlam.2 hL hl hth.le
  have hc1:=mul_le_mul_of_nonneg_left hprim (hlo.le.trans hlam.1)
  have hc2 : lam*highDegreeTailPrimitive p (logarithmicOverlapThreshold p lam L)≤logarithmicTailBudget lamhi L p := by
    unfold highDegreeTailPrimitive
    have hpow : (logarithmicOverlapThreshold p lam L)^p=
        (logarithmicOverlapThreshold p lam L)^(p-1)*logarithmicOverlapThreshold p lam L := by
      simpa only [Nat.sub_add_cancel (by omega : 1≤p)] using
        (pow_succ (logarithmicOverlapThreshold p lam L) (p-1))
    rw [hpow]
    convert hcost using 1 <;> ring
  nlinarith

end GeneralDepthPaper
