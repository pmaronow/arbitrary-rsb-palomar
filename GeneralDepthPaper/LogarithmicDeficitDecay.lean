module

public import GeneralDepthPaper.LogarithmicVarianceBounds
public import GeneralDepthPaper.CutoffHighVarianceDeficit

@[expose] public section


/-! Uniform p⁻⁴ smoothing at the manuscript's logarithmic threshold,
for the actual high-degree candidate and its actual selected-state Γ. -/
noncomputable section
open Set Filter
open scoped Topology
namespace GeneralDepthPaper
set_option maxHeartbeats 1200000

theorem logarithmic_exponential_bound {ε m L B t p : ℝ}
    (hε : 0 < ε) (hm : m∈Icc ε 1) (hL : 0 < L)
    (hcoef : 10≤ε^2*L) (hB : 0≤B) (hp : 1≤p)
    (ht : L*Real.log p-B≤t) :
    Real.exp (-m^2*t/2)≤Real.exp (B/2)*Real.exp (-5*Real.log p) := by
  have hm0 : 0 ≤ m:=hε.le.trans hm.1
  have hsq : ε^2 ≤ m^2 := pow_le_pow_left₀ hε.le hm.1 2
  have hsq1 : m^2≤1 := by simpa only [one_pow] using pow_le_pow_left₀ hm0 hm.2 2
  have hl : 0≤Real.log p:=Real.log_nonneg hp
  have hc : 10 ≤ m^2*L := hcoef.trans (mul_le_mul_of_nonneg_right hsq hL.le)
  have ht' := mul_le_mul_of_nonneg_left ht (sq_nonneg m)
  have hb := mul_le_mul_of_nonneg_right hsq1 hB
  have hlog := mul_le_mul_of_nonneg_right hc hl
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem exponential_logarithmic_budget_eventually {D E c : ℝ} (hc : 0 < c) :
    ∀ᶠp:ℕ in atTop,
      D*Real.exp (-5*Real.log (p:ℝ))+E*Real.exp (-c*(p:ℝ))≤((p:ℝ)^4)⁻¹ := by
  have hlim : Tendsto (fun p:ℕ=>D/(p:ℝ)+E*(p:ℝ)^4*Real.exp (-c*(p:ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun p:ℕ=>D/(p:ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa only [zero_add] using h1.add (tendsto_nat_polynomial_exp E c 4 hc)
  have hs:=hlim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [eventually_ge_atTop (1:ℕ),hs] with p hp hs
  have hpn : 0 < (p:ℝ) := by exact_mod_cast (show 0<p by omega)
  have he : Real.exp (-5*Real.log (p:ℝ))=((p:ℝ)^5)⁻¹ := by
    rw [show -5*Real.log (p:ℝ)=-(5*Real.log (p:ℝ)) by ring,Real.exp_neg,
      show 5*Real.log (p:ℝ)=((5:ℕ):ℝ)*Real.log (p:ℝ) by norm_num,
      Real.exp_nat_mul,Real.exp_log hpn]
  rw [he]
  conv_rhs => rw [←one_div]
  apply (le_div_iff₀ (pow_pos hpn 4)).mpr
  have heq : (D*((p:ℝ)^5)⁻¹+E*Real.exp (-c*(p:ℝ)))*(p:ℝ)^4=
      D/(p:ℝ)+E*(p:ℝ)^4*Real.exp (-c*(p:ℝ)) := by
    field_simp [ne_of_gt hpn]
    <;> ring
  rw [heq]
  exact hs.le

theorem logarithmic_deficit_decay (Ξ : AdmissibleCovariance)
    {ε qc cQ CQ lamlo lamhi L : ℝ} (hε : 0 < ε) (hc : qc∈Ioo (0:ℝ) 1)
    (hcQ : 0 < cQ) (hlo : 0 < lamlo) (hLH : lamlo≤lamhi)
    (hL : 0 < L) (hcoef : 10≤ε^2*L) :
    ∀ᶠp:ℕ in atTop,∀hp:4≤p,∀he:Even p,∀hn:p∉Ξ.degrees,
      ∀lam:ℝ,∀hlam:lam∈Icc lamlo lamhi,∀Q:Overlap,
        (Q:ℝ)∈endpointStrip cQ CQ p→∀m∈Icc ε 1,∀r:ℕ,
          ∀z:AtomicPoint r,∀hz:IsAtomicPoint z,atomicLocation z (Fin.last r)<qc→
            1-Gamma (Ξ.addHighDegree p hp he hn lam (hlo.trans_le hlam.1))
                (twoLevelMeasure z hz m Q) (logarithmicOverlapThreshold p lam L)≤((p:ℝ)^4)⁻¹ := by
  obtain ⟨C,hC,hbound⟩:=cutoff_high_variance_deficit_bound hε
  let B:=cutoffDriverVarianceBound Ξ qc lamhi
  let D:=2*Real.exp (B/2)
  let E:=2*C
  let c:=ε^2*lamlo/16
  have hcpos : 0 < c := by dsimp only [c];positivity
  have hB : 0≤B := cutoffDriverVarianceBound_nonneg Ξ hc (hlo.le.trans hLH)
  have hv:=logarithmic_variance_bounds_eventually Ξ (CQ:=CQ) hc hcQ hlo hLH hL
  have hg:=logarithmicOverlapThreshold_geometry_eventually (CQ:=CQ) hc hcQ hlo hLH hL
  have hs:=exponential_logarithmic_budget_eventually (D:=D) (E:=E) hcpos
  have hlarge : ∀ᶠp:ℕ in atTop,1<lamlo*(p:ℝ)/4 :=
    ((tendsto_const_mul_atTop_of_pos (by positivity : (0:ℝ)<lamlo/4)).mpr
      tendsto_natCast_atTop_atTop).eventually_gt_atTop 1 |>.mono (fun p hp=>by nlinarith)
  filter_upwards [eventually_ge_atTop (4:ℕ),hv,hg,hs,hlarge] with p hp hv hg hs hlarge
  intro hp' he hn lam hlam Q hQ m hm r z hz hzqc
  let X:=Ξ.addHighDegree p hp' he hn lam (hlo.trans_le hlam.1)
  let q:=logarithmicOverlapThreshold p lam L
  have hgeom:=hg lam hlam Q hQ
  have hvars:=hv hp' he hn lam hlam Q hQ
  have hq : q∈Ioc qc (Q:ℝ):=⟨hgeom.1,hgeom.2.le⟩
  have hR : 1<X.first Q-X.first q := hlarge.trans hvars.2
  have hb:=hbound X r z hz m hm Q qc hzqc q hq hR
  have ht:=logarithmic_exponential_bound hε hm hL hcoef hB
    (by exact_mod_cast (show 1≤p by omega)) hvars.1
  have hr : Real.exp (-ε^2*(X.first Q-X.first q)/4)≤Real.exp (-c*(p:ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hh:=mul_le_mul_of_nonneg_left hvars.2.le (sq_nonneg ε)
    dsimp only [c]
    nlinarith
  have h1:=mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ)≤2)
  have h2:=mul_le_mul_of_nonneg_left hr (by positivity : (0:ℝ)≤2*C)
  apply hb.trans
  apply (add_le_add h1 h2).trans
  convert hs using 1 <;> dsimp only [D,E] <;> ring

end GeneralDepthPaper
