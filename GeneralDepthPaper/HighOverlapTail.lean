module

public import GeneralDepthPaper.LogarithmicDeficitDecay
public import GeneralDepthPaper.GammaTailBounds

@[expose] public section


/-! The actual uniform Γ′ ≤ 1/2 upper-overlap conclusion of Proposition 4.10.
The candidate need not yet satisfy its endpoint stationarity equation. -/
noncomputable section
open Set Filter
open scoped Topology
namespace GeneralDepthPaper
set_option maxHeartbeats 900000

theorem high_overlap_slope_tail (Ξ : AdmissibleCovariance)
    {ε qc cQ CQ lamlo lamhi L : ℝ} (hε : 0 < ε) (hc : qc∈Ioo (0:ℝ) 1)
    (hcQ : 0 < cQ) (hlo : 0 < lamlo) (hLH : lamlo≤lamhi)
    (hL : 0 < L) (hcoef : 10≤ε^2*L) :
    ∀ᶠp:ℕ in atTop,∀hp:4≤p,∀he:Even p,∀hn:p∉Ξ.degrees,
      ∀lam:ℝ,∀hlam:lam∈Icc lamlo lamhi,∀Q:Overlap,
        (Q:ℝ)∈endpointStrip cQ CQ p→∀m∈Icc ε 1,∀r:ℕ,
          ∀z:AtomicPoint r,∀hz:IsAtomicPoint z,atomicLocation z (Fin.last r)<qc→
            ∀q∈Icc (logarithmicOverlapThreshold p lam L) 1,
              GammaPrime (Ξ.addHighDegree p hp he hn lam (hlo.trans_le hlam.1))
                (twoLevelMeasure z hz m Q) q≤1/2 := by
  have hd:=logarithmic_deficit_decay Ξ (CQ:=CQ) hε hc hcQ hlo hLH hL hcoef
  have hg:=logarithmicOverlapThreshold_geometry_eventually (CQ:=CQ) hc hcQ hlo hLH hL
  have hlim : Tendsto (fun p:ℕ=>(Ξ.second 1+lamhi)*((1:ℝ)/(p:ℝ))^2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2:ℕ)≠0),mul_zero] using
      ((tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun p:ℕ=>(1:ℝ)/(p:ℝ)) atTop (𝓝 0)).pow 2).const_mul (Ξ.second 1+lamhi)
  have hs:=hlim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2))
  filter_upwards [eventually_ge_atTop (4:ℕ),hd,hg,hs] with p hp hd hg hs
  intro hp' he hn lam hlam Q hQ m hm r z hz hzqc q hq
  have hqhat : logarithmicOverlapThreshold p lam L∈Icc (0:ℝ) 1:=
    ⟨(logarithmicOverlapThreshold_pos ..).le,(hg lam hlam Q hQ).2.le.trans Q.property.2⟩
  have hδ:=hd hp' he hn lam hlam Q hQ m hm r z hz hzqc
  have hb:=highDegree_GammaPrime_tail_bound Ξ p hp' he hn (hlo.trans_le hlam.1) hlam.2
    (twoLevelMeasure z hz m Q) hqhat hq hδ
  have hpn : (p:ℝ)≠0 := by exact_mod_cast (show p≠0 by omega)
  have heq : (Ξ.second 1+lamhi)*(p:ℝ)^2*((p:ℝ)^4)⁻¹=
      (Ξ.second 1+lamhi)*((1:ℝ)/(p:ℝ))^2 := by
    field_simp [hpn]
    <;> ring
  rw [heq] at hb
  exact hb.trans hs.le

end GeneralDepthPaper
