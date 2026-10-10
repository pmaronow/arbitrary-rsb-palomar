module

public import DepthPaper.CandidateEndpointSchur
public import DepthPaper.StationaryCandidateContacts

@[expose] public section


/-! Literal Lemma 4.8 for the actual stationary family. All Hessian
blocks, stationary equations, endpoint roots and chart identifications
are supplied by proved properties of the selected actual objects. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 64
namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

theorem stationary_candidate_hessian (d:LimitingStandingData Ξ seed) :
    ∀ᶠp:ℕ in atTop,4≤p ∧ ∀he:Even p,∃hp:4≤p,∃hn:p∉Ξ.degrees,
      ∀theta:ℝ×ℝ,∀ht:theta∈d.parameterWindow,
        ∃_hz:IsAtomicPoint (d.stationaryBranch p theta),
          let z:=d.stationaryBranch p theta
          let Ψ:=Ξ.addHighDegree p hp he hn theta.1 (d.couplingLower_pos.trans_le ht.1.1)
          let Q:=distinguishedEndpoint Ξ p d.cutoff d.stripRateLower d.stripRateUpper (z,(theta.2,theta.1))
          (theta.2=1→∀v:AtomicPoint r,v≠0→0<fderiv ℝ
            (fderiv ℝ (atomicFunctionalExtension Ψ r)) z v v) ∧
          (theta.2<1→d.stationaryMassFunction p theta=0→
            IsAtomicPoint (twoLevelAtomicCoordinates (z,theta.2,Q)) ∧
            ∀v:AtomicPoint (r+1),v≠0→0<fderiv ℝ
              (fderiv ℝ (atomicFunctionalExtension Ψ (r+1)))
              (twoLevelAtomicCoordinates (z,theta.2,Q)) v v) := by
  obtain ⟨_,_,_,_,_,Hreg⟩:=d.stationaryBranch_regular_error_eventually
  have hCQ:d.stripRateLower<d.stripRateUpper := by
    have hpow:d.massLower^2≤1 := by nlinarith [d.massLower_mem.1,d.massLower_mem.2]
    have hh:=mul_le_mul_of_nonneg_right hpow d.couplingLower_pos.le
    change d.massLower^2*d.couplingLower≤1*d.couplingLower at hh
    have hl:=d.couplingLower_le_upper
    have hs:=d.strip_rates
    linarith
  filter_upwards [d.stationary_candidate_contacts,Hreg,d.stationary_reduced_hessian_positive,
    distinguished_endpoint_smooth_eventually Ξ (isCompact_closedBall seed d.radius) d.ball_valid
      d.massLower_mem d.couplingLower_pos d.couplingLower_le_upper d.cutoff_mem d.ball_below_cutoff
      d.strip_rates.1 d.strip_rates.2.1 d.strip_rates.2.2,
    endpointStrip_above_cutoff_eventually (CQ:=d.stripRateUpper) d.cutoff_mem.2 d.strip_rates.1]
    with p hcontact hreg hred hroot hcut
  refine ⟨hcontact.1,?_⟩
  intro he
  obtain ⟨hp,hn,Hcontact⟩:=hcontact.2 he
  refine ⟨hp,hn,?_⟩
  intro theta ht
  obtain ⟨hz,Hc⟩:=Hcontact theta ht
  let z:=d.stationaryBranch p theta
  let eta:HighDegreeLowerParameter r:=(z,(theta.2,theta.1))
  let Q:=distinguishedEndpoint Ξ p d.cutoff d.stripRateLower d.stripRateUpper eta
  have hr:=hreg he theta ht
  have hb:z∈closedBall seed d.radius := ball_subset_closedBall (hr.2.2.2.2.self_of_nhds.1)
  have hdom:=hroot he eta hb ht.2 ht.1
  have hstrip:Q∈endpointStrip d.stripRateLower d.stripRateUpper p := Ioo_subset_Icc_self hdom.2.1
  have hunit:Q∈Ioo d.cutoff 1 :=
    ⟨hcut Q hstrip,(endpointStrip_mem_unit d.strip_rates.1 p hstrip).2⟩
  have hc:atomicLocation z (Fin.last r)<d.cutoff := d.ball_below_cutoff z hb
  have hlam:0<theta.1 := d.couplingLower_pos.trans_le ht.1.1
  have hm:theta.2∈Ioc (0:ℝ) 1 := ⟨d.massLower_mem.1.trans_le ht.2.1,ht.2.2⟩
  have hF:ContDiffAt ℝ ∞ (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper)
      (theta,z) := hr.2.1 z hb
  refine ⟨hz,?_,?_⟩
  · intro hm1 v hv
    have heq:=reduced_mass_one_eventuallyEq_atomic Ξ p hp he hn d.cutoff d.stripRateLower
      d.stripRateUpper theta.1 hCQ hlam z hz hc
      (by simpa only [eta,hm1] using hdom.1) (by simpa only [Q,eta,hm1] using hunit)
    have heq':(fun y:AtomicPoint r=>stationaryReducedObjective Ξ p d.cutoff d.stripRateLower
        d.stripRateUpper (theta,y))=ᶠ[𝓝 z]
        atomicFunctionalExtension (Ξ.addHighDegree p hp he hn theta.1 hlam) r := by
      simpa only [stationaryReducedObjective,stationaryParameterAssembly,
        ContinuousLinearMap.coe_mk',LinearMap.coe_mk,AddHom.coe_mk,hm1] using heq
    rw [←heq'.fderiv.fderiv_eq]
    exact (mul_pos (half_pos d.margin_pos) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv))).trans_le
      (hr.2.2.1 z hb v)
  · intro hm1 hg
    have hcrit:fderiv ℝ (fixedCouplingReducedObjective Ξ p d.cutoff d.stripRateLower
        d.stripRateUpper theta.1) (z,theta.2)=0 := by
      let F:=stationaryReducedObjective Ξ (r:=r) p d.cutoff d.stripRateLower d.stripRateUpper
      have hi:HasFDerivAt (fun y:AtomicPoint r×ℝ=>((theta.1,y.2),y.1))
          fixedCouplingAssembly (z,theta.2) := by
        convert ((hasFDerivAt_const (𝕜:=ℝ) theta.1 (z,theta.2)).prodMk
          (hasFDerivAt_snd (𝕜:=ℝ) (p:=(z,theta.2)))).prodMk (hasFDerivAt_fst (𝕜:=ℝ) (p:=(z,theta.2))) using 1
        rfl
      have hd:=(hF.differentiableAt (by simp)).hasFDerivAt.comp (z,theta.2) hi
      have hlow:=hr.2.2.2.2.self_of_nhds.2
      have hlow' (v:AtomicPoint r):fderiv ℝ F (theta,z) (0,v)=0 := by
        have H:=congrArg (fun L:AtomicPoint r→L[ℝ]ℝ=>L v) hlow
        rw [partialGradient_eq_fullDerivative _ (hF.differentiableAt (by simp))] at H
        simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,zero_apply] using H
      apply ContinuousLinearMap.ext
      intro v
      change (fderiv ℝ (F ∘ fun y:AtomicPoint r×ℝ=>((theta.1,y.2),y.1)) (z,theta.2)) v=0
      rw [hd.fderiv]
      change fderiv ℝ F (theta,z) ((0,v.2),v.1)=0
      rw [show ((0,v.2),v.1)=((0,0),v.1)+v.2 • (((0,1):ℝ×ℝ),(0:AtomicPoint r)) by simp,
        map_add,map_smul]
      have hlv:fderiv ℝ F (theta,z) ((0,0),v.1)=0 := hlow' v.1
      rw [hlv]
      change 0+v.2 • d.stationaryMassFunction p theta=0
      rw [hg,smul_zero,add_zero]
    refine ⟨isAtomicPoint_twoLevelCoordinates z hz theta.2 Q ⟨hm.1,hm1⟩ (hc.trans hunit.1) hunit.2,?_⟩
    exact candidateEndpoint_atomic_hessian_pos_from_reduced Ξ p hp he hn d.cutoff
      d.stripRateLower d.stripRateUpper theta.1 hCQ hlam z hz theta.2 ⟨hm.1,hm1⟩ hc
      hdom.1 hunit (hred he theta ht) hcrit

end LimitingStandingData
end DepthPaper
