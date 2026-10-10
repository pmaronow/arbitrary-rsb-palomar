module

public import DepthPaper.StationaryBranchProposition
public import DepthPaper.EndpointChartContacts

@[expose] public section


/-! Actual stationary-candidate contacts. The lower stationary equations,
the genuine endpoint root, and the actual measure first variation identify
all contacts and the mass function, including mass one. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 64

theorem stationaryCandidate_contacts_of_actual_root (Ξ:AdmissibleCovariance) {r:ℕ}
    (p:ℕ) (hp:4≤p) (he:Even p) (hn:p∉Ξ.degrees) (qc cQ CQ:ℝ) (hCQ:cQ<CQ)
    (theta:ℝ×ℝ) (z:AtomicPoint r) (hz:IsAtomicPoint z)
    (hm:theta.2∈Ioc (0:ℝ) 1) (hlam:0<theta.1)
    (hc:atomicLocation z (Fin.last r)<qc)
    (hdom:(z,(theta.2,theta.1))∈distinguishedEndpointDomain Ξ p qc cQ CQ)
    (hunit:distinguishedEndpoint Ξ p qc cQ CQ (z,(theta.2,theta.1))∈Ioo qc 1)
    (hgrad:partialGradient (stationaryReducedObjective Ξ p qc cQ CQ) theta z=0)
    (hcontact:Gamma (Ξ.addHighDegree p hp he hn theta.1 hlam)
      (twoLevelMeasure z hz theta.2 (distinguishedOverlap Ξ p qc cQ CQ (z,(theta.2,theta.1))))
      (distinguishedOverlap Ξ p qc cQ CQ (z,(theta.2,theta.1)))=
      (distinguishedOverlap Ξ p qc cQ CQ (z,(theta.2,theta.1)):ℝ)) :
    let Ψ:=Ξ.addHighDegree p hp he hn theta.1 hlam
    let Q:=distinguishedOverlap Ξ p qc cQ CQ (z,(theta.2,theta.1))
    let μ:=twoLevelMeasure z hz theta.2 Q
    (∀q∈(atomicMeasure z hz : Measure Overlap).support,firstVariation Ψ μ q=0) ∧
    (∀q∈(atomicMeasure z hz : Measure Overlap).support,q≠⟨0,by norm_num⟩→
      firstVariationDerivative Ψ μ q=0) ∧
    firstVariationDerivative Ψ μ Q=0 ∧
    fderiv ℝ (stationaryReducedObjective Ξ p qc cQ CQ) (theta,z) ((0,1),0)=
      firstVariation Ψ μ Q := by
  let Ψ:=Ξ.addHighDegree p hp he hn theta.1 hlam
  let η:HighDegreeLowerParameter r:=(z,(theta.2,theta.1))
  let Q:=distinguishedOverlap Ξ p qc cQ CQ η
  let μ:=twoLevelMeasure z hz theta.2 Q
  have hc0:0<qc := (atomicLocation_mem_unit hz (Fin.last r)).1.trans_lt hc
  have hqeq:(Q:ℝ)=distinguishedEndpoint Ξ p qc cQ CQ η :=
    distinguishedOverlap_coe Ξ p qc cQ CQ η ⟨hc0.le.trans hunit.1.le,hunit.2.le⟩
  have hqcQ:qc<(Q:ℝ) := by rw [hqeq];exact hunit.1
  have hQ1:(Q:ℝ)<1 := by rw [hqeq];exact hunit.2
  have hred:=contDiffAt_reducedEndpointFunctional Ξ p qc cQ CQ hCQ (by omega) hz hdom
  have hstat:ContDiffAt ℝ ∞ (stationaryReducedObjective Ξ p qc cQ CQ) (theta,z) :=
    hred.comp (theta,z) stationaryParameterAssembly.contDiff.contDiffAt
  have hfull:fderiv ℝ (stationaryReducedObjective Ξ p qc cQ CQ) (theta,z)=
      (fderiv ℝ (reducedEndpointFunctional Ξ p qc cQ CQ) η).comp stationaryParameterAssembly := by
    exact (hred.differentiableAt (by simp)).hasFDerivAt.comp (theta,z)
      stationaryParameterAssembly.hasFDerivAt |>.fderiv
  have hen:=reducedEndpointFunctional_envelope Ξ p hp he hn qc cQ CQ hCQ hz
    ⟨hm.1,hm.2.trans_lt (by norm_num)⟩ hlam hc hdom hunit
  have hzgrad:fderiv ℝ (partialAtomicFunctionalExtension Ψ r theta.2 Q) z=0 := by
    apply ContinuousLinearMap.ext
    intro v
    have hg:=congrArg (fun L:AtomicPoint r→L[ℝ]ℝ=>L v) hgrad
    rw [partialGradient_eq_fullDerivative _ (hstat.differentiableAt (by simp)),hfull,hen] at hg
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.inl_apply,zero_apply] at hg
    change fderiv ℝ (endpointFunctionalChart Ξ p qc) (η,distinguishedEndpoint Ξ p qc cQ CQ η)
      ((v,(0,0)),0)=0 at hg
    rw [←hqeq] at hg
    rw [endpointFunctionalChart_lower_direction Ξ p hp he hn qc z hz theta.2 theta.1
      hm hlam Q hc hqcQ hQ1] at hg
    exact hg
  have hlow:=(atomic_gradient_zero_iff Ψ z hz theta.2 hm Q ⟨hc.trans hqcQ,hQ1⟩).mp hzgrad
  have hint:(∫q:Overlap,firstVariation Ψ μ q ∂(atomicMeasure z hz : Measure Overlap))=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [show ∀ᵐq ∂(atomicMeasure z hz : Measure Overlap),q∈(atomicMeasure z hz : Measure Overlap).support
      from Measure.support_mem_ae] with q hq
    exact hlow.1 q hq
  have hmass:fderiv ℝ (stationaryReducedObjective Ξ p qc cQ CQ) (theta,z) ((0,1),0)=
      firstVariation Ψ μ Q := by
    rw [hfull,hen]
    change fderiv ℝ (endpointFunctionalChart Ξ p qc) (η,distinguishedEndpoint Ξ p qc cQ CQ η)
      ((0,(1,0)),0)=firstVariation Ψ μ Q
    rw [←hqeq,endpointFunctionalChart_mass_direction Ξ p hp he hn qc z hz theta.2 theta.1
      hm hlam Q hc hqcQ hQ1,hint,sub_zero]
  have htop:firstVariationDerivative Ψ μ Q=0 := by
    dsimp only [firstVariationDerivative]
    rw [hcontact,sub_self,mul_zero]
  exact ⟨hlow.1,hlow.2,htop,hmass⟩

namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

/-- Literal Lemma 4.6 for the actual selected family, uniformly on the
closed parameter window, including the disappearing top atom at mass one. -/
theorem stationary_candidate_contacts (d:LimitingStandingData Ξ seed) :
    ∀ᶠp:ℕ in atTop,4≤p ∧ ∀heven:Even p,∃hp:4≤p,∃hn:p∉Ξ.degrees,
      ∀theta:ℝ×ℝ,∀ht:theta∈d.parameterWindow,
        ∃hz:IsAtomicPoint (d.stationaryBranch p theta),
          let z:=d.stationaryBranch p theta
          let Ψ:=Ξ.addHighDegree p hp heven hn theta.1 (d.couplingLower_pos.trans_le ht.1.1)
          let Q:=distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper (z,(theta.2,theta.1))
          let μ:=twoLevelMeasure z hz theta.2 Q
          (∀q∈(atomicMeasure z hz : Measure Overlap).support,firstVariation Ψ μ q=0) ∧
          (∀q∈(atomicMeasure z hz : Measure Overlap).support,q≠⟨0,by norm_num⟩→
            firstVariationDerivative Ψ μ q=0) ∧
          firstVariationDerivative Ψ μ Q=0 ∧
          d.stationaryMassFunction p theta=firstVariation Ψ μ Q := by
  obtain ⟨_,_,_,_,_,Hstationary⟩:=d.stationaryBranch_eventually
  obtain ⟨_,_,_,_,Hcontact⟩:=distinguished_endpoint_contact_eventually Ξ
    (isCompact_closedBall seed d.radius) d.ball_valid d.massLower_mem d.couplingLower_pos
    d.couplingLower_le_upper d.cutoff_mem d.ball_below_cutoff d.strip_rates.1
    d.strip_rates.2.1 d.strip_rates.2.2
  have hCQ:d.stripRateLower<d.stripRateUpper := by
    have he:d.massLower^2≤1 := by nlinarith [d.massLower_mem.1,d.massLower_mem.2]
    have hh:d.massLower^2*d.couplingLower≤d.couplingUpper :=
      (mul_le_mul_of_nonneg_right he (show 0≤d.couplingLower from d.couplingLower_pos.le)).trans
        (by simpa only [one_mul] using d.couplingLower_le_upper)
    linarith [d.strip_rates.2.1,d.strip_rates.2.2]
  filter_upwards [Hstationary,Hcontact,
    distinguished_endpoint_smooth_eventually Ξ (isCompact_closedBall seed d.radius) d.ball_valid
      d.massLower_mem d.couplingLower_pos d.couplingLower_le_upper d.cutoff_mem d.ball_below_cutoff
      d.strip_rates.1 d.strip_rates.2.1 d.strip_rates.2.2,
    endpointStrip_above_cutoff_eventually (CQ:=d.stripRateUpper) d.cutoff_mem.2 d.strip_rates.1]
      with p hs hc hsm hcut
  refine ⟨hc.1,?_⟩
  intro heven
  obtain ⟨hp4,hn,hdata⟩:=hc.2 heven
  refine ⟨hp4,hn,?_⟩
  intro theta ht
  let z:=d.stationaryBranch p theta
  have hzball:z∈closedBall seed d.radius := ball_subset_closedBall (hs heven theta ht).1
  let hz:=d.ball_valid z hzball
  refine ⟨hz,?_⟩
  let η:HighDegreeLowerParameter r:=(z,(theta.2,theta.1))
  let Q:=distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper η
  have hd:=hdata η hzball ht.2 ht.1
  have hdomain:η∈distinguishedEndpointDomain Ξ p d.cutoff d.stripRateLower d.stripRateUpper :=
    (hsm heven η hzball ht.2 ht.1).1
  have hstrip:(Q:ℝ)∈endpointStrip d.stripRateLower d.stripRateUpper p := Ioo_subset_Icc_self hd.2.1
  have hqcQ:d.cutoff<(Q:ℝ) := hcut Q hstrip
  have hQ1:(Q:ℝ)<1 := (endpointStrip_mem_unit d.strip_rates.1 p hstrip).2
  have hunit:distinguishedEndpoint Ξ p d.cutoff d.stripRateLower d.stripRateUpper η∈Ioo d.cutoff 1 := by
    rw [←hd.1]
    exact ⟨hqcQ,hQ1⟩
  exact stationaryCandidate_contacts_of_actual_root Ξ p hp4 heven hn
    d.cutoff d.stripRateLower d.stripRateUpper hCQ theta z hz
    ⟨d.massLower_mem.1.trans_le ht.2.1,ht.2.2⟩ (d.couplingLower_pos.trans_le ht.1.1)
    (d.ball_below_cutoff z hzball) hdomain hunit (hs heven theta ht).2.1 hd.2.2.1

end LimitingStandingData
end DepthPaper
