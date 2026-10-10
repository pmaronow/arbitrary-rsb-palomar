module

public import GeneralDepthPaper.RevisedSectionFourScalar
public import GeneralDepthPaper.RevisedSectionFourReduction
public import GeneralDepthPaper.RevisedStripLocalization

@[expose] public section

/-! The printed Section 4 windows and the actual selectors. Computation
uses a harmless larger root-search interval; the proved actual root lies
strictly inside the paper's narrower Sp and is its unique contact root. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1800000
namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

def revisedEndpointStrip (d:LimitingStandingData Ξ seed) (p:ℕ):Set ℝ:=
  endpointStrip d.stripRateLower d.revisedCouplingUpper p

theorem revisedCouplingLower_lt_upper (d:LimitingStandingData Ξ seed):
    d.couplingLower<d.revisedCouplingUpper:=by
  dsimp only [couplingLower,revisedCouplingUpper]
  linarith [d.couplingMargin_pos]

theorem revisedEndpointStrip_subset (d:LimitingStandingData Ξ seed) (p:ℕ):
    d.revisedEndpointStrip p⊆endpointStrip d.stripRateLower d.stripRateUpper p:=by
  intro q hq
  refine ⟨hq.1,?_⟩
  have hu:d.revisedCouplingUpper≤d.stripRateUpper:=by
    dsimp only [stripRateUpper]
    linarith [d.revisedCouplingUpper_lt_upper]
  have hh:Real.exp (-d.stripRateUpper*(p:ℝ))≤Real.exp (-d.revisedCouplingUpper*(p:ℝ)):=by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg p)]
  have hqu:=hq.2
  change q≤1-Real.exp (-d.revisedCouplingUpper*(p:ℝ)) at hqu
  change q≤1-Real.exp (-d.stripRateUpper*(p:ℝ))
  linarith

/-- Exact revised Propositions 4.3–4.4 on the printed Λ and Sp. -/
theorem revised_endpoint_root_and_reduction_data (d:LimitingStandingData Ξ seed) :
    ∃b:ℝ,0 < b ∧ ∃D:ℝ,0 < D ∧
      ∃Cq:ℝ,0 < Cq ∧ ∃Aq:ℕ,∃cq:ℝ,0 < cq ∧
      ∃Cf:ℝ,0 < Cf ∧ ∃Af:ℕ,∃cf:ℝ,0 < cf ∧ ∃P:ℕ,4 ≤ P ∧
        ∀p:ℕ,P ≤ p→∀heven:Even p,∃hp:4 ≤ p,∃hn:p∉Ξ.degrees,
          ∀theta:HighDegreeLowerParameter r,∀hz:theta.1∈closedBall seed d.radius,
            theta.2.1∈Icc d.massLower 1→∀hlam:theta.2.2∈d.revisedCouplingWindow,
            let Ψ := Ξ.addHighDegree p hp heven hn theta.2.2 (d.couplingLower_pos.trans_le hlam.1)
            let Q := distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper theta
            (Q:ℝ)=distinguishedEndpoint Ξ p d.cutoff d.stripRateLower d.stripRateUpper theta ∧
            (Q:ℝ)∈Ioo (1-Real.exp (-d.stripRateLower*(p:ℝ))) (1-Real.exp (-d.revisedCouplingUpper*(p:ℝ))) ∧
            Gamma Ψ (twoLevelMeasure theta.1 (d.ball_valid _ hz) theta.2.1 Q) Q=(Q:ℝ) ∧
            (∀T:Overlap,(T:ℝ)∈d.revisedEndpointStrip p→
              Gamma Ψ (twoLevelMeasure theta.1 (d.ball_valid _ hz) theta.2.1 T) T=(T:ℝ)→T=Q) ∧
            b*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-theta.2.1^2*theta.2.2*(p:ℝ)/2) ≤ 1-(Q:ℝ) ∧
            1-(Q:ℝ) ≤ D*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-theta.2.1^2*theta.2.2*(p:ℝ)/2) ∧
            ContDiffAt ℝ ∞ (distinguishedEndpoint Ξ p d.cutoff d.stripRateLower d.stripRateUpper) theta ∧
            (∀j:ℕ,1 ≤ j→j ≤ 2→‖iteratedFDeriv ℝ j
              (distinguishedEndpoint Ξ p d.cutoff d.stripRateLower d.stripRateUpper) theta‖ ≤ Cq*(p:ℝ)^Aq*Real.exp (-cq*(p:ℝ))) ∧
            ContDiffAt ℝ ∞ (reducedEndpointFunctional Ξ p d.cutoff d.stripRateLower d.stripRateUpper) theta ∧
            reducedEndpointFunctional Ξ p d.cutoff d.stripRateLower d.stripRateUpper theta=twoLevelFunctional Ψ theta.1
              (d.ball_valid _ hz) theta.2.1 Q ∧
            fderiv ℝ (reducedEndpointFunctional Ξ p d.cutoff d.stripRateLower d.stripRateUpper) theta=
              (fderiv ℝ (endpointFunctionalChart Ξ p d.cutoff)
                (theta,distinguishedEndpoint Ξ p d.cutoff d.stripRateLower d.stripRateUpper theta)).comp
                  (ContinuousLinearMap.inl ℝ (HighDegreeLowerParameter r) ℝ) ∧
            (theta.2.1 < 1→0 < deriv (deriv (fun q=>twoLevelFunctional Ψ theta.1 (d.ball_valid _ hz)
              theta.2.1 (projIcc 0 1 zero_le_one q))) Q) ∧
            (∀j:ℕ,j ≤ 3→‖iteratedFDeriv ℝ j
              (fun u=>reducedEndpointFunctional Ξ p d.cutoff d.stripRateLower d.stripRateUpper u-limitingObjectiveCore Ξ u)
                theta‖ ≤ Cf*(p:ℝ)^Af*Real.exp (-cf*(p:ℝ))) := by
  obtain ⟨b,hb,D,hD,Cq,hCq,Aq,cq,hcq,Cf,hCf,Af,cf,hcf,P,hP,H⟩:=
    endpoint_root Ξ r (closedBall seed d.radius) (isCompact_closedBall seed d.radius)
      d.ball_valid d.massLower d.couplingLower d.couplingUpper d.cutoff d.stripRateLower
      d.stripRateUpper d.massLower_mem d.couplingLower_pos d.couplingLower_le_upper
      d.cutoff_mem d.ball_below_cutoff d.strip_rates.1 d.strip_rates.2.1 d.strip_rates.2.2
  obtain ⟨PL,Hlocal⟩:=eventually_atTop.mp (revised_strip_localization d.massLower_mem
    d.couplingLower_pos d.revisedCouplingLower_lt_upper.le hb hD)
  refine ⟨b,hb,D,hD,Cq,hCq,Aq,cq,hcq,Cf,hCf,Af,cf,hcf,max P PL,
    hP.trans (le_max_left _ _),?_⟩
  intro p hpP he
  obtain ⟨hp,hn,Hdata⟩:=H p ((le_max_left _ _).trans hpP) he
  refine ⟨hp,hn,?_⟩
  intro theta hz hm hlam
  have hlamold:theta.2.2∈Icc d.couplingLower d.couplingUpper:=
    ⟨hlam.1,hlam.2.trans d.revisedCouplingUpper_lt_upper.le⟩
  have hd:=Hdata theta hz hm hlamold
  have hlocation:=Hlocal p ((le_max_right _ _).trans hpP) theta.2.1 hm theta.2.2 hlam
    (distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper theta)
      hd.2.2.2.2.1 hd.2.2.2.2.2.1
  refine ⟨hd.1,?_,hd.2.2.1,?_,hd.2.2.2.2⟩
  · change _∈Ioo (1-Real.exp (-d.stripRateLower*(p:ℝ)))
      (1-Real.exp (-d.revisedCouplingUpper*(p:ℝ))) at hlocation
    exact hlocation
  · intro T hT hroot
    exact hd.2.2.2.1 T (d.revisedEndpointStrip_subset p hT) hroot

end LimitingStandingData
theorem revised_prepared_endpoint_root_and_reduction (Ξ:AdmissibleCovariance) {r:ℕ}
    (seed:AtomicPoint r) (hz:IsAtomicPoint seed) (hND:PaperNondegenerate Ξ seed hz)
    (hsub:Ξ.IsSubcritical) :
    ∃d:LimitingStandingData Ξ seed,
    ∃b:ℝ,0 < b ∧ ∃D:ℝ,0 < D ∧
      ∃Cq:ℝ,0 < Cq ∧ ∃Aq:ℕ,∃cq:ℝ,0 < cq ∧
      ∃Cf:ℝ,0 < Cf ∧ ∃Af:ℕ,∃cf:ℝ,0 < cf ∧ ∃P:ℕ,4 ≤ P ∧
        ∀p:ℕ,P ≤ p→∀heven:Even p,∃hp:4 ≤ p,∃hn:p∉Ξ.degrees,
          ∀theta:HighDegreeLowerParameter r,∀hz:theta.1∈closedBall seed d.radius,
            theta.2.1∈Icc d.massLower 1→∀hlam:theta.2.2∈d.revisedCouplingWindow,
            let Ψ := Ξ.addHighDegree p hp heven hn theta.2.2 (d.couplingLower_pos.trans_le hlam.1)
            let Q := distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper theta
            (Q:ℝ)=distinguishedEndpoint Ξ p d.cutoff d.stripRateLower d.stripRateUpper theta ∧
            (Q:ℝ)∈Ioo (1-Real.exp (-d.stripRateLower*(p:ℝ))) (1-Real.exp (-d.revisedCouplingUpper*(p:ℝ))) ∧
            Gamma Ψ (twoLevelMeasure theta.1 (d.ball_valid _ hz) theta.2.1 Q) Q=(Q:ℝ) ∧
            (∀T:Overlap,(T:ℝ)∈d.revisedEndpointStrip p→
              Gamma Ψ (twoLevelMeasure theta.1 (d.ball_valid _ hz) theta.2.1 T) T=(T:ℝ)→T=Q) ∧
            b*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-theta.2.1^2*theta.2.2*(p:ℝ)/2) ≤ 1-(Q:ℝ) ∧
            1-(Q:ℝ) ≤ D*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-theta.2.1^2*theta.2.2*(p:ℝ)/2) ∧
            ContDiffAt ℝ ∞ (distinguishedEndpoint Ξ p d.cutoff d.stripRateLower d.stripRateUpper) theta ∧
            (∀j:ℕ,1 ≤ j→j ≤ 2→‖iteratedFDeriv ℝ j
              (distinguishedEndpoint Ξ p d.cutoff d.stripRateLower d.stripRateUpper) theta‖ ≤ Cq*(p:ℝ)^Aq*Real.exp (-cq*(p:ℝ))) ∧
            ContDiffAt ℝ ∞ (reducedEndpointFunctional Ξ p d.cutoff d.stripRateLower d.stripRateUpper) theta ∧
            reducedEndpointFunctional Ξ p d.cutoff d.stripRateLower d.stripRateUpper theta=twoLevelFunctional Ψ theta.1
              (d.ball_valid _ hz) theta.2.1 Q ∧
            fderiv ℝ (reducedEndpointFunctional Ξ p d.cutoff d.stripRateLower d.stripRateUpper) theta=
              (fderiv ℝ (endpointFunctionalChart Ξ p d.cutoff)
                (theta,distinguishedEndpoint Ξ p d.cutoff d.stripRateLower d.stripRateUpper theta)).comp
                  (ContinuousLinearMap.inl ℝ (HighDegreeLowerParameter r) ℝ) ∧
            (theta.2.1 < 1→0 < deriv (deriv (fun q=>twoLevelFunctional Ψ theta.1 (d.ball_valid _ hz)
              theta.2.1 (projIcc 0 1 zero_le_one q))) Q) ∧
            (∀j:ℕ,j ≤ 3→‖iteratedFDeriv ℝ j
              (fun u=>reducedEndpointFunctional Ξ p d.cutoff d.stripRateLower d.stripRateUpper u-limitingObjectiveCore Ξ u)
                theta‖ ≤ Cf*(p:ℝ)^Af*Real.exp (-cf*(p:ℝ))) := by
  obtain ⟨d⟩:=exists_limitingStandingData Ξ seed hz
    (nondegenerate_of_paperNondegenerate Ξ seed hz hND hsub)
  exact ⟨d,d.revised_endpoint_root_and_reduction_data⟩

end GeneralDepthPaper
