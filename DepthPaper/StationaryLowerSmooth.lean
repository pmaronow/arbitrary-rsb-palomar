module

public import DepthPaper.StationaryLowerActual
public import DepthPaper.CoerciveStationaryEquation

@[expose] public section


/-! Ordinary all-order smoothness of the actual lower selector, including
the closed physical parameter-window endpoints. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 64

namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

theorem stationaryBranch_regular_error_eventually (d:LimitingStandingData Ξ seed) :
    ∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧
      ∀ᶠp:ℕ in atTop,∀heven:Even p,∀theta∈d.parameterWindow,
        ContDiffAt ℝ ∞ (d.stationaryBranch p) theta ∧
        (∀z∈closedBall seed d.radius,
          ContDiffAt ℝ ∞ (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper)
            (theta,z)) ∧
        (∀z∈closedBall seed d.radius,∀v:AtomicPoint r,
          d.margin/2*‖v‖^2 ≤ partialHessian
            (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper) theta z v v) ∧
        (∀z∈closedBall seed d.radius,∀j:ℕ,j ≤ 3→
          ‖iteratedFDeriv ℝ j (fun w=>
            stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper w-
            stationaryLimitingObjective Ξ w) (theta,z)‖ ≤
              C*(p:ℝ)^A*Real.exp (-c*(p:ℝ))) ∧
        (∀ᶠu in 𝓝 theta, d.stationaryBranch p u∈ball seed d.radius ∧
          partialGradient (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper)
            u (d.stationaryBranch p u)=0) := by
  have hR:=d.radius_pos
  have hκ:=d.margin_pos
  obtain ⟨C,hC,A,c,hc,H⟩:=reduced_endpoint_C3_exponential_bound Ξ
    (isCompact_closedBall seed d.radius) d.ball_valid d.massLower_mem d.couplingLower_pos
    d.couplingLower_le_upper d.cutoff_mem d.ball_below_cutoff d.strip_rates.1
    d.strip_rates.2.1 d.strip_rates.2.2
  obtain ⟨_,_,_,_,_,Hs⟩:=d.stationaryBranch_eventually
  have Hsmall:∀ᶠp:ℕ in atTop,C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) < d.margin*d.radius/8 :=
    (tendsto_nat_polynomial_exp C c A hc).eventually
      (eventually_lt_nhds (show (0:ℝ) < d.margin*d.radius/8 by positivity))
  have hCQ:d.stripRateLower < d.stripRateUpper := by
    have he:d.massLower^2 ≤ 1 := by nlinarith [d.massLower_mem.1,d.massLower_mem.2]
    have hh:=mul_le_mul_of_nonneg_right he d.couplingLower_pos.le
    change d.massLower^2*d.couplingLower ≤ 1*d.couplingLower at hh
    have hl:=d.couplingLower_le_upper
    have hs:=d.strip_rates
    linarith
  refine ⟨C,hC,A,c,hc,?_⟩
  filter_upwards [H,Hs,Hsmall,eventually_ge_atTop 1,
    distinguished_endpoint_smooth_eventually Ξ (isCompact_closedBall seed d.radius) d.ball_valid
      d.massLower_mem d.couplingLower_pos d.couplingLower_le_upper d.cutoff_mem d.ball_below_cutoff
      d.strip_rates.1 d.strip_rates.2.1 d.strip_rates.2.2] with p hp hs hsmall hp1 hroot
  intro heven theta ht
  have hmp:0 < theta.2 := d.massLower_mem.1.trans_le ht.2.1
  have hsm (z:AtomicPoint r) (hz:z∈closedBall seed d.radius):
      ContDiffAt ℝ ∞ (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper)
        (theta,z) :=
    (contDiffAt_reducedEndpointFunctional Ξ p d.cutoff d.stripRateLower d.stripRateUpper hCQ
      (by omega) (d.ball_valid z hz)
      (hroot heven (z,(theta.2,theta.1)) hz ht.2 ht.1).1).comp (theta,z)
        stationaryParameterAssembly.contDiff.contDiffAt
  have hjets (z:AtomicPoint r) (hz:z∈closedBall seed d.radius) (j:ℕ) (hj:j ≤ 3):
      ‖iteratedFDeriv ℝ j (fun w=>
        stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper w-
        stationaryLimitingObjective Ξ w) (theta,z)‖ ≤ C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
    have hr:=contDiffAt_reducedEndpointFunctional Ξ p d.cutoff d.stripRateLower d.stripRateUpper hCQ
      (by omega) (d.ball_valid z hz) (hroot heven (z,(theta.2,theta.1)) hz ht.2 ht.1).1
    exact (norm_stationaryObjective_difference_jet_le Ξ p d.cutoff d.stripRateLower d.stripRateUpper
      theta z j (hr.sub (contDiffAt_limitingObjectiveCore Ξ (d.ball_valid z hz) hmp))).trans
        (hp heven (z,(theta.2,theta.1)) hz ht.2 ht.1 j hj)
  have hz0:d.branch theta.2∈closedBall seed d.radius := by
    rw [mem_closedBall]
    have hh:=d.branch_close theta.2 ht.2
    linarith [d.radius_pos]
  have hzero:partialGradient (stationaryLimitingObjective Ξ) theta (d.branch theta.2)=0 := by
    rw [stationaryLimitingObjective_gradient Ξ _ (d.ball_valid _ hz0) theta hmp]
    exact d.branch_stationary theta.2 ht.2
  have hgrad:‖partialGradient
      (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper)
      theta (d.branch theta.2)‖ ≤ C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
    have hh:=(norm_partialGradient_sub_le (hsm _ hz0)
      (contDiffAt_stationaryLimitingObjective Ξ _ (d.ball_valid _ hz0) theta hmp)).trans
        (hjets _ hz0 1 (by norm_num))
    simpa only [hzero,sub_zero] using hh
  have hco:∀z∈closedBall seed d.radius,∀v:AtomicPoint r,
      d.margin/2*‖v‖^2 ≤ partialHessian
        (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper) theta z v v :=
    (hs heven theta ht).2.2.2.2
  have hdiff:=contDiffAt_coerciveBallStationarySelector
    (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper)
    seed (d.branch theta.2) d.radius (d.radius/2) (d.margin/2) theta
    (by positivity) (by positivity) (by linarith [d.branch_close theta.2 ht.2]) hsm hco
    (by convert hgrad.trans_lt hsmall using 1 <;> ring)
  have heq:=eventually_stationary_coerciveBallStationarySelector
    (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper)
    seed (d.branch theta.2) d.radius (d.radius/2) (d.margin/2) theta
    (by positivity) (by positivity) (by linarith [d.branch_close theta.2 ht.2]) hsm hco
    (by convert hgrad.trans_lt hsmall using 1 <;> ring)
  exact ⟨hdiff,hsm,hco,hjets,heq⟩

end LimitingStandingData
end DepthPaper
