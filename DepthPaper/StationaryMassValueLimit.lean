module

public import DepthPaper.StationaryMassJetBounds

@[expose] public section


/-! The actual reduced mass stationarity function converges uniformly
to the genuine pressure envelope (λ−ell(m))/2. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1900000
set_option maxSynthPendingDepth 64

namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

theorem stationaryMassFunction_value_error (d:LimitingStandingData Ξ seed) :
    ∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧
      ∀ᶠp:ℕ in atTop,∀heven:Even p,∀theta∈d.parameterWindow,
        |d.stationaryMassFunction p theta-
          (theta.1-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) theta.2)/2| ≤
          C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  obtain ⟨L,hL,hLip⟩:=d.boundedSmoothOn_limitingMassJetField.value_lipschitz d.stationaryInputWindow_convex
  obtain ⟨Cz,hCz,Az,cz,hcz,Hz⟩:=d.stationaryBranch_eventually
  obtain ⟨Cf,hCf,Af,cf,hcf,Hf⟩:=reduced_endpoint_C3_exponential_bound Ξ
    (isCompact_closedBall seed d.radius) d.ball_valid d.massLower_mem d.couplingLower_pos
    d.couplingLower_le_upper d.cutoff_mem d.ball_below_cutoff d.strip_rates.1
    d.strip_rates.2.1 d.strip_rates.2.2
  obtain ⟨C,hC,A,c,hc,Hsum⟩:=three_degree_exp_envelope
    (C1:=Cf) (C2:=L*Cz) (C3:=0) (A1:=Af) (A2:=Az) (A3:=0)
    hCf.le (by positivity) (by norm_num) hcf hcz (show (0:ℝ)<1 by norm_num)
  have hCQ:d.stripRateLower < d.stripRateUpper := by
    have hs:=d.strip_rates
    have he:d.massLower^2 ≤ 1 := by nlinarith [d.massLower_mem.1,d.massLower_mem.2]
    have hh:=mul_le_mul_of_nonneg_right he d.couplingLower_pos.le
    change d.massLower^2*d.couplingLower ≤ 1*d.couplingLower at hh
    have hl:=d.couplingLower_le_upper
    linarith
  refine ⟨C,hC,A,c,hc,?_⟩
  filter_upwards [Hz,Hf,eventually_ge_atTop 1,
    distinguished_endpoint_smooth_eventually Ξ (isCompact_closedBall seed d.radius) d.ball_valid
      d.massLower_mem d.couplingLower_pos d.couplingLower_le_upper d.cutoff_mem d.ball_below_cutoff
      d.strip_rates.1 d.strip_rates.2.1 d.strip_rates.2.2] with p hz hf hp1 hroot
  intro heven theta ht
  have hzspec:=hz heven theta ht
  let zp:=d.stationaryBranch p theta
  have hzp:zp∈closedBall seed d.radius := ball_subset_closedBall hzspec.1
  have hz0:d.branch theta.2∈closedBall seed d.radius := by
    rw [mem_closedBall]
    have hh:=d.branch_close theta.2 ht.2
    linarith [d.radius_pos]
  have hmp:0 < theta.2 := d.massLower_mem.1.trans_le ht.2.1
  have hfs:ContDiffAt ℝ ∞ (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper)
      (theta,zp) :=
    (contDiffAt_reducedEndpointFunctional Ξ p d.cutoff d.stripRateLower d.stripRateUpper hCQ
      (by omega) (d.ball_valid zp hzp)
      (hroot heven (zp,(theta.2,theta.1)) hzp ht.2 ht.1).1).comp (theta,zp)
        stationaryParameterAssembly.contDiff.contDiffAt
  have hgs:=contDiffAt_stationaryLimitingObjective Ξ zp (d.ball_valid zp hzp) theta hmp
  have hraw:=contDiffAt_reducedEndpointFunctional Ξ p d.cutoff d.stripRateLower d.stripRateUpper hCQ
    (by omega) (d.ball_valid zp hzp) (hroot heven (zp,(theta.2,theta.1)) hzp ht.2 ht.1).1
  have hjet:‖iteratedFDeriv ℝ 1 (fun w=>
      stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper w-
      stationaryLimitingObjective Ξ w) (theta,zp)‖ ≤ Cf*(p:ℝ)^Af*Real.exp (-cf*(p:ℝ)) :=
    (norm_stationaryObjective_difference_jet_le Ξ p d.cutoff d.stripRateLower d.stripRateUpper theta zp 1
      (hraw.sub (contDiffAt_limitingObjectiveCore Ξ (d.ball_valid zp hzp) hmp))).trans
        (hf heven (zp,(theta.2,theta.1)) hzp ht.2 ht.1 1 (by norm_num))
  have heval:|d.stationaryMassFunction p theta-d.limitingMassJetField (theta,zp)| ≤
      Cf*(p:ℝ)^Af*Real.exp (-cf*(p:ℝ)) := by
    have hh:=(norm_directional_jet_difference_le hfs hgs (((0,1),0):(ℝ×ℝ)×AtomicPoint r)
      (by simp [Prod.norm_def]) 0).trans hjet
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,stationaryMassFunction,
      limitingMassJetField,zp] using hh
  have hgraph:‖(theta,zp)-(theta,d.branch theta.2)‖=‖zp-d.branch theta.2‖ := by
    change max ‖theta-theta‖ ‖zp-d.branch theta.2‖=‖zp-d.branch theta.2‖
    rw [sub_self,norm_zero,max_eq_right (norm_nonneg _)]
  have hlim:|d.limitingMassJetField (theta,zp)-d.limitingMassJetField (theta,d.branch theta.2)| ≤
      L*(Cz*(p:ℝ)^Az*Real.exp (-cz*(p:ℝ))) := by
    have hh:=hLip (theta,d.branch theta.2) ⟨ht,hz0⟩ (theta,zp) ⟨ht,hzp⟩
    rw [hgraph,Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hzspec.2.2.2.1 hL)
  rw [←d.limitingMassJetField_on_branch theta ht]
  have htri:=abs_sub_le (d.stationaryMassFunction p theta)
    (d.limitingMassJetField (theta,zp)) (d.limitingMassJetField (theta,d.branch theta.2))
  have hs:=(add_le_add heval hlim).trans
    (show Cf*(p:ℝ)^Af*Real.exp (-cf*(p:ℝ))+L*(Cz*(p:ℝ)^Az*Real.exp (-cz*(p:ℝ))) ≤
        C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) by
      convert Hsum p hp1 using 1 <;> ring)
  exact htri.trans hs

end LimitingStandingData
end DepthPaper
