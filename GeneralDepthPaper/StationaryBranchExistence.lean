module

public import GeneralDepthPaper.StationaryObjectiveCoordinates
public import GeneralDepthPaper.LimitingCouplingWindow

@[expose] public section


/-! The actual reduced Parisi functional has a unique stationary lower
configuration on the fixed coordinate ball for every sufficiently large
even degree. Its displacement is controlled by the verified C³ error. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 64

def stationaryLowerBranch (Ξ:AdmissibleCovariance) {r:ℕ} (p:ℕ) (qc cQ CQ:ℝ)
    (center:AtomicPoint r) (R:ℝ) : (ℝ×ℝ)→AtomicPoint r :=
  coerciveBallStationarySelector (stationaryReducedObjective Ξ p qc cQ CQ) center R

theorem stationary_lower_branch_of_small_error (Ξ:AdmissibleCovariance) {r:ℕ}
    (p:ℕ) (qc cQ CQ:ℝ) (center z0:AtomicPoint r) (R κ:ℝ) (theta:ℝ×ℝ)
    (hR:0 < R) (hκ:0 < κ) (hm:0 < theta.2)
    (hvalid:∀z∈closedBall center R,IsAtomicPoint z)
    (hz0:dist z0 center ≤ R/2)
    (hzero:partialGradient (stationaryLimitingObjective Ξ) theta z0=0)
    (hH:∀z∈closedBall center R,∀v:AtomicPoint r,
      κ*‖v‖^2 ≤ partialHessian (stationaryLimitingObjective Ξ) theta z v v)
    (hsm:∀z∈closedBall center R,ContDiffAt ℝ ∞ (stationaryReducedObjective Ξ p qc cQ CQ) (theta,z))
    {ε:ℝ} (hε:0 ≤ ε) (hεH:ε ≤ κ/2) (hεg:ε < κ*R/8)
    (hjets:∀z∈closedBall center R,∀j:ℕ,j ≤ 2→
      ‖iteratedFDeriv ℝ j (fun w=>stationaryReducedObjective Ξ p qc cQ CQ w-
        stationaryLimitingObjective Ξ w) (theta,z)‖ ≤ ε) :
    stationaryLowerBranch Ξ p qc cQ CQ center R theta∈ball center R ∧
    partialGradient (stationaryReducedObjective Ξ p qc cQ CQ) theta
      (stationaryLowerBranch Ξ p qc cQ CQ center R theta)=0 ∧
    (∀z∈closedBall center R,partialGradient (stationaryReducedObjective Ξ p qc cQ CQ) theta z=0→
      z=stationaryLowerBranch Ξ p qc cQ CQ center R theta) ∧
    ‖stationaryLowerBranch Ξ p qc cQ CQ center R theta-z0‖ ≤ 2*ε/κ ∧
    (∀z∈closedBall center R,∀v:AtomicPoint r,
      κ/2*‖v‖^2 ≤ partialHessian (stationaryReducedObjective Ξ p qc cQ CQ) theta z v v) := by
  let f:=stationaryReducedObjective Ξ (r:=r) p qc cQ CQ
  let g:=stationaryLimitingObjective Ξ (r:=r)
  have hg (z:AtomicPoint r) (hz:z∈closedBall center R):ContDiffAt ℝ ∞ g (theta,z) :=
    contDiffAt_stationaryLimitingObjective Ξ z (hvalid z hz) theta hm
  have hz0ball:z0∈closedBall center R := by
    rw [mem_closedBall]
    linarith
  have hgrad:‖partialGradient f theta z0‖ ≤ ε := by
    have hh:=(norm_partialGradient_sub_le (hsm z0 hz0ball) (hg z0 hz0ball)).trans
      (hjets z0 hz0ball 1 (by norm_num))
    change ‖partialGradient f theta z0-partialGradient g theta z0‖ ≤ ε at hh
    change partialGradient g theta z0=0 at hzero
    simpa only [hzero,sub_zero] using hh
  have hcoercive:∀z∈closedBall center R,∀v:AtomicPoint r,
      κ/2*‖v‖^2 ≤ partialHessian f theta z v v := by
    intro z hz
    apply bilinear_coercivity_of_norm_close (partialHessian f theta z)
      (partialHessian g theta z) hκ
    · intro v hv
      simpa only [hv,one_pow,mul_one] using hH z hz v
    · exact ((norm_partialHessian_sub_le (hsm z hz) (hg z hz)).trans
        (hjets z hz 2 (by norm_num))).trans hεH
  have hspec:=coerciveBallStationarySelector_spec f center z0 R (R/2) (κ/2) theta
    (by positivity) (by positivity) (by linarith) hsm hcoercive
    (by have hh:=hgrad.trans_lt hεg; convert hh using 1 <;> ring)
  refine ⟨hspec.1,hspec.2.1,hspec.2.2.2.1,?_,hcoercive⟩
  have he:‖partialGradient f theta z0‖/(κ/2) ≤ 2*ε/κ := by
    apply (div_le_div_of_nonneg_right hgrad (by positivity)).trans_eq
    field_simp
  exact hspec.2.2.2.2.trans he

theorem stationary_lower_branch_eventually (Ξ:AdmissibleCovariance) {r:ℕ}
    (center:AtomicPoint r) (R κ:ℝ) (hR:0 < R) (hκ:0 < κ)
    (hvalid:∀z∈closedBall center R,IsAtomicPoint z)
    {e lo hi qc cQ CQ:ℝ} (he:e∈Ioo (0:ℝ) 1) (hlo:0 < lo) (hLH:lo ≤ hi)
    (hc:qc∈Ioo (0:ℝ) 1) (hcut:∀z∈closedBall center R,atomicLocation z (Fin.last r) < qc)
    (hcQ:0 < cQ) (hclo:cQ < e^2*lo/2) (hChi:hi/2 < CQ)
    (z0:ℝ→AtomicPoint r)
    (hz0:∀m∈Icc e 1,dist (z0 m) center ≤ R/2)
    (hzero:∀m∈Icc e 1,fderiv ℝ (fun y=>limitingAtomicPhi Ξ r (y,m)) (z0 m)=0)
    (hH:∀z∈closedBall center R,∀m∈Icc e 1,∀v:AtomicPoint r,
      κ*‖v‖^2 ≤ (fderiv ℝ (fun u=>fderiv ℝ (fun w=>limitingAtomicPhi Ξ r (w,m)) u) z v) v) :
    ∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧
      ∀ᶠp:ℕ in atTop,∀heven:Even p,∀theta:ℝ×ℝ,
        theta.1∈Icc lo hi→theta.2∈Icc e 1→
        stationaryLowerBranch Ξ p qc cQ CQ center R theta∈ball center R ∧
        partialGradient (stationaryReducedObjective Ξ p qc cQ CQ) theta
          (stationaryLowerBranch Ξ p qc cQ CQ center R theta)=0 ∧
        (∀z∈closedBall center R,partialGradient (stationaryReducedObjective Ξ p qc cQ CQ) theta z=0→
          z=stationaryLowerBranch Ξ p qc cQ CQ center R theta) ∧
        ‖stationaryLowerBranch Ξ p qc cQ CQ center R theta-z0 theta.2‖ ≤
          C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) ∧
        (∀z∈closedBall center R,∀v:AtomicPoint r,
          κ/2*‖v‖^2 ≤ partialHessian (stationaryReducedObjective Ξ p qc cQ CQ) theta z v v) := by
  have hK:IsCompact (closedBall center R) := isCompact_closedBall _ _
  obtain ⟨C,hC,A,c,hcpos,H⟩:=reduced_endpoint_C3_exponential_bound
    Ξ hK hvalid he hlo hLH hc hcut hcQ hclo hChi
  have hsmall:∀ᶠp:ℕ in atTop,C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) < min (κ/2) (κ*R/8) :=
    (tendsto_nat_polynomial_exp C c A hcpos).eventually
      (eventually_lt_nhds (show (0:ℝ) < min (κ/2) (κ*R/8) by positivity))
  have hCQ:cQ < CQ := by
    have hh:=mul_le_mul_of_nonneg_right (show e^2 ≤ 1 by nlinarith [he.1,he.2]) hlo.le
    nlinarith
  refine ⟨2*C/κ,by positivity,A,c,hcpos,?_⟩
  filter_upwards [H,hsmall,eventually_ge_atTop 1,
    distinguished_endpoint_smooth_eventually Ξ hK hvalid he hlo hLH hc hcut hcQ hclo hChi]
    with p hp hb hp1 hdom
  intro heven theta hl hm
  have hmp:0 < theta.2 := he.1.trans_le hm.1
  have hsm:∀z∈closedBall center R,
      ContDiffAt ℝ ∞ (stationaryReducedObjective Ξ p qc cQ CQ) (theta,z) := by
    intro z hz
    exact (contDiffAt_reducedEndpointFunctional Ξ p qc cQ CQ hCQ (by omega) (hvalid z hz)
      (hdom heven (z,(theta.2,theta.1)) hz hm hl).1).comp (theta,z)
        stationaryParameterAssembly.contDiff.contDiffAt
  have hz0b:z0 theta.2∈closedBall center R := by rw [mem_closedBall];linarith [hz0 theta.2 hm]
  have hzg:partialGradient (stationaryLimitingObjective Ξ) theta (z0 theta.2)=0 := by
    rw [stationaryLimitingObjective_gradient Ξ _ (hvalid _ hz0b) theta hmp]
    exact hzero theta.2 hm
  have hHH:∀z∈closedBall center R,∀v:AtomicPoint r,
      κ*‖v‖^2 ≤ partialHessian (stationaryLimitingObjective Ξ) theta z v v := by
    intro z hz v
    rw [stationaryLimitingObjective_hessian Ξ z (hvalid _ hz) theta hmp,
      ←limitingAtomicPhi_hessian_eq Ξ z (hvalid _ hz) theta.2 hmp]
    exact hH z hz theta.2 hm v
  have hjets:∀z∈closedBall center R,∀j:ℕ,j ≤ 2→
      ‖iteratedFDeriv ℝ j (fun w=>stationaryReducedObjective Ξ p qc cQ CQ w-
        stationaryLimitingObjective Ξ w) (theta,z)‖ ≤ C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
    intro z hz j hj
    have hf:=hsm z hz
    have hg:=contDiffAt_stationaryLimitingObjective Ξ z (hvalid z hz) theta hmp
    have hr:=contDiffAt_reducedEndpointFunctional Ξ p qc cQ CQ hCQ (by omega) (hvalid z hz)
      (hdom heven (z,(theta.2,theta.1)) hz hm hl).1
    exact (norm_stationaryObjective_difference_jet_le Ξ p qc cQ CQ theta z j
      (hr.sub (contDiffAt_limitingObjectiveCore Ξ (hvalid z hz) hmp))).trans
        (hp heven (z,(theta.2,theta.1)) hz hm hl j (by omega))
  have hs:=stationary_lower_branch_of_small_error Ξ p qc cQ CQ center (z0 theta.2) R κ theta
    hR hκ hmp hvalid (hz0 theta.2 hm) hzg hHH hsm (by positivity)
    (hb.trans_le (min_le_left _ _)).le (hb.trans_le (min_le_right _ _)) hjets
  refine ⟨hs.1,hs.2.1,hs.2.2.1,?_,hs.2.2.2.2⟩
  convert hs.2.2.2.1 using 1 <;> ring

end GeneralDepthPaper
