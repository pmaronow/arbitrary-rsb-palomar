module

public import DepthPaper.StationaryLowerSmooth
public import DepthPaper.StationaryLimitingBounds
public import DepthPaper.StationaryPotentialComparison

@[expose] public section


/-! Quantitative C² convergence of the actual lower stationary family.
The fourth limiting jet is bounded on the genuine compact chart box. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 64

namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

theorem limitingBranch_eventually_stationary (d:LimitingStandingData Ξ seed)
    (theta:ℝ×ℝ) (ht:theta∈d.parameterWindow) :
    ∀ᶠu in 𝓝 theta,partialGradient (stationaryLimitingObjective Ξ) u (d.branch u.2)=0 := by
  have hmp:0 < theta.2 := d.massLower_mem.1.trans_le ht.2.1
  have hmass:∀ᶠu in 𝓝 theta,u.2∈d.massDomain :=
    continuousAt_snd.eventually (d.massDomain_open.mem_nhds (d.massWindow_subset ht.2))
  have hpos:∀ᶠu in 𝓝 theta,0 < u.2 :=
    continuousAt_snd.eventually (isOpen_Ioi.mem_nhds hmp)
  filter_upwards [hmass,hpos] with u hu hm
  obtain ⟨hz,hnd⟩:=d.branch_nondegenerate_domain u.2 hu
  rw [stationaryLimitingObjective_gradient Ξ _ hz u hm,
    fderiv_limitingAtomicPhi_locations Ξ (d.branch u.2) hz u.2 hm,
    fderiv_atomicFunctional_eq_zero_of_minimizer _ (d.branch u.2) hz hnd.1,smul_zero]

theorem stationaryBranch_C2_exponential_error (d:LimitingStandingData Ξ seed) :
    ∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧
      ∀ᶠp:ℕ in atTop,∀heven:Even p,∀theta∈d.parameterWindow,∀j:ℕ,j ≤ 2→
        ‖iteratedFDeriv ℝ j (fun u=>d.stationaryBranch p u-d.branch u.2) theta‖ ≤
          C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  obtain ⟨Cf,hCf,A,c,hc,Hf⟩:=d.stationaryBranch_regular_error_eventually
  obtain ⟨_,_,_,_,_,Hz⟩:=d.stationaryBranch_eventually
  obtain ⟨B2,hB2,HB2⟩:=d.boundedSmoothOn_stationaryLimitingObjective.bound 2
  obtain ⟨B3,hB3,HB3⟩:=d.boundedSmoothOn_stationaryLimitingObjective.bound 3
  obtain ⟨B4,hB4,HB4⟩:=d.boundedSmoothOn_stationaryLimitingObjective.bound 4
  let D:ℝ:=1+B2+B3+B4
  have hD:0 ≤ D := by dsimp [D];linarith
  let κ:ℝ:=d.margin/2
  have hκ:0 < κ := by dsimp [κ];linarith [d.margin_pos]
  let K1:ℝ:=(1+D/κ)*max 1 ((D+1)/κ)/κ
  let K2:ℝ:=(1+D/κ)*(max 1 ((D+1)/κ))^2/κ*(1+3*(D+1)/κ)
  let K:ℝ:=1+1/κ+K1+K2
  have hK1:0 ≤ K1 := by dsimp [K1];positivity
  have hK2:0 ≤ K2 := by dsimp [K2];positivity
  have hK:0 < K := by dsimp [K];positivity
  have Hsmall:∀ᶠp:ℕ in atTop,Cf*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) ≤ 1 :=
    (tendsto_nat_polynomial_exp Cf c A hc).eventually
      (eventually_le_nhds (show (0:ℝ) < 1 by norm_num))
  refine ⟨K*Cf,mul_pos hK hCf,A,c,hc,?_⟩
  filter_upwards [Hf,Hz,Hsmall] with p hf hz hsmall
  intro heven theta ht j hj
  have hreg:=hf heven theta ht
  have hsel:=hz heven theta ht
  have hmp:0 < theta.2 := d.massLower_mem.1.trans_le ht.2.1
  have hq:=hreg.1
  have hr:ContDiffAt ℝ ∞ (fun u:ℝ×ℝ=>d.branch u.2) theta :=
    (d.branch_smooth.contDiffAt (d.massDomain_open.mem_nhds
      (d.massWindow_subset ht.2))).comp theta contDiffAt_snd
  have hqs:d.stationaryBranch p theta∈closedBall seed d.radius := ball_subset_closedBall hsel.1
  have hrs:d.branch theta.2∈closedBall seed d.radius := by
    rw [mem_closedBall]
    linarith [d.branch_close theta.2 ht.2,d.radius_pos]
  have hg (z:AtomicPoint r) (hz:z∈closedBall seed d.radius):
      ContDiffAt ℝ ∞ (stationaryLimitingObjective Ξ) (theta,z) :=
    contDiffAt_stationaryLimitingObjective Ξ z (d.ball_valid z hz) theta hmp
  have hBG (z:AtomicPoint r) (hz:z∈closedBall seed d.radius) (v:AtomicPoint r):
      κ*‖v‖^2 ≤ partialHessian (stationaryLimitingObjective Ξ) theta z v v := by
    rw [stationaryLimitingObjective_hessian Ξ z (d.ball_valid z hz) theta hmp,
      ←limitingAtomicPhi_hessian_eq Ξ z (d.ball_valid z hz) theta.2 hmp]
    exact (by dsimp [κ];nlinarith [sq_nonneg ‖v‖,d.margin_pos] :
      κ*‖v‖^2 ≤ d.margin*‖v‖^2).trans (d.hessian_margin z hz theta.2 ht.2 v)
  have hb (z:AtomicPoint r) (hz:z∈closedBall seed d.radius) (i:ℕ) (hi:2 ≤ i) (hi4:i ≤ 4):
      ‖iteratedFDeriv ℝ i (stationaryLimitingObjective Ξ) (theta,z)‖ ≤ D := by
    have hw:(theta,z)∈d.stationaryInputWindow := ⟨ht,hz⟩
    interval_cases i
    · exact (HB2 (theta,z) hw).trans (by dsimp [D];linarith)
    · exact (HB3 (theta,z) hw).trans (by dsimp [D];linarith)
    · exact (HB4 (theta,z) hw).trans (by dsimp [D];linarith)
  have hs:=stationary_potential_C2_comparison
    (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper)
    (stationaryLimitingObjective Ξ) (closedBall seed d.radius) (convex_closedBall _ _)
    hq hr hqs hrs hreg.2.1 hg
    (hreg.2.2.2.2.mono (fun _ hu=>hu.2)) (d.limitingBranch_eventually_stationary theta ht)
    hκ hD ⟨by positivity,hsmall⟩ hreg.2.2.1 hBG hb
    (fun z hz i _ hi=>hreg.2.2.2.1 z hz i hi)
  have he:Cf*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) ≥ 0 := by positivity
  have hKs:1/κ ≤ K ∧ K1 ≤ K ∧ K2 ≤ K := by
    have hi:0 ≤ 1/κ := by positivity
    dsimp only [K]
    exact ⟨by linarith,by linarith,by linarith⟩
  have hbound:‖iteratedFDeriv ℝ j (fun u=>d.stationaryBranch p u-d.branch u.2) theta‖ ≤
      (Cf*(p:ℝ)^A*Real.exp (-c*(p:ℝ)))*K := by
    interval_cases j
    · simpa only [norm_iteratedFDeriv_zero] using hs.1.trans
        (by convert mul_le_mul_of_nonneg_left hKs.1 he using 1 <;> ring)
    · rw [fun_iteratedFDeriv_sub_apply (hq.of_le (by simp)) (hr.of_le (by simp))]
      exact hs.2.1.trans (by
        convert mul_le_mul_of_nonneg_left hKs.2.1 he using 1 <;> dsimp [K1] <;> ring)
    · rw [fun_iteratedFDeriv_sub_apply (hq.of_le (by simp)) (hr.of_le (by simp))]
      exact hs.2.2.trans (by
        convert mul_le_mul_of_nonneg_left hKs.2.2 he using 1 <;> dsimp [K2] <;> ring)
  exact hbound.trans_eq (by ring)

end LimitingStandingData
end DepthPaper
