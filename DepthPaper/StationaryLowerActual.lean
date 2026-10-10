module

public import DepthPaper.StationaryBranchExistence
public import DepthPaper.LimitingStandingData

@[expose] public section


/-! A nondegenerate seed alone constructs the standing choices and yields
actual unique lower stationary configurations for all large even degrees. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1400000

namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

def stationaryBranch (d:LimitingStandingData Ξ seed) (p:ℕ) : (ℝ×ℝ)→AtomicPoint r :=
  stationaryLowerBranch Ξ p d.cutoff d.stripRateLower d.stripRateUpper seed d.radius

def parameterWindow (d:LimitingStandingData Ξ seed) : Set (ℝ×ℝ) :=
  Icc d.couplingLower d.couplingUpper×ˢIcc d.massLower 1

theorem stationaryBranch_eventually (d:LimitingStandingData Ξ seed) :
    ∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧
      ∀ᶠp:ℕ in atTop,∀heven:Even p,∀theta∈d.parameterWindow,
        d.stationaryBranch p theta∈ball seed d.radius ∧
        partialGradient (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper)
          theta (d.stationaryBranch p theta)=0 ∧
        (∀z∈closedBall seed d.radius,
          partialGradient (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper) theta z=0→
          z=d.stationaryBranch p theta) ∧
        ‖d.stationaryBranch p theta-d.branch theta.2‖ ≤ C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) ∧
        (∀z∈closedBall seed d.radius,∀v:AtomicPoint r,
          d.margin/2*‖v‖^2 ≤ partialHessian
            (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper) theta z v v) := by
  obtain ⟨C,hC,A,c,hc,H⟩:=stationary_lower_branch_eventually Ξ seed d.radius d.margin
    d.radius_pos d.margin_pos d.ball_valid d.massLower_mem d.couplingLower_pos
    d.couplingLower_le_upper d.cutoff_mem d.ball_below_cutoff d.strip_rates.1
    d.strip_rates.2.1 d.strip_rates.2.2 d.branch (fun m hm=>(d.branch_close m hm).le)
    d.branch_stationary d.hessian_margin
  refine ⟨C,hC,A,c,hc,?_⟩
  filter_upwards [H] with p hp heven theta htheta
  exact hp heven theta htheta.1 htheta.2

theorem stationaryBranch_uniform_limit (d:LimitingStandingData Ξ seed) :
    TendstoUniformlyOn d.stationaryBranch (fun theta:ℝ×ℝ=>d.branch theta.2)
      (atTop⊓𝓟 {p:ℕ|Even p}) d.parameterWindow := by
  obtain ⟨C,hC,A,c,hc,H⟩:=d.stationaryBranch_eventually
  have H':∀ᶠp:ℕ in atTop⊓𝓟 {p:ℕ|Even p},∀theta∈d.parameterWindow,
      ‖d.stationaryBranch p theta-d.branch theta.2‖ ≤ C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
    rw [eventually_inf_principal]
    filter_upwards [H] with p hp heven theta ht
    exact (hp heven theta ht).2.2.2.1
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hbound:∀ᶠp:ℕ in atTop,C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) < ε :=
    (tendsto_nat_polynomial_exp C c A hc).eventually (eventually_lt_nhds hε)
  filter_upwards [H',hbound.filter_mono inf_le_left] with p hp hb theta ht
  simpa only [dist_eq_norm,norm_sub_rev] using (hp theta ht).trans_lt hb

end LimitingStandingData

theorem exists_actual_stationary_lower_family (Ξ:AdmissibleCovariance) {r:ℕ}
    (seed:AtomicPoint r) (hz:IsAtomicPoint seed) (hnd:Nondegenerate Ξ seed hz) :
    ∃d:LimitingStandingData Ξ seed,∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧
      ∀ᶠp:ℕ in atTop,∀heven:Even p,∀theta∈d.parameterWindow,
        d.stationaryBranch p theta∈ball seed d.radius ∧
        partialGradient (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper)
          theta (d.stationaryBranch p theta)=0 ∧
        (∀z∈closedBall seed d.radius,
          partialGradient (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper) theta z=0→
          z=d.stationaryBranch p theta) ∧
        ‖d.stationaryBranch p theta-d.branch theta.2‖ ≤ C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) ∧
        (∀z∈closedBall seed d.radius,∀v:AtomicPoint r,
          d.margin/2*‖v‖^2 ≤ partialHessian
            (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper) theta z v v) := by
  obtain ⟨d⟩:=exists_limitingStandingData Ξ seed hz hnd
  exact ⟨d,d.stationaryBranch_eventually⟩

end DepthPaper
