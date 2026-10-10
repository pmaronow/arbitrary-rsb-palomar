module

public import GeneralDepthPaper.RevisedSectionFourBranches
public import GeneralDepthPaper.RevisedSectionFourEnvelope

@[expose] public section

/-! Complete revised Proposition 4.5, including the actual optimized
objective and all mixed derivatives through order three. All standing
choices are constructed from the paper seed; Hessian positivity is a
proved dependency and is not an additional hypothesis. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1800000

theorem revised_stationary_branches (Ξ:AdmissibleCovariance) {r:ℕ}
    (seed:AtomicPoint r) (hz:IsAtomicPoint seed) (hND:PaperNondegenerate Ξ seed hz)
    (hsub:Ξ.IsSubcritical) :
    ∃d:LimitingStandingData Ξ seed,
      (    (∀j:ℕ,j≤2→
      TendstoUniformlyOn (fun p theta=>iteratedFDeriv ℝ j
        (fun u=>d.stationaryBranch p u-d.branch u.2) theta) (fun _=>0)
        (atTop⊓𝓟 {p:ℕ|Even p}) d.revisedParameterWindow) ∧
    (∀j:ℕ,j≤2→
      TendstoUniformlyOn (fun p theta=>iteratedFDeriv ℝ j
        (fun u:ℝ×ℝ=>d.stationaryMassFunction p u-
          (u.1-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) u.2)/2) theta)
        (fun _=>0) (atTop⊓𝓟 {p:ℕ|Even p}) d.revisedParameterWindow) ∧
    ∀ᶠp:ℕ in atTop,∀he:Even p,∀theta∈d.revisedParameterWindow,
      d.stationaryBranch p theta∈ball seed d.radius ∧
      partialGradient (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper)
        theta (d.stationaryBranch p theta)=0 ∧
      (∀z∈closedBall seed d.radius,
        partialGradient (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper)
          theta z=0→z=d.stationaryBranch p theta) ∧
      ContDiffAt ℝ ∞ (d.stationaryBranch p) theta ∧
      (∀z∈closedBall seed d.radius,∀v:AtomicPoint r,
        d.margin/2*‖v‖^2≤partialHessian
          (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper) theta z v v) ∧
      ContDiffAt ℝ ∞ (d.stationaryMassFunction p) theta ∧
      d.stationaryMassFunction p theta=
        fderiv ℝ (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper)
          (theta,d.stationaryBranch p theta) ((0,1),0) ∧
      HasDerivAt (fun m=>d.revisedScalarObjective p (theta.1,m))
        (d.stationaryMassFunction p theta) theta.2) ∧
      (∀j:ℕ,j≤3→TendstoUniformlyOn
        (fun p theta=>iteratedFDeriv ℝ j
          (fun u=>d.revisedScalarObjective p u-revisedLimitingScalarObjective Ξ u) theta)
        (fun _=>0) (atTop⊓𝓟 {p:ℕ|Even p}) d.revisedParameterWindow) ∧
      (∀ᶠp:ℕ in atTop,∀he:Even p,∀theta∈d.revisedParameterWindow,
        HasFDerivAt (d.revisedScalarObjective p)
          (revisedParameterGradientProjection
            (fderiv ℝ (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper)
              (theta,d.stationaryBranch p theta))) theta) ∧
      ∃C:ℝ,0<C ∧ ∃A:ℕ,∃c:ℝ,0<c ∧
        ∀ᶠp:ℕ in atTop,∀he:Even p,∀theta∈d.revisedParameterWindow,
          ContDiffAt ℝ ∞ (d.revisedScalarObjective p) theta ∧
          ∀j:ℕ,j≤3→‖iteratedFDeriv ℝ j
            (fun u=>d.revisedScalarObjective p u-revisedLimitingScalarObjective Ξ u) theta‖≤
              C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  obtain ⟨d⟩:=exists_limitingStandingData Ξ seed hz
    (nondegenerate_of_paperNondegenerate Ξ seed hz hND hsub)
  obtain ⟨C,hC,A,c,hc,HC⟩:=d.revisedScalarObjective_C3_exponential_error
  refine ⟨d,d.revised_stationary_branches_data,
    (fun j hj=>(d.revisedScalarObjective_C3_uniform_limit j hj).mono d.revisedParameterWindow_subset),
    ?_,C,hC,A,c,hc,?_⟩
  · filter_upwards [d.revisedScalarObjective_fullDerivative_eventually] with p hp he theta ht
    exact hp he theta (d.revisedParameterWindow_subset ht)
  · filter_upwards [HC] with p hp he theta ht
    exact hp he theta (d.revisedParameterWindow_subset ht)

end GeneralDepthPaper
