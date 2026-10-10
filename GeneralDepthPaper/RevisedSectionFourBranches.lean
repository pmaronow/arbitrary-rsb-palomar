module

public import GeneralDepthPaper.RevisedSectionFourScalar

@[expose] public section

/-! Revised Proposition 4.5: actual lower stationary coordinates, uniform
C² convergence, positive lower-coordinate Hessians and the genuine mass
response. Optimized objective C³ convergence is proved separately. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 1800000
namespace LimitingStandingData
variable {Ξ:AdmissibleCovariance} {r:ℕ} {seed:AtomicPoint r}

/-- The coordinate dimension 2r may be zero; no extra positive-depth
assumption is made. All stationary and uniqueness equations are actual. -/
theorem revised_stationary_branches_data (d:LimitingStandingData Ξ seed) :
    (∀j:ℕ,j≤2→
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
        (d.stationaryMassFunction p theta) theta.2 := by
  obtain ⟨_,_,_,_,_,Hz⟩:=d.stationaryBranch_eventually
  obtain ⟨_,_,_,_,_,Hreg⟩:=d.stationaryBranch_regular_error_eventually
  obtain ⟨_,_,_,_,_,Hmass⟩:=d.stationaryMassFunction_C2_exponential_error
  refine ⟨fun j hj=>(d.stationaryBranch_C2_uniform_limit j hj).mono d.revisedParameterWindow_subset,
    fun j hj=>(d.stationaryMassFunction_C2_uniform_limit j hj).mono d.revisedParameterWindow_subset,?_⟩
  filter_upwards [Hz,Hreg,Hmass,d.revisedScalarObjective_massDerivative_eventually]
    with p hz hr hm hJ he theta ht
  have htold:=d.revisedParameterWindow_subset ht
  have hzs:=hz he theta htold
  exact ⟨hzs.1,hzs.2.1,hzs.2.2.1,(hr he theta htold).1,hzs.2.2.2.2,
    (hm he theta htold).1,rfl,hJ he theta htold⟩

end LimitingStandingData
end GeneralDepthPaper
