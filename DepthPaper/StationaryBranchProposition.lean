module

public import DepthPaper.StationaryCouplingSlope
public import DepthPaper.DegreeExponentialUniformConvergence
public import DepthPaper.StandingCutoffData

@[expose] public section


/-! Literal Proposition 4.5: all-depth actual stationary branches, their
C² limits, the coupling curve and its unique inverse mass. Standing
choices are constructed from the genuine nondegenerate seed. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1800000

def StationaryBranchesTarget (Ξ:AdmissibleCovariance) {r:ℕ} (seed:AtomicPoint r):Prop:=
  ∃d:LimitingStandingData Ξ seed,
    (∀j:ℕ,j ≤ 2→
      TendstoUniformlyOn (fun p theta=>iteratedFDeriv ℝ j
        (fun u=>d.stationaryBranch p u-d.branch u.2) theta) (fun _=>0)
        (atTop⊓𝓟 {p:ℕ|Even p}) d.parameterWindow) ∧
    (∀j:ℕ,j ≤ 2→
      TendstoUniformlyOn (fun p theta=>iteratedFDeriv ℝ j
        (fun u:ℝ×ℝ=>d.stationaryMassFunction p u-
          (u.1-pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) u.2)/2) theta)
        (fun _=>0) (atTop⊓𝓟 {p:ℕ|Even p}) d.parameterWindow) ∧
    (∀j:ℕ,j ≤ 2→
      TendstoUniformlyOn (fun p m=>iteratedFDeriv ℝ j (fun u=>d.couplingCurve p u-
        pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) u) m) (fun _=>0)
        (atTop⊓𝓟 {p:ℕ|Even p}) (Icc d.massLower 1)) ∧
    Tendsto (fun p=>d.couplingCurve p 1) (atTop⊓𝓟 {p:ℕ|Even p})
      (𝓝 (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1)) ∧
    ∀ᶠp:ℕ in atTop,∀heven:Even p,
      (∀theta∈d.parameterWindow,
        d.stationaryBranch p theta∈ball seed d.radius ∧
        partialGradient (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper)
          theta (d.stationaryBranch p theta)=0 ∧
        (∀z∈closedBall seed d.radius,
          partialGradient (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper) theta z=0→
          z=d.stationaryBranch p theta) ∧
        ContDiffAt ℝ ∞ (d.stationaryBranch p) theta ∧
        (∀z∈closedBall seed d.radius,∀v:AtomicPoint r,
          d.margin/2*‖v‖^2 ≤ partialHessian
            (stationaryReducedObjective Ξ p d.cutoff d.stripRateLower d.stripRateUpper) theta z v v) ∧
        ContDiffAt ℝ ∞ (d.stationaryMassFunction p) theta ∧
        1/4 ≤ fderiv ℝ (d.stationaryMassFunction p) theta (1,0)) ∧
      (∀m∈Icc d.massLower 1,
        d.couplingCurve p m∈Ioo d.couplingLower d.couplingUpper ∧
        d.stationaryMassFunction p (d.couplingCurve p m,m)=0 ∧
        (∀lam∈Icc d.couplingLower d.couplingUpper,
          d.stationaryMassFunction p (lam,m)=0→lam=d.couplingCurve p m) ∧
        ContDiffAt ℝ ∞ (d.couplingCurve p) m ∧ deriv (d.couplingCurve p) m ≤ -d.slope) ∧
      StrictAntiOn (d.couplingCurve p) (Icc d.massLower 1) ∧
      (∀lam∈Ioc (d.couplingCurve p 1)
        (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1+d.couplingMargin),
        d.bifurcatingMass p lam∈Ioo d.massLower 1 ∧
        d.couplingCurve p (d.bifurcatingMass p lam)=lam ∧
        (∀m∈Icc d.massLower 1,d.couplingCurve p m=lam→m=d.bifurcatingMass p lam))

theorem stationary_branches (Ξ:AdmissibleCovariance) {r:ℕ} (seed:AtomicPoint r)
    (hz:IsAtomicPoint seed) (hnd:Nondegenerate Ξ seed hz):StationaryBranchesTarget Ξ seed:=by
  obtain ⟨d⟩:=exists_limitingStandingData Ξ seed hz hnd
  obtain ⟨_,_,_,_,_,Hz⟩:=d.stationaryBranch_eventually
  obtain ⟨_,_,_,_,_,Hreg⟩:=d.stationaryBranch_regular_error_eventually
  obtain ⟨Cf,hCf,Af,cf,hcf,Hmass⟩:=d.stationaryMassFunction_C2_exponential_error
  obtain ⟨_,_,_,_,_,Hroot⟩:=d.couplingCurve_eventually
  have Hsmall:∀ᶠp:ℕ in atTop,Cf*(p:ℝ)^Af*Real.exp (-cf*(p:ℝ)) ≤ 1/4:=
    (tendsto_nat_polynomial_exp Cf cf Af hcf).eventually
      (eventually_le_nhds (show (0:ℝ) < 1/4 by norm_num))
  refine ⟨d,d.stationaryBranch_C2_uniform_limit,d.stationaryMassFunction_C2_uniform_limit,
    d.couplingCurve_C2_uniform_limit,d.couplingCurve_critical_limit,?_⟩
  filter_upwards [Hz,Hreg,Hmass,Hroot,Hsmall,d.couplingCurve_slope_eventually,
    d.bifurcatingMass_eventually] with p hz hr hm hroot hsmall hs hb heven
  refine ⟨?_,?_,(hb heven).1,(hb heven).2⟩
  · intro theta ht
    have hzs:=hz heven theta ht
    have hms:=hm heven theta ht
    have he:=d.stationaryMassFunction_coupling_partial_error p theta ht hms.1 (hms.2 1 (by norm_num))
    have hh:=neg_le_abs (fderiv ℝ (d.stationaryMassFunction p) theta (1,0)-1/2)
    exact ⟨hzs.1,hzs.2.1,hzs.2.2.1,(hr heven theta ht).1,hzs.2.2.2.2,hms.1,by linarith⟩
  · intro m hmem
    have hrt:=hroot heven m hmem
    exact ⟨hrt.1,hrt.2.1,hrt.2.2.2.2.2,(hs heven m hmem).1,(hs heven m hmem).2⟩

end DepthPaper
