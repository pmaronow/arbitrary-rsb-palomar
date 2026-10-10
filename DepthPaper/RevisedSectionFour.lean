module

public import DepthPaper.RevisedGardnerTransition
public import GeneralDepthPaper.RevisedSectionFourWindows
public import GeneralDepthPaper.RevisedSectionFourStationarity
public import GeneralDepthPaper.RevisedSectionFourScalar
public import GeneralDepthPaper.RevisedSectionFourGeometry

@[expose] public section

/-! Revised finite-support covariance interface for the complete
Section 4 proof. Exact coefficient/covariance bridges preserve every
actual functional, state, variation and covariance derivative. -/
noncomputable section
open Set Filter Metric MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal ENNReal
namespace DepthPaper.RevisedSectionFour
open GeneralDepthPaper FourPapersCommon ColeHopfFoundation.ProbabilityTheory

theorem endpointReduction (Ξ:RevisedCovariance) {r:ℕ}
    (seed:GeneralDepthPaper.AtomicPoint r) (hz:GeneralDepthPaper.IsAtomicPoint seed)
    (hND:Ξ.Nondegenerate seed hz) (hsub:Ξ.IsSubcritical) :
    ∃d:GeneralDepthPaper.LimitingStandingData Ξ.toGeneralCovariance seed,
    ∃b:ℝ,0 < b ∧ ∃D:ℝ,0 < D ∧
      ∃Cq:ℝ,0 < Cq ∧ ∃Aq:ℕ,∃cq:ℝ,0 < cq ∧
      ∃Cf:ℝ,0 < Cf ∧ ∃Af:ℕ,∃cf:ℝ,0 < cf ∧ ∃P:ℕ,4 ≤ P ∧
        ∀p:ℕ,P ≤ p→∀heven:Even p,∃hp:4 ≤ p,∃hn:p∉Ξ.toGeneralCovariance.degrees,
          ∀theta:GeneralDepthPaper.HighDegreeLowerParameter r,∀hz:theta.1∈closedBall seed d.radius,
            theta.2.1∈Icc d.massLower 1→∀hlam:theta.2.2∈d.revisedCouplingWindow,
            let Ψ := Ξ.toGeneralCovariance.addHighDegree p hp heven hn theta.2.2 (d.couplingLower_pos.trans_le hlam.1)
            let Q := GeneralDepthPaper.distinguishedOverlap Ξ.toGeneralCovariance p d.cutoff d.stripRateLower d.stripRateUpper theta
            (Q:ℝ)=GeneralDepthPaper.distinguishedEndpoint Ξ.toGeneralCovariance p d.cutoff d.stripRateLower d.stripRateUpper theta ∧
            (Q:ℝ)∈Ioo (1-Real.exp (-d.stripRateLower*(p:ℝ))) (1-Real.exp (-d.revisedCouplingUpper*(p:ℝ))) ∧
            GeneralDepthPaper.Gamma Ψ (GeneralDepthPaper.twoLevelMeasure theta.1 (d.ball_valid _ hz) theta.2.1 Q) Q=(Q:ℝ) ∧
            (∀T:GeneralDepthPaper.Overlap,(T:ℝ)∈d.revisedEndpointStrip p→
              GeneralDepthPaper.Gamma Ψ (GeneralDepthPaper.twoLevelMeasure theta.1 (d.ball_valid _ hz) theta.2.1 T) T=(T:ℝ)→T=Q) ∧
            b*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-theta.2.1^2*theta.2.2*(p:ℝ)/2) ≤ 1-(Q:ℝ) ∧
            1-(Q:ℝ) ≤ D*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-theta.2.1^2*theta.2.2*(p:ℝ)/2) ∧
            ContDiffAt ℝ ∞ (GeneralDepthPaper.distinguishedEndpoint Ξ.toGeneralCovariance p d.cutoff d.stripRateLower d.stripRateUpper) theta ∧
            (∀j:ℕ,1 ≤ j→j ≤ 2→‖iteratedFDeriv ℝ j
              (GeneralDepthPaper.distinguishedEndpoint Ξ.toGeneralCovariance p d.cutoff d.stripRateLower d.stripRateUpper) theta‖ ≤ Cq*(p:ℝ)^Aq*Real.exp (-cq*(p:ℝ))) ∧
            ContDiffAt ℝ ∞ (GeneralDepthPaper.reducedEndpointFunctional Ξ.toGeneralCovariance p d.cutoff d.stripRateLower d.stripRateUpper) theta ∧
            GeneralDepthPaper.reducedEndpointFunctional Ξ.toGeneralCovariance p d.cutoff d.stripRateLower d.stripRateUpper theta=GeneralDepthPaper.twoLevelFunctional Ψ theta.1
              (d.ball_valid _ hz) theta.2.1 Q ∧
            fderiv ℝ (GeneralDepthPaper.reducedEndpointFunctional Ξ.toGeneralCovariance p d.cutoff d.stripRateLower d.stripRateUpper) theta=
              (fderiv ℝ (GeneralDepthPaper.endpointFunctionalChart Ξ.toGeneralCovariance p d.cutoff)
                (theta,GeneralDepthPaper.distinguishedEndpoint Ξ.toGeneralCovariance p d.cutoff d.stripRateLower d.stripRateUpper theta)).comp
                  (ContinuousLinearMap.inl ℝ (GeneralDepthPaper.HighDegreeLowerParameter r) ℝ) ∧
            (theta.2.1 < 1→0 < deriv (deriv (fun q=>GeneralDepthPaper.twoLevelFunctional Ψ theta.1 (d.ball_valid _ hz)
              theta.2.1 (projIcc 0 1 zero_le_one q))) Q) ∧
            (∀j:ℕ,j ≤ 3→‖iteratedFDeriv ℝ j
              (fun u=>GeneralDepthPaper.reducedEndpointFunctional Ξ.toGeneralCovariance p d.cutoff d.stripRateLower d.stripRateUpper u-GeneralDepthPaper.limitingObjectiveCore Ξ.toGeneralCovariance u)
                theta‖ ≤ Cf*(p:ℝ)^Af*Real.exp (-cf*(p:ℝ))) := by
  exact GeneralDepthPaper.revised_prepared_endpoint_root_and_reduction Ξ.toGeneralCovariance seed hz
    (RevisedCovariance.paperNondegenerate_toGeneralCovariance Ξ seed hz hND)
    (RevisedCovariance.isSubcritical_toGeneralCovariance Ξ hsub)

theorem stationaryBranches (Ξ:RevisedCovariance) {r:ℕ}
    (seed:GeneralDepthPaper.AtomicPoint r) (hz:GeneralDepthPaper.IsAtomicPoint seed)
    (hND:Ξ.Nondegenerate seed hz) (hsub:Ξ.IsSubcritical) :
    ∃d:GeneralDepthPaper.LimitingStandingData Ξ.toGeneralCovariance seed,
      (    (∀j:ℕ,j≤2→
      TendstoUniformlyOn (fun p theta=>iteratedFDeriv ℝ j
        (fun u=>d.stationaryBranch p u-d.branch u.2) theta) (fun _=>0)
        (atTop⊓𝓟 {p:ℕ|Even p}) d.revisedParameterWindow) ∧
    (∀j:ℕ,j≤2→
      TendstoUniformlyOn (fun p theta=>iteratedFDeriv ℝ j
        (fun u:ℝ×ℝ=>d.stationaryMassFunction p u-
          (u.1-GeneralDepthPaper.pressureEll (GeneralDepthPaper.scaledThermodynamicPressure Ξ.toGeneralCovariance.toEvenMixture) u.2)/2) theta)
        (fun _=>0) (atTop⊓𝓟 {p:ℕ|Even p}) d.revisedParameterWindow) ∧
    ∀ᶠp:ℕ in atTop,∀he:Even p,∀theta∈d.revisedParameterWindow,
      d.stationaryBranch p theta∈ball seed d.radius ∧
      GeneralDepthPaper.partialGradient (GeneralDepthPaper.stationaryReducedObjective Ξ.toGeneralCovariance p d.cutoff d.stripRateLower d.stripRateUpper)
        theta (d.stationaryBranch p theta)=0 ∧
      (∀z∈closedBall seed d.radius,
        GeneralDepthPaper.partialGradient (GeneralDepthPaper.stationaryReducedObjective Ξ.toGeneralCovariance p d.cutoff d.stripRateLower d.stripRateUpper)
          theta z=0→z=d.stationaryBranch p theta) ∧
      ContDiffAt ℝ ∞ (d.stationaryBranch p) theta ∧
      (∀z∈closedBall seed d.radius,∀v:GeneralDepthPaper.AtomicPoint r,
        d.margin/2*‖v‖^2≤GeneralDepthPaper.partialHessian
          (GeneralDepthPaper.stationaryReducedObjective Ξ.toGeneralCovariance p d.cutoff d.stripRateLower d.stripRateUpper) theta z v v) ∧
      ContDiffAt ℝ ∞ (d.stationaryMassFunction p) theta ∧
      d.stationaryMassFunction p theta=
        fderiv ℝ (GeneralDepthPaper.stationaryReducedObjective Ξ.toGeneralCovariance p d.cutoff d.stripRateLower d.stripRateUpper)
          (theta,d.stationaryBranch p theta) ((0,1),0) ∧
      HasDerivAt (fun m=>d.revisedScalarObjective p (theta.1,m))
        (d.stationaryMassFunction p theta) theta.2) ∧
      (∀j:ℕ,j≤3→TendstoUniformlyOn
        (fun p theta=>iteratedFDeriv ℝ j
          (fun u=>d.revisedScalarObjective p u-GeneralDepthPaper.revisedLimitingScalarObjective Ξ.toGeneralCovariance u) theta)
        (fun _=>0) (atTop⊓𝓟 {p:ℕ|Even p}) d.revisedParameterWindow) ∧
      (∀ᶠp:ℕ in atTop,∀he:Even p,∀theta∈d.revisedParameterWindow,
        HasFDerivAt (d.revisedScalarObjective p)
          (GeneralDepthPaper.revisedParameterGradientProjection
            (fderiv ℝ (GeneralDepthPaper.stationaryReducedObjective Ξ.toGeneralCovariance p d.cutoff d.stripRateLower d.stripRateUpper)
              (theta,d.stationaryBranch p theta))) theta) ∧
      ∃C:ℝ,0<C ∧ ∃A:ℕ,∃c:ℝ,0<c ∧
        ∀ᶠp:ℕ in atTop,∀he:Even p,∀theta∈d.revisedParameterWindow,
          ContDiffAt ℝ ∞ (d.revisedScalarObjective p) theta ∧
          ∀j:ℕ,j≤3→‖iteratedFDeriv ℝ j
            (fun u=>d.revisedScalarObjective p u-GeneralDepthPaper.revisedLimitingScalarObjective Ξ.toGeneralCovariance u) theta‖≤
              C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  exact GeneralDepthPaper.revised_stationary_branches Ξ.toGeneralCovariance seed hz
    (RevisedCovariance.paperNondegenerate_toGeneralCovariance Ξ seed hz hND)
    (RevisedCovariance.isSubcritical_toGeneralCovariance Ξ hsub)

theorem scalarBifurcation (Ξ:RevisedCovariance) {r:ℕ}
    (seed:GeneralDepthPaper.AtomicPoint r) (hz:GeneralDepthPaper.IsAtomicPoint seed)
    (hND:Ξ.Nondegenerate seed hz) (hsub:Ξ.IsSubcritical) :
    ∃d:GeneralDepthPaper.LimitingStandingData Ξ.toGeneralCovariance seed,
      Tendsto (fun p=>d.couplingCurve p 1) (atTop⊓𝓟 {p:ℕ|Even p})
        (𝓝 (GeneralDepthPaper.pressureEll (GeneralDepthPaper.scaledThermodynamicPressure Ξ.toGeneralCovariance.toEvenMixture) 1)) ∧
      ∀ᶠp:ℕ in atTop,∀he:Even p,
        (d.couplingCurve p 1∈Ioo d.couplingLower d.revisedCouplingUpper) ∧
        d.stationaryMassFunction p (d.couplingCurve p 1,1)=0 ∧
        (∀lam∈d.revisedCouplingWindow,
          (d.stationaryMassFunction p (lam,1)<0↔lam<d.couplingCurve p 1) ∧
          (d.stationaryMassFunction p (lam,1)=0↔lam=d.couplingCurve p 1) ∧
          (0<d.stationaryMassFunction p (lam,1)↔d.couplingCurve p 1<lam)) ∧
        (∀theta∈d.revisedParameterWindow,
          ContDiffAt ℝ ∞ (d.stationaryMassFunction p) theta ∧
          d.slope/2≤fderiv ℝ (d.stationaryMassFunction p) theta (0,1) ∧
          1/4≤fderiv ℝ (d.stationaryMassFunction p) theta (1,0) ∧
          HasDerivAt (fun m=>d.revisedScalarObjective p (theta.1,m))
            (d.stationaryMassFunction p theta) theta.2) ∧
        (∀lam∈d.revisedCouplingWindow,
          ∃!m:ℝ,m∈Icc d.massLower 1 ∧
            IsMinOn (fun u=>d.revisedScalarObjective p (lam,u)) (Icc d.massLower 1) m ∧
            (lam≤d.couplingCurve p 1→m=1) ∧
            (d.couplingCurve p 1<lam→m∈Ioo d.massLower 1 ∧
              d.stationaryMassFunction p (lam,m)=0) ∧
          (∀n∈Icc d.massLower 1,
            IsMinOn (fun u=>d.revisedScalarObjective p (lam,u)) (Icc d.massLower 1) n→n=m)) := by
  exact GeneralDepthPaper.revised_scalar_bifurcation Ξ.toGeneralCovariance seed hz
    (RevisedCovariance.paperNondegenerate_toGeneralCovariance Ξ seed hz hND)
    (RevisedCovariance.isSubcritical_toGeneralCovariance Ξ hsub)

theorem candidateGeometry (Ξ:RevisedCovariance) {r:ℕ}
    (seed:GeneralDepthPaper.AtomicPoint r) (hz:GeneralDepthPaper.IsAtomicPoint seed)
    (hND:Ξ.Nondegenerate seed hz) (hsub:Ξ.IsSubcritical) :
    ∃d:GeneralDepthPaper.LimitingStandingData Ξ.toGeneralCovariance seed,∃gamma:ℝ,0<gamma ∧
      (∀m:d.MassInterval,d.limitingVariation m 1≤ -5*gamma) ∧
      (∀m:d.MassInterval,∀q∈Icc d.cutoff 1,d.limitingVariation m q≤ -4*gamma) ∧
      (1/2:ℝ)*(∫q in d.cutoff..1,(1-q)*Ξ.second q)≤gamma ∧
      ∃L:ℝ,0<L ∧ L=10/d.massLower^2 ∧ 10≤d.massLower^2*L ∧
        ∀ᶠp:ℕ in atTop,4≤p ∧ ∀he:Even p,∃hp:4≤p,∃hn:p∉Ξ.toGeneralCovariance.degrees,
          ∀theta:ℝ×ℝ,∀ht:theta∈d.revisedParameterWindow,
            ∃hzp:GeneralDepthPaper.IsAtomicPoint (d.stationaryBranch p theta),
              let z:=d.stationaryBranch p theta
              let Ψ:=Ξ.toGeneralCovariance.addHighDegree p hp he hn theta.1 (d.couplingLower_pos.trans_le ht.1.1)
              let Q:=GeneralDepthPaper.distinguishedOverlap Ξ.toGeneralCovariance p d.cutoff d.stripRateLower d.stripRateUpper (z,(theta.2,theta.1))
              let μ:=GeneralDepthPaper.twoLevelMeasure z hzp theta.2 Q
              let a:=GeneralDepthPaper.logarithmicOverlapThreshold p theta.1 L
              ((μ:Measure GeneralDepthPaper.Overlap)=ENNReal.ofReal theta.2 • (GeneralDepthPaper.atomicMeasure z hzp:Measure GeneralDepthPaper.Overlap)+
                ENNReal.ofReal (1-theta.2) • Measure.dirac Q) ∧
              (theta.2=1→μ=GeneralDepthPaper.atomicMeasure z hzp) ∧
              (∀q∈(GeneralDepthPaper.atomicMeasure z hzp:Measure GeneralDepthPaper.Overlap).support,GeneralDepthPaper.firstVariation Ψ μ q=0) ∧
              (∀q∈(GeneralDepthPaper.atomicMeasure z hzp:Measure GeneralDepthPaper.Overlap).support,q≠⟨0,by norm_num⟩→
                deriv (GeneralDepthPaper.firstVariation Ψ μ) q=0) ∧
              deriv (GeneralDepthPaper.firstVariation Ψ μ) Q=0 ∧
              d.stationaryMassFunction p theta=GeneralDepthPaper.firstVariation Ψ μ Q ∧
              (∀q∈Icc (0:ℝ) d.cutoff,GeneralDepthPaper.firstVariation Ψ μ q≤0 ∧
                (GeneralDepthPaper.firstVariation Ψ μ q=0↔q∈FRSB.parisiSupport (GeneralDepthPaper.atomicMeasure z hzp))) ∧
              (∀i:Fin r,deriv (deriv (GeneralDepthPaper.firstVariation Ψ μ)) (z.1 i)<0) ∧
              GeneralDepthPaper.firstVariation Ψ μ d.cutoff≤ -3*gamma ∧
              d.cutoff<a ∧ a<(Q:ℝ) ∧ (Q:ℝ)<1 ∧
              theta.1*(p:ℝ)*a^(p-1)=(10/d.massLower^2)*Real.log (p:ℝ) ∧
              (∀t∈Ioo (0:ℝ) 1,theta.1*(p:ℝ)*t^(p-1)=(10/d.massLower^2)*Real.log (p:ℝ)→t=a) ∧
              (∀q∈Icc d.cutoff a,GeneralDepthPaper.firstVariation Ψ μ q≤ -gamma) ∧
              (∀q∈Icc a 1,derivWithin (GeneralDepthPaper.Gamma Ψ μ) (Icc (0:ℝ) 1) q≤1/2) ∧
              StrictMonoOn (GeneralDepthPaper.firstVariation Ψ μ) (Icc a (Q:ℝ)) ∧
              StrictAntiOn (GeneralDepthPaper.firstVariation Ψ μ) (Icc (Q:ℝ) 1) ∧
              deriv (deriv (GeneralDepthPaper.firstVariation Ψ μ)) Q<0 ∧
              (GeneralDepthPaper.firstVariation Ψ μ Q<0→
                (∀q∈Icc (0:ℝ) 1,GeneralDepthPaper.firstVariation Ψ μ q≤0) ∧
                {q∈Icc (0:ℝ) 1|GeneralDepthPaper.firstVariation Ψ μ q=0}=FRSB.parisiSupport (GeneralDepthPaper.atomicMeasure z hzp)) ∧
              (GeneralDepthPaper.firstVariation Ψ μ Q=0→
                (∀q∈Icc (0:ℝ) 1,GeneralDepthPaper.firstVariation Ψ μ q≤0) ∧
                {q∈Icc (0:ℝ) 1|GeneralDepthPaper.firstVariation Ψ μ q=0}=FRSB.parisiSupport (GeneralDepthPaper.atomicMeasure z hzp)∪{(Q:ℝ)}) := by
  exact GeneralDepthPaper.revised_stationary_candidate_geometry Ξ.toGeneralCovariance seed hz
    (RevisedCovariance.paperNondegenerate_toGeneralCovariance Ξ seed hz hND)
    (RevisedCovariance.isSubcritical_toGeneralCovariance Ξ hsub)

end DepthPaper.RevisedSectionFour
