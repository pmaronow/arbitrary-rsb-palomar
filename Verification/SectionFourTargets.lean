module

public import GeneralDepthPaper.RevisedSectionFourReduction
public import GeneralDepthPaper.RevisedSectionFourDeficit
public import GeneralDepthPaper.RevisedSectionFourWindows
public import GeneralDepthPaper.RevisedSectionFourStationarity
public import GeneralDepthPaper.RevisedSectionFourScalar
public import GeneralDepthPaper.RevisedSectionFourGeometry
public import GeneralDepthPaper.RevisedAppendixBSplitting
public import GeneralDepthPaper.RevisedAppendixBData

@[expose] public section

/-! Independently expanded targets for revised Sections 4.1–4.11 and
Appendix B.1–B.3. Compact-data statements are stronger than their
specialization to the constructed standing neighborhood. The seed
statements spell out actual minimization, contacts and curvature;
Hessian positivity and standing data are proved dependencies.

The prepared selectors lie in the exact printed coupling/overlap
windows. All derivatives, norms, conditional measures and expectations
below are of the concrete physical objects; no theorem target is a
proposition-valued alias. -/
noncomputable section
open Set Filter Metric MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal ENNReal
namespace Verification.SectionFourTargets
open GeneralDepthPaper FourPapersCommon ColeHopfFoundation.ProbabilityTheory

theorem lowerRecursion_exact :
  ∀Ξ:AdmissibleCovariance,∀r:ℕ,∀K:Set (AtomicPoint r),IsCompact K→
    ∀hvalid:(∀z∈K,IsAtomicPoint z),∀ε lamlo lamhi qc cQ CQ:ℝ,0<ε→0<lamlo→lamlo≤lamhi→
    qc∈Ioo (0:ℝ) 1→(∀z∈K,atomicLocation z (Fin.last r)<qc)→0<cQ→
    ∃C:ℝ,0<C ∧ ∃A:ℕ,∃c:ℝ,0<c ∧ ∃p0:ℕ,4≤p0 ∧
      ∀p:ℕ,p0≤p→∀he:Even p,∀z:AtomicPoint r,∀hz:z∈K,∀m∈Icc ε 1,∀lam∈Icc lamlo lamhi,
        ∀Q:GeneralDepthPaper.Overlap,(Q:ℝ)∈endpointStrip cQ CQ p→
          ∃hp:4≤p,∃hn:p∉Ξ.degrees,∃hlam:0<lam,
            twoLevelFunctional (Ξ.addHighDegree p hp he hn lam hlam) z
                (hvalid z hz) m Q=
              limitingAtomicObjective Ξ r lam (z,m)+
                (1-m)/2*(∫q in (Q:ℝ)..1,(1-q)*(Ξ.addHighDegree p hp he hn lam hlam).second q)+
                  lowerRecursionErrorRaw Ξ p qc (z,(m,(lam,(Q:ℝ)))) ∧
            ContDiffAt ℝ ∞ (lowerRecursionErrorRaw Ξ p qc) (z,(m,(lam,(Q:ℝ)))) ∧
            ∀n:ℕ,n≤4→∀v:Fin n→LowerInputCoordinate r,
              ‖directionalWordJet lowerInputAxis (lowerRecursionErrorRaw Ξ p qc)
                (List.ofFn v) (z,(m,(lam,(Q:ℝ))))‖≤C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  exact GeneralDepthPaper.revised_lower_recursion

theorem endpointDeficit_exact :
  ∀Ξ:AdmissibleCovariance,∀r:ℕ,∀K:Set (AtomicPoint r),IsCompact K→
    ∀hvalid:(∀z∈K,IsAtomicPoint z),∀e lo hi qc cQ CQ:ℝ,0 < e→∀hlo:0 < lo,lo ≤ hi→
      qc∈Ioo (0:ℝ) 1→(∀z∈K,atomicLocation z (Fin.last r) < qc)→0 < cQ→
      ∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧ ∃b:ℝ,0 < b ∧ ∃D:ℝ,0 < D ∧ ∃P:ℕ,4 ≤ P ∧
        ∀p:ℕ,P ≤ p→∀he:Even p,∃hp:4 ≤ p,∃hn:p∉Ξ.degrees,
          ∀z:AtomicPoint r,∀hz:z∈K,∀m∈Icc e 1,∀lam:ℝ,∀hlam:lam∈Icc lo hi,
            ∀Q:GeneralDepthPaper.Overlap,(Q:ℝ)∈endpointStrip cQ CQ p→
              let x : CutoffInputParameter r := (z,(m,(lam,(Q:ℝ))))
              let Ψ := Ξ.addHighDegree p hp he hn lam (hlo.trans_le hlam.1)
              1-Gamma Ψ (twoLevelMeasure z (hvalid z hz) m Q) Q=
                endpointDeficitFromRemainder Ξ p qc x ∧
              ContDiffAt ℝ ∞ (endpointDeficitFromRemainder Ξ p qc) x ∧
              (∀j:ℕ,j ≤ 2→‖iteratedFDeriv ℝ j (endpointDeficitFromRemainder Ξ p qc) x‖ ≤ C*(p:ℝ)^A*Real.exp (-c*(p:ℝ))) ∧
              (∀j:ℕ,j ≤ 2→∀v:Fin j→LowerInputCoordinate r,
                ‖directionalWordJet lowerInputAxis (endpointDeficitFromRemainder Ξ p qc)
                  (List.ofFn v) x‖ ≤ C*(p:ℝ)^A*Real.exp (-c*(p:ℝ))) ∧
              b*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-m^2*lam*(p:ℝ)/2) ≤ 1-Gamma Ψ (twoLevelMeasure z (hvalid z hz) m Q) Q ∧
              1-Gamma Ψ (twoLevelMeasure z (hvalid z hz) m Q) Q ≤ D*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-m^2*lam*(p:ℝ)/2) := by
  exact GeneralDepthPaper.revised_endpoint_deficit

theorem intermediateDeficit_exact (Ξ:AdmissibleCovariance) {r:ℕ}
    (z:AtomicPoint r) (hz:IsAtomicPoint z) (m:ℝ) (hm:m∈Ioc (0:ℝ) 1)
    (Q:GeneralDepthPaper.Overlap) (qc:ℝ) (hc:atomicLocation z (Fin.last r)<qc)
    (q:ℝ) (hq:q∈Icc qc (Q:ℝ)) :
    1-Gamma Ξ (twoLevelMeasure z hz m Q) q≤
      4*Real.exp (-m^2*(Ξ.first q-Ξ.first qc)/2) := by
  exact GeneralDepthPaper.revised_intermediate_deficit Ξ z hz m hm Q qc hc q hq

theorem preparedEndpointReduction_exact (Ξ:AdmissibleCovariance) {r:ℕ}
    (seed:AtomicPoint r) (hz:IsAtomicPoint seed) (hND:(IsParisiMinimizer Ξ (atomicMeasure seed hz) ∧
      (∀q∈Icc (0:ℝ) 1,firstVariation Ξ (atomicMeasure seed hz) q≤0 ∧
        (firstVariation Ξ (atomicMeasure seed hz) q=0↔∃i,q=atomicLocation seed i)) ∧
      (∀i:Fin r,closedJet 1 2 (firstVariation Ξ (atomicMeasure seed hz)) (seed.1 i)<0)))
    (hsub:Ξ.second 0<1) :
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
            (∀T:GeneralDepthPaper.Overlap,(T:ℝ)∈d.revisedEndpointStrip p→
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
  exact GeneralDepthPaper.revised_prepared_endpoint_root_and_reduction Ξ seed hz hND hsub

theorem stationaryBranches_exact (Ξ:AdmissibleCovariance) {r:ℕ}
    (seed:AtomicPoint r) (hz:IsAtomicPoint seed) (hND:(IsParisiMinimizer Ξ (atomicMeasure seed hz) ∧
      (∀q∈Icc (0:ℝ) 1,firstVariation Ξ (atomicMeasure seed hz) q≤0 ∧
        (firstVariation Ξ (atomicMeasure seed hz) q=0↔∃i,q=atomicLocation seed i)) ∧
      (∀i:Fin r,closedJet 1 2 (firstVariation Ξ (atomicMeasure seed hz)) (seed.1 i)<0)))
    (hsub:Ξ.second 0<1) :
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
          (fun u=>d.revisedScalarObjective p u-(scaledThermodynamicPressure Ξ.toEvenMixture u.2/u.2+u.1*u.2/2)) theta)
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
            (fun u=>d.revisedScalarObjective p u-(scaledThermodynamicPressure Ξ.toEvenMixture u.2/u.2+u.1*u.2/2)) theta‖≤
              C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  exact GeneralDepthPaper.revised_stationary_branches Ξ seed hz hND hsub

theorem scalarBifurcation_exact (Ξ:AdmissibleCovariance) {r:ℕ}
    (seed:AtomicPoint r) (hz:IsAtomicPoint seed) (hND:(IsParisiMinimizer Ξ (atomicMeasure seed hz) ∧
      (∀q∈Icc (0:ℝ) 1,firstVariation Ξ (atomicMeasure seed hz) q≤0 ∧
        (firstVariation Ξ (atomicMeasure seed hz) q=0↔∃i,q=atomicLocation seed i)) ∧
      (∀i:Fin r,closedJet 1 2 (firstVariation Ξ (atomicMeasure seed hz)) (seed.1 i)<0)))
    (hsub:Ξ.second 0<1) :
    ∃d:LimitingStandingData Ξ seed,
      Tendsto (fun p=>d.couplingCurve p 1) (atTop⊓𝓟 {p:ℕ|Even p})
        (𝓝 (pressureEll (scaledThermodynamicPressure Ξ.toEvenMixture) 1)) ∧
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
  exact GeneralDepthPaper.revised_scalar_bifurcation Ξ seed hz hND hsub

theorem candidateGeometry_exact (Ξ:AdmissibleCovariance) {r:ℕ}
    (seed:AtomicPoint r) (hz:IsAtomicPoint seed) (hND:(IsParisiMinimizer Ξ (atomicMeasure seed hz) ∧
      (∀q∈Icc (0:ℝ) 1,firstVariation Ξ (atomicMeasure seed hz) q≤0 ∧
        (firstVariation Ξ (atomicMeasure seed hz) q=0↔∃i,q=atomicLocation seed i)) ∧
      (∀i:Fin r,closedJet 1 2 (firstVariation Ξ (atomicMeasure seed hz)) (seed.1 i)<0)))
    (hsub:Ξ.second 0<1) :
    ∃d:LimitingStandingData Ξ seed,∃gamma:ℝ,0<gamma ∧
      (∀m:d.MassInterval,d.limitingVariation m 1≤ -5*gamma) ∧
      (∀m:d.MassInterval,∀q∈Icc d.cutoff 1,d.limitingVariation m q≤ -4*gamma) ∧
      (1/2:ℝ)*(∫q in d.cutoff..1,(1-q)*Ξ.second q)≤gamma ∧
      ∃L:ℝ,0<L ∧ L=10/d.massLower^2 ∧ 10≤d.massLower^2*L ∧
        ∀ᶠp:ℕ in atTop,4≤p ∧ ∀he:Even p,∃hp:4≤p,∃hn:p∉Ξ.degrees,
          ∀theta:ℝ×ℝ,∀ht:theta∈d.revisedParameterWindow,
            ∃hzp:IsAtomicPoint (d.stationaryBranch p theta),
              let z:=d.stationaryBranch p theta
              let Ψ:=Ξ.addHighDegree p hp he hn theta.1 (d.couplingLower_pos.trans_le ht.1.1)
              let Q:=distinguishedOverlap Ξ p d.cutoff d.stripRateLower d.stripRateUpper (z,(theta.2,theta.1))
              let μ:=twoLevelMeasure z hzp theta.2 Q
              let a:=logarithmicOverlapThreshold p theta.1 L
              ((μ:Measure GeneralDepthPaper.Overlap)=ENNReal.ofReal theta.2 • (atomicMeasure z hzp:Measure GeneralDepthPaper.Overlap)+
                ENNReal.ofReal (1-theta.2) • Measure.dirac Q) ∧
              (theta.2=1→μ=atomicMeasure z hzp) ∧
              (∀q∈(atomicMeasure z hzp:Measure GeneralDepthPaper.Overlap).support,firstVariation Ψ μ q=0) ∧
              (∀q∈(atomicMeasure z hzp:Measure GeneralDepthPaper.Overlap).support,q≠⟨0,by norm_num⟩→
                deriv (firstVariation Ψ μ) q=0) ∧
              deriv (firstVariation Ψ μ) Q=0 ∧
              d.stationaryMassFunction p theta=firstVariation Ψ μ Q ∧
              (∀q∈Icc (0:ℝ) d.cutoff,firstVariation Ψ μ q≤0 ∧
                (firstVariation Ψ μ q=0↔q∈FRSB.parisiSupport (atomicMeasure z hzp))) ∧
              (∀i:Fin r,deriv (deriv (firstVariation Ψ μ)) (z.1 i)<0) ∧
              firstVariation Ψ μ d.cutoff≤ -3*gamma ∧
              d.cutoff<a ∧ a<(Q:ℝ) ∧ (Q:ℝ)<1 ∧
              theta.1*(p:ℝ)*a^(p-1)=(10/d.massLower^2)*Real.log (p:ℝ) ∧
              (∀t∈Ioo (0:ℝ) 1,theta.1*(p:ℝ)*t^(p-1)=(10/d.massLower^2)*Real.log (p:ℝ)→t=a) ∧
              (∀q∈Icc d.cutoff a,firstVariation Ψ μ q≤ -gamma) ∧
              (∀q∈Icc a 1,derivWithin (Gamma Ψ μ) (Icc (0:ℝ) 1) q≤1/2) ∧
              StrictMonoOn (firstVariation Ψ μ) (Icc a (Q:ℝ)) ∧
              StrictAntiOn (firstVariation Ψ μ) (Icc (Q:ℝ) 1) ∧
              deriv (deriv (firstVariation Ψ μ)) Q<0 ∧
              (firstVariation Ψ μ Q<0→
                (∀q∈Icc (0:ℝ) 1,firstVariation Ψ μ q≤0) ∧
                {q∈Icc (0:ℝ) 1|firstVariation Ψ μ q=0}=FRSB.parisiSupport (atomicMeasure z hzp)) ∧
              (firstVariation Ψ μ Q=0→
                (∀q∈Icc (0:ℝ) 1,firstVariation Ψ μ q≤0) ∧
                {q∈Icc (0:ℝ) 1|firstVariation Ψ μ q=0}=FRSB.parisiSupport (atomicMeasure z hzp)∪{(Q:ℝ)}) := by
  exact GeneralDepthPaper.revised_stationary_candidate_geometry Ξ seed hz hND hsub

theorem cutoffSplitting_exact (Ξ:AdmissibleCovariance)
    {ε lamlo lamhi qc cQ CQ:ℝ} (hε:0<ε) (hlo:0<lamlo)
    (hLH:lamlo≤lamhi) (hc:qc∈Ioo (0:ℝ) 1) (hcQ:0<cQ) :
    ∃C:ℝ,0<C ∧ ∃A:ℕ,∃c:ℝ,0<c ∧ ∃P:ℕ,
      ∀p:ℕ,P≤p→∀he:Even p,∃hp:4≤p,∃hn:p∉Ξ.degrees,
        ∀m:ℝ,∀hm:m∈Icc ε 1,∀lam:ℝ,∀hlam:lam∈Icc lamlo lamhi,
          ∀hlampos:0<lam,∀Q:GeneralDepthPaper.Overlap,(Q:ℝ)∈endpointStrip cQ CQ p→
            ∃hqcQ:qc<(Q:ℝ),
              let Ψ:=Ξ.addHighDegree p hp he hn lam hlampos
              let W:=Ψ.first Q-Ψ.first qc
              (∀x:ℝ,terminalValue (cutoffEndpointTerminal Ξ p qc (m,(lam,Q))) x=
                coleHopf m W.toNNReal (fun y=>Real.log (Real.cosh y)) x-
                  m*W/2-(1/m-1)*Real.log 2) ∧
              LipschitzWith 1 (terminalValue (cutoffEndpointTerminal Ξ p qc (m,(lam,Q)))) ∧
              ContDiffAt ℝ ∞ (cutoffEndpointTerminal Ξ p qc) (m,(lam,Q)) ∧
              ContDiffAt ℝ ∞ scaledLogCoshTerminal m ∧
              (∀n≤4,∀v:Fin n→Fin 3,
                terminalSumNorm (directionalWordJet cutoffAxis (cutoffEndpointError Ξ p qc)
                  (List.ofFn v) (m,(lam,Q)))≤C*(p:ℝ)^A*Real.exp (-c*(p:ℝ))) ∧
              ∀r:ℕ,∀z:AtomicPoint r,∀hz:IsAtomicPoint z,
                atomicLocation z (Fin.last r)<qc→∀x:ℝ,
                  potential Ψ (twoLevelMeasure z hz m Q) qc x=
                    (Ψ.first 1-Ψ.first Q)/2+m*W/2+(1/m-1)*Real.log 2+
                      terminalValue (cutoffEndpointTerminal Ξ p qc (m,(lam,Q))) x := by
  exact GeneralDepthPaper.revised_cutoff_splitting Ξ hε hlo hLH hc hcQ

theorem belowCutoff_exact (Ψ Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m ∈ Ioc (0 : ℝ) 1)
    (Q : GeneralDepthPaper.Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r) < qc)
    (hqcQ : qc < (Q : ℝ)) :
    (∀ q ∈ Icc (0 : ℝ) qc, ∀ x,
      potential Ψ (twoLevelMeasure z hz m Q) q x =
        cutoffCandidateConstant Ψ m Q qc +
          (cutoffCandidateData Ψ z hz m ⟨hm.1.le, hm.2⟩ Q qc hc hqcQ.le).potential q x) ∧
    (Paper.canonicalBrownianMeasure.map
      (cutoffTruncatedStatePath Ψ z hz m ⟨hm.1.le, hm.2⟩ Q qc hc hqcQ.le) =
      Paper.canonicalBrownianMeasure.map (cutoffOptimalStatePath Ψ z hz m Q qc)) ∧
    (∀ sample, cutoffOptimalStatePath Ψ z hz m Q qc sample =
      additiveStatePath (cutoffCandidateData Ψ z hz m ⟨hm.1.le, hm.2⟩ Q qc hc hqcQ.le).driftData
        0 qc (cutoff_pos z hz qc hc).le
        (rescaledClockBrownianPath (mixedBeta Ψ.toEvenMixture)
          (cutoffCovarianceClock Ψ qc) sample)) ∧
    (∀ q ∈ Icc (0 : ℝ) qc,
      firstVariation Ψ (twoLevelMeasure z hz m Q) q =
        (cutoffCandidateData Ψ z hz m ⟨hm.1.le, hm.2⟩ Q qc hc hqcQ.le).firstVariation q) ∧
    ((cutoffComparisonData Ψ z hz m ⟨hm.1.le, hm.2⟩ qc hc).potential 0 0 =
      m⁻¹ * potential ((temperatureCovarianceFamily Ψ).covariance m) (atomicMeasure z hz) 0 0 -
        m / 2 * (Ψ.first 1 - Ψ.first qc)) ∧
    (∀ q ∈ Icc (0 : ℝ) qc,
      (cutoffComparisonData Ξ z hz m ⟨hm.1.le, hm.2⟩ qc hc).firstVariation q =
        (m^2)⁻¹ * firstVariation ((temperatureCovarianceFamily Ξ).covariance m)
          (atomicMeasure z hz) q) := by
  exact GeneralDepthPaper.revised_below_cutoff Ψ Ξ z hz m hm Q qc hc hqcQ

theorem conditionalKernel_exact (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m ∈ Icc (0 : ℝ) 1)
    (Q : GeneralDepthPaper.Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r) < qc)
    (q : ℝ) (hq : q ∈ Ioc qc (Q : ℝ))
    (E : Set GeneralDepthPaper.BrownianSample)
    (hE : MeasurableSet[Paper.canonicalBrownianFiltration (Ξ.clock qc).toNNReal] E) :
    (Paper.canonicalBrownianMeasure.restrict E).map
        (fun sample => optimalState Ξ (twoLevelMeasure z hz m Q) sample q) =
      revisedCutoffKernel m (Ξ.first Q - Ξ.first qc).toNNReal
        (Ξ.first q - Ξ.first qc).toNNReal ∘ₘ
          (Paper.canonicalBrownianMeasure.restrict E).map
            (fun sample => optimalState Ξ (twoLevelMeasure z hz m Q) sample qc) := by
  exact GeneralDepthPaper.revised_cutoff_conditional_law Ξ z hz m hm Q qc hc q hq E hE

theorem conditionalKernelDensity_exact (m:ℝ) (W t:ℝ≥0) (ht:0<t) (htW:t≤W) (x:ℝ) :
    revisedCutoffKernel m W t x=volume.withDensity (fun y=>ENNReal.ofReal
      (gaussianPDFReal x t y*Real.exp (m*terminalDoobPotential m W t y)/
        Real.exp (m*terminalDoobPotential m W 0 x))) := by
  exact GeneralDepthPaper.revisedCutoffKernel_density m W t ht htW x

theorem deficitExpectation_exact (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m ∈ Icc (0 : ℝ) 1)
    (Q : GeneralDepthPaper.Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r) < qc)
    (q : ℝ) (hq : q ∈ Icc qc (Q : ℝ)) :
    1 - Gamma Ξ (twoLevelMeasure z hz m Q) q =
      ∫ sample, 1 - (deriv (terminalDoobPotential m (Ξ.first Q - Ξ.first qc).toNNReal
        (Ξ.first q - Ξ.first qc).toNNReal)
          (optimalState Ξ (twoLevelMeasure z hz m Q) sample q))^2
            ∂Paper.canonicalBrownianMeasure := by
  exact GeneralDepthPaper.revised_cutoff_deficit_expectation Ξ z hz m hm Q qc hc q hq

theorem endpointExpectation_exact (Ξ : AdmissibleCovariance) {r : ℕ}
    (z : AtomicPoint r) (hz : IsAtomicPoint z) (m : ℝ) (hm : m ∈ Icc (0 : ℝ) 1)
    (Q : GeneralDepthPaper.Overlap) (qc : ℝ) (hc : atomicLocation z (Fin.last r) < qc)
    (hqcQ : qc ≤ (Q : ℝ)) :
    1 - Gamma Ξ (twoLevelMeasure z hz m Q) Q =
      ∫ sample, Paper.sech (optimalState Ξ (twoLevelMeasure z hz m Q) sample Q)^2
        ∂Paper.canonicalBrownianMeasure := by
  exact GeneralDepthPaper.revised_cutoff_endpoint_expectation Ξ z hz m hm Q qc hc hqcQ

end Verification.SectionFourTargets
