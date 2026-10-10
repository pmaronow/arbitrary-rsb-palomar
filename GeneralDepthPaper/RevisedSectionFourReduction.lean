module

public import GeneralDepthPaper.LowerRecursionLemma
public import GeneralDepthPaper.EndpointDeficitLemma
public import GeneralDepthPaper.EndpointRootProposition
public import GeneralDepthPaper.RevisedSectionFourDeficit

@[expose] public section

/-! Independently expanded exact targets for revised Sections 4.1–4.4.
Every compact finite-atomic lower-coordinate set is allowed, so the
constructed paper neighborhood is an immediate specialization. The
C^ell bounds below include all ordered coordinate derivatives and
operator norms; all expressions are the actual Parisi objects. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
namespace GeneralDepthPaper

theorem revised_lower_recursion :
  ∀Ξ:AdmissibleCovariance,∀r:ℕ,∀K:Set (AtomicPoint r),IsCompact K→
    ∀hvalid:(∀z∈K,IsAtomicPoint z),∀ε lamlo lamhi qc cQ CQ:ℝ,0<ε→0<lamlo→lamlo≤lamhi→
    qc∈Ioo (0:ℝ) 1→(∀z∈K,atomicLocation z (Fin.last r)<qc)→0<cQ→
    ∃C:ℝ,0<C ∧ ∃A:ℕ,∃c:ℝ,0<c ∧ ∃p0:ℕ,4≤p0 ∧
      ∀p:ℕ,p0≤p→∀he:Even p,∀z:AtomicPoint r,∀hz:z∈K,∀m∈Icc ε 1,∀lam∈Icc lamlo lamhi,
        ∀Q:Overlap,(Q:ℝ)∈endpointStrip cQ CQ p→
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
  exact lower_recursion

theorem revised_endpoint_deficit :
  ∀Ξ:AdmissibleCovariance,∀r:ℕ,∀K:Set (AtomicPoint r),IsCompact K→
    ∀hvalid:(∀z∈K,IsAtomicPoint z),∀e lo hi qc cQ CQ:ℝ,0 < e→∀hlo:0 < lo,lo ≤ hi→
      qc∈Ioo (0:ℝ) 1→(∀z∈K,atomicLocation z (Fin.last r) < qc)→0 < cQ→
      ∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧ ∃b:ℝ,0 < b ∧ ∃D:ℝ,0 < D ∧ ∃P:ℕ,4 ≤ P ∧
        ∀p:ℕ,P ≤ p→∀he:Even p,∃hp:4 ≤ p,∃hn:p∉Ξ.degrees,
          ∀z:AtomicPoint r,∀hz:z∈K,∀m∈Icc e 1,∀lam:ℝ,∀hlam:lam∈Icc lo hi,
            ∀Q:Overlap,(Q:ℝ)∈endpointStrip cQ CQ p→
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
  exact endpoint_deficit

theorem revised_endpoint_root_and_reduction :
  ∀Ξ:AdmissibleCovariance,∀r:ℕ,∀K:Set (AtomicPoint r),IsCompact K→
    ∀hvalid:(∀z∈K,IsAtomicPoint z),∀e lo hi qc cQ CQ:ℝ,
      e∈Ioo (0:ℝ) 1→∀hlo:0 < lo,lo ≤ hi→qc∈Ioo (0:ℝ) 1→
      (∀z∈K,atomicLocation z (Fin.last r) < qc)→0 < cQ→
      cQ < e^2*lo/2→hi/2 < CQ→
      ∃b:ℝ,0 < b ∧ ∃D:ℝ,0 < D ∧
      ∃Cq:ℝ,0 < Cq ∧ ∃Aq:ℕ,∃cq:ℝ,0 < cq ∧
      ∃Cf:ℝ,0 < Cf ∧ ∃Af:ℕ,∃cf:ℝ,0 < cf ∧ ∃P:ℕ,4 ≤ P ∧
        ∀p:ℕ,P ≤ p→∀heven:Even p,∃hp:4 ≤ p,∃hn:p∉Ξ.degrees,
          ∀theta:HighDegreeLowerParameter r,∀hz:theta.1∈K,
            theta.2.1∈Icc e 1→∀hlam:theta.2.2∈Icc lo hi,
            let Ψ := Ξ.addHighDegree p hp heven hn theta.2.2 (hlo.trans_le hlam.1)
            let Q := distinguishedOverlap Ξ p qc cQ CQ theta
            (Q:ℝ)=distinguishedEndpoint Ξ p qc cQ CQ theta ∧
            (Q:ℝ)∈Ioo (1-Real.exp (-cQ*(p:ℝ))) (1-Real.exp (-CQ*(p:ℝ))) ∧
            Gamma Ψ (twoLevelMeasure theta.1 (hvalid _ hz) theta.2.1 Q) Q=(Q:ℝ) ∧
            (∀T:Overlap,(T:ℝ)∈endpointStrip cQ CQ p→
              Gamma Ψ (twoLevelMeasure theta.1 (hvalid _ hz) theta.2.1 T) T=(T:ℝ)→T=Q) ∧
            b*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-theta.2.1^2*theta.2.2*(p:ℝ)/2) ≤ 1-(Q:ℝ) ∧
            1-(Q:ℝ) ≤ D*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-theta.2.1^2*theta.2.2*(p:ℝ)/2) ∧
            ContDiffAt ℝ ∞ (distinguishedEndpoint Ξ p qc cQ CQ) theta ∧
            (∀j:ℕ,1 ≤ j→j ≤ 2→‖iteratedFDeriv ℝ j
              (distinguishedEndpoint Ξ p qc cQ CQ) theta‖ ≤ Cq*(p:ℝ)^Aq*Real.exp (-cq*(p:ℝ))) ∧
            ContDiffAt ℝ ∞ (reducedEndpointFunctional Ξ p qc cQ CQ) theta ∧
            reducedEndpointFunctional Ξ p qc cQ CQ theta=twoLevelFunctional Ψ theta.1
              (hvalid _ hz) theta.2.1 Q ∧
            fderiv ℝ (reducedEndpointFunctional Ξ p qc cQ CQ) theta=
              (fderiv ℝ (endpointFunctionalChart Ξ p qc)
                (theta,distinguishedEndpoint Ξ p qc cQ CQ theta)).comp
                  (ContinuousLinearMap.inl ℝ (HighDegreeLowerParameter r) ℝ) ∧
            (theta.2.1 < 1→0 < deriv (deriv (fun q=>twoLevelFunctional Ψ theta.1 (hvalid _ hz)
              theta.2.1 (projIcc 0 1 zero_le_one q))) Q) ∧
            (∀j:ℕ,j ≤ 3→‖iteratedFDeriv ℝ j
              (fun u=>reducedEndpointFunctional Ξ p qc cQ CQ u-limitingObjectiveCore Ξ u)
                theta‖ ≤ Cf*(p:ℝ)^Af*Real.exp (-cf*(p:ℝ))) := by
  exact endpoint_root

end GeneralDepthPaper
