module

public import GeneralDepthPaper.CutoffSplittingLemma
public import GeneralDepthPaper.RevisedAppendixBData

@[expose] public section

/-! Revised Appendix B.1. The terminal datum is an actual element of the
complete compatible three-jet terminal space. Its norm below is precisely
the sum |ψ(0)| + Σ_{j=1}³ sup |∂ₓʲψ| used in the paper. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal
namespace GeneralDepthPaper
open ColeHopfFoundation.ProbabilityTheory
set_option maxHeartbeats 1000000

theorem revised_cutoff_terminal_lipschitz (m V:ℝ) (hV:0≤V) :
    LipschitzWith 1 (terminalValue (cutoffTerminal m V)) := by
  apply (lipschitzWith_terminalValue (cutoffTerminal m V)).weaken
  exact_mod_cast norm_terminalJet_cutoffTerminal_le_one m V hV

/-- Every quantifier of revised B.1; valid on any compact mass/coupling
window and exponentially thin endpoint strip, without seed assumptions. -/
theorem revised_cutoff_splitting (Ξ:AdmissibleCovariance)
    {ε lamlo lamhi qc cQ CQ:ℝ} (hε:0<ε) (hlo:0<lamlo)
    (hLH:lamlo≤lamhi) (hc:qc∈Ioo (0:ℝ) 1) (hcQ:0<cQ) :
    ∃C:ℝ,0<C ∧ ∃A:ℕ,∃c:ℝ,0<c ∧ ∃P:ℕ,
      ∀p:ℕ,P≤p→∀he:Even p,∃hp:4≤p,∃hn:p∉Ξ.degrees,
        ∀m:ℝ,∀hm:m∈Icc ε 1,∀lam:ℝ,∀hlam:lam∈Icc lamlo lamhi,
          ∀hlampos:0<lam,∀Q:Overlap,(Q:ℝ)∈endpointStrip cQ CQ p→
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
  obtain ⟨C,hC,A,c,hcpos,P,H⟩:=cutoff_splitting Ξ hε hlo hLH hc hcQ
  refine ⟨C,hC,A,c,hcpos,P,?_⟩
  intro p hpP he
  obtain ⟨hp,hn,Hdata⟩:=H p hpP he
  refine ⟨hp,hn,?_⟩
  intro m hm lam hlam hlampos Q hQ
  obtain ⟨hqcQ,hterminal,hsm,hscaled,hjets,_⟩:=Hdata m hm lam hlam hlampos Q hQ
  refine ⟨hqcQ,?_,?_,hsm,hscaled,hjets,?_⟩
  · intro x
    rw [hterminal,terminalValue_cutoffTerminal m _ (sub_nonneg.mpr
      ((Ξ.addHighDegree p hp he hn lam hlampos).first_strictMonoOn.monotoneOn
        hc.1.le Q.property.1 hqcQ.le)) x]
    simp only [cutoffLeadingConstant]
    ring
  · rw [hterminal]
    exact revised_cutoff_terminal_lipschitz m _ (sub_nonneg.mpr
      ((Ξ.addHighDegree p hp he hn lam hlampos).first_strictMonoOn.monotoneOn
        hc.1.le Q.property.1 hqcQ.le))
  · intro r z hz hzqc x
    rw [potential_twoLevelMeasure_at_cutoff _ z hz m ⟨hε.le.trans hm.1,hm.2⟩
      Q qc hzqc hqcQ.le x,hterminal]
    simp only [cutoffCandidateConstant,cutoffLeadingConstant]
    ring

end GeneralDepthPaper
