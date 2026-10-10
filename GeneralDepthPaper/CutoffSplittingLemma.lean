module

public import GeneralDepthPaper.CutoffSplitting

@[expose] public section


/-! Closed full cutoff-splitting Lemma 4.1 on the paper's parameter
windows. Every sufficiently large even degree is automatically outside
the finite base degree set. All analytical and stochastic inputs are
discharged by the actual selected mixed solution and constructed kernels. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

def CutoffSplittingTarget (Ξ:AdmissibleCovariance)
    (ε lamlo lamhi qc cQ CQ:ℝ) : Prop :=
  ∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧ ∃P:ℕ,
    ∀p:ℕ,P≤p→∀he:Even p,∃hp:4≤p,∃hn:p∉Ξ.degrees,
      ∀m:ℝ,∀hm:m∈Icc ε 1,∀lam:ℝ,∀hlam:lam∈Icc lamlo lamhi,
        ∀hlampos:0 < lam,∀Q:Overlap,Q.val∈endpointStrip cQ CQ p→
          ∃hqcQ:qc < (Q:ℝ),
            cutoffEndpointTerminal Ξ p qc (m,(lam,Q))=
              cutoffTerminal m ((Ξ.addHighDegree p hp he hn lam hlampos).first Q-
                (Ξ.addHighDegree p hp he hn lam hlampos).first qc) ∧
            ContDiffAt ℝ ∞ (cutoffEndpointTerminal Ξ p qc) (m,(lam,Q)) ∧
            ContDiffAt ℝ ∞ scaledLogCoshTerminal m ∧
            (∀n≤4,∀v:Fin n→Fin 3,
              terminalSumNorm (directionalWordJet cutoffAxis (cutoffEndpointError Ξ p qc)
                (List.ofFn v) (m,(lam,Q)))≤C*(p:ℝ)^A*Real.exp (-c*(p:ℝ))) ∧
            ∀r:ℕ,∀z:AtomicPoint r,∀hz:IsAtomicPoint z,
              ∀hzqc:atomicLocation z (Fin.last r) < qc,
                ∀hmpos:0 < m,
                  CutoffSplittingAt (Ξ.addHighDegree p hp he hn lam hlampos) Ξ
                    z hz m ⟨hmpos,hm.2⟩ Q qc hzqc hqcQ

theorem cutoff_splitting (Ξ:AdmissibleCovariance)
    {ε lamlo lamhi qc cQ CQ:ℝ} (hε:0 < ε) (hlo:0 < lamlo)
    (hLH:lamlo≤lamhi) (hc:qc∈Ioo (0:ℝ) 1) (hcQ:0 < cQ) :
    CutoffSplittingTarget Ξ ε lamlo lamhi qc cQ CQ := by
  obtain ⟨C,hC,A,c,hcpos,P,hP,hbound⟩:=
    cutoff_terminal_approximation Ξ (CQ:=CQ) hε hlo hLH hc hcQ
  refine ⟨C,hC,A,c,hcpos,max P (max 4 (Ξ.degrees.sup id+1)),?_⟩
  intro p hpP he
  have hpold:P≤p:=(le_max_left _ _).trans hpP
  have hp4:4≤p:=(le_max_left _ _).trans ((le_max_right _ _).trans hpP)
  have hnot:p∉Ξ.degrees := by
    intro hmem
    have hh:p≤Ξ.degrees.sup id:=Finset.le_sup (f:=id) hmem
    have hbig:Ξ.degrees.sup id+1≤p:=
      (le_max_right _ _).trans ((le_max_right _ _).trans hpP)
    omega
  refine ⟨hp4,hnot,?_⟩
  intro m hm lam hlam hlampos Q hQ
  obtain ⟨hW,hterminal,hpsi,hjets⟩:=hbound p hpold m hm lam hlam Q hQ
  let X:=Ξ.addHighDegree p hp4 he hnot lam hlampos
  have hactualW:1 < X.first Q-X.first qc := by
    have heq:=endpointVariance_eq_expression Ξ p hp4 he hnot lam hlampos qc Q
    change X.first Q-X.first qc=endpointVarianceExpression Ξ p qc (lam,Q) at heq
    exact heq.symm ▸ hW
  have hqcQ:qc < (Q:ℝ) := by
    by_contra h
    have hQqc:(Q:ℝ)≤qc:=le_of_not_gt h
    have hx:X.first Q≤X.first qc:=X.first_strictMonoOn.monotoneOn
      Q.property.1 hc.1.le hQqc
    linarith
  refine ⟨hqcQ,?_,hterminal,hpsi,hjets,?_⟩
  · change cutoffTerminal m (endpointVarianceExpression Ξ p qc (lam,Q))=
      cutoffTerminal m (X.first Q-X.first qc)
    rw [←endpointVariance_eq_expression Ξ p hp4 he hnot lam hlampos qc Q]
    rfl
  · intro r z hz hzqc hmpos
    exact cutoff_splitting_at X Ξ z hz m ⟨hmpos,hm.2⟩ Q qc hzqc hqcQ

end GeneralDepthPaper
