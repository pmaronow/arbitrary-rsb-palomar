module

public import GeneralDepthPaper.CutoffEndpointErrorBound
public import GeneralDepthPaper.DirectionalWordJets

@[expose] public section


/-! Literal Banach-space C⁴ and coordinate-partial approximation in
cutoff Lemma 4.1(a), with the paper's sum norm on the terminal space. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace GeneralDepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

def cutoffEndpointTerminal (Ξ:AdmissibleCovariance) (p:ℕ) (qc:ℝ)
    (x:ℝ×(ℝ×ℝ)) : TerminalSpace :=
  cutoffTerminal x.1 (endpointVarianceExpression Ξ p qc x.2)

theorem cutoff_terminal_approximation (Ξ:AdmissibleCovariance)
    {ε lamlo lamhi qc cQ CQ:ℝ} (hε:0 < ε) (hlo:0 < lamlo)
    (hLH:lamlo≤lamhi) (hc:qc∈Ioo (0:ℝ) 1) (hcQ:0 < cQ) :
    ∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧ ∃p0:ℕ,1≤p0 ∧
      ∀p:ℕ,p0≤p→∀m∈Icc ε 1,∀lam∈Icc lamlo lamhi,
        ∀Q∈endpointStrip cQ CQ p,
          1 < endpointVarianceExpression Ξ p qc (lam,Q) ∧
          ContDiffAt ℝ ∞ (cutoffEndpointTerminal Ξ p qc) (m,(lam,Q)) ∧
          ContDiffAt ℝ ∞ scaledLogCoshTerminal m ∧
          ∀n≤4,∀v:Fin n→Fin 3,
            terminalSumNorm (directionalWordJet cutoffAxis (cutoffEndpointError Ξ p qc)
              (List.ofFn v) (m,(lam,Q)))≤C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  obtain ⟨C,hC,A,c,hcpos,P,hP,hbound⟩:=
    cutoff_endpoint_error_exponential_bound Ξ (CQ:=CQ) hε hlo hLH hc hcQ 4
  refine ⟨4*C,by positivity,A,c,hcpos,P,hP,?_⟩
  intro p hp m hm lam hlam Q hQ
  obtain ⟨hW,herror,hjets⟩:=hbound p hp m hm lam hlam Q hQ
  have hm2:m∈Ioo (0:ℝ) 2:=⟨hε.trans_le hm.1,hm.2.trans_lt (by norm_num)⟩
  have houter:ContDiffAt ℝ ∞ (fun y:ℝ×ℝ=>cutoffTerminal y.1 y.2)
      (cutoffParameterMap Ξ p qc (m,(lam,Q))) :=
    contDiffAt_cutoffTerminal hm2.1.ne' (zero_lt_one.trans hW)
  have hterminal:ContDiffAt ℝ ∞ (cutoffEndpointTerminal Ξ p qc) (m,(lam,Q)) :=
    houter.comp (m,(lam,Q)) (contDiff_cutoffParameterMap Ξ p qc).contDiffAt
  refine ⟨hW,hterminal,contDiffAt_scaledLogCoshTerminal hm2,?_⟩
  intro n hn v
  let H:=cutoffParameterMap Ξ p qc
  let U:=H ⁻¹' cutoffErrorDomain
  have hH:ContDiff ℝ ∞ H:=contDiff_cutoffParameterMap Ξ p qc
  have hU:IsOpen U:=isOpen_cutoffErrorDomain.preimage hH.continuous
  have hx:(m,(lam,Q))∈U:=⟨hm2,zero_lt_one.trans hW⟩
  have he:ContDiffOn ℝ ∞ (cutoffEndpointError Ξ p qc) U :=
    contDiffOn_cutoffErrorTerminal.comp hH.contDiffOn (fun _ hy=>hy)
  rw [←iteratedFDeriv_dirs_eq_directionalWordJet cutoffAxis hU he n v hx]
  have hop:‖iteratedFDeriv ℝ n (cutoffEndpointError Ξ p qc) (m,(lam,Q))
      (fun i=>cutoffAxis (v i))‖≤
      ‖iteratedFDeriv ℝ n (cutoffEndpointError Ξ p qc) (m,(lam,Q))‖ := by
    simpa only [norm_cutoffAxis,Finset.prod_const_one,mul_one] using
      (iteratedFDeriv ℝ n (cutoffEndpointError Ξ p qc) (m,(lam,Q))).le_opNorm
        (fun i=>cutoffAxis (v i))
  exact (terminalSumNorm_le_four_norm _).trans
    ((mul_le_mul_of_nonneg_left (hop.trans (hjets n hn)) (by norm_num)).trans_eq (by ring))

end GeneralDepthPaper
