module

public import DepthPaper.CutoffCovarianceJetBound
public import DepthPaper.CutoffEndpointErrorBound
public import DepthPaper.CutoffRecursionRegularity
public import DepthPaper.CutoffSelectedMoments
public import DepthPaper.CutoffComparisonState
public import DepthPaper.TruncatedVariationConvergence

@[expose] public section


/-! Appendix A.2 applied to the actual cutoff data of the high-degree
candidate. Covariance, moving atomic nodes and levels, and compatible
terminal jets all converge to the genuine ψ-comparison recursion. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 64

theorem tendsto_cutoffEndpointTerminal_of_degree (Ξ : AdmissibleCovariance)
    {ε lo hi qc cQ CQ m0 : ℝ} (hε : 0<ε) (hlo : 0<lo) (hLH : lo≤hi)
    (hc : qc∈Ioo (0:ℝ) 1) (hcQ : 0<cQ) (hm0 : m0∈Icc ε 1)
    (p : ℕ→ℕ) (hp : Tendsto p atTop atTop)
    (m lam Q : ℕ→ℝ) (hm : ∀n,m n∈Icc ε 1)
    (hl : ∀n,lam n∈Icc lo hi) (hQ : ∀n,Q n∈endpointStrip cQ CQ (p n))
    (hmt : Tendsto m atTop (𝓝 m0)) :
    Tendsto (fun n=>cutoffTerminal (m n)
      (endpointVarianceExpression Ξ (p n) qc (lam n,Q n))) atTop
      (𝓝 (scaledLogCoshTerminal m0)) := by
  obtain ⟨C,hC,A,c,hc',P,hP,H⟩:=cutoff_endpoint_error_exponential_bound Ξ
    hε hlo hLH hc hcQ 0
  have hb : ∀ᶠn in atTop,‖cutoffEndpointError Ξ (p n) qc (m n,(lam n,Q n))‖≤
      C*(p n:ℝ)^A*Real.exp (-c*(p n:ℝ)) := by
    filter_upwards [hp.eventually (eventually_ge_atTop P)] with n hn
    have HH:=(H (p n) hn (m n) (hm n) (lam n) (hl n) (Q n) (hQ n)).2.2 0 le_rfl
    simpa only [iteratedFDeriv_zero_apply,norm_iteratedFDeriv_zero] using HH
  have hz : Tendsto (fun n=>cutoffEndpointError Ξ (p n) qc (m n,(lam n,Q n)))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero' (.of_forall fun n=>norm_nonneg _) hb
      ((tendsto_nat_polynomial_exp C c A hc').comp hp)
  have hm0' : m0∈Ioo (0:ℝ) 2:=⟨hε.trans_le hm0.1,hm0.2.trans_lt (by norm_num)⟩
  have hpsi := (contDiffAt_scaledLogCoshTerminal hm0').continuousAt.tendsto.comp hmt
  have Hsum:=hz.add hpsi
  simpa only [cutoffEndpointError,cutoffErrorTerminal,Function.comp_def,
    sub_add_cancel,zero_add] using Hsum

theorem cutoffCandidateData_highDegree_convergence (Ξ : AdmissibleCovariance)
    {r : ℕ} {ε lo hi qc cQ CQ m0 : ℝ}
    (hε : 0<ε) (hlo : 0<lo) (hLH : lo≤hi) (hc : qc∈Ioo (0:ℝ) 1) (hcQ : 0<cQ)
    (p : ℕ→ℕ) (hp : ∀n,4≤p n) (he : ∀n,Even (p n))
    (hn : ∀n,p n∉Ξ.degrees) (hpt : Tendsto p atTop atTop)
    (m lam : ℕ→ℝ) (hm : ∀n,m n∈Icc ε 1) (hl : ∀n,lam n∈Icc lo hi)
    (Q : ℕ→Overlap) (hQ : ∀n,(Q n:ℝ)∈endpointStrip cQ CQ (p n))
    (hqcQ : ∀n,qc≤(Q n:ℝ))
    (z : ℕ→AtomicPoint r) (hz : ∀n,IsAtomicPoint (z n))
    (hzc : ∀n,atomicLocation (z n) (Fin.last r)<qc)
    (z0 : AtomicPoint r) (hz0 : IsAtomicPoint z0)
    (hz0c : atomicLocation z0 (Fin.last r)<qc) (hm0 : m0∈Icc ε 1)
    (hzt : Tendsto z atTop (𝓝 z0)) (hmt : Tendsto m atTop (𝓝 m0)) :
    TruncatedDataConvergence
      (fun n=>cutoffCandidateData
        (Ξ.addHighDegree (p n) (hp n) (he n) (hn n) (lam n) (hlo.trans_le (hl n).1))
        (z n) (hz n) (m n) ⟨hε.le.trans (hm n).1,(hm n).2⟩ (Q n) qc (hzc n) (hqcQ n))
      (cutoffComparisonData Ξ z0 hz0 m0 ⟨hε.le.trans hm0.1,hm0.2⟩ qc hz0c) := by
  constructor
  · intro j
    exact tendsto_cutoffCovarianceJetMap_highDegree Ξ hc (hlo.le.trans hLH)
      p hp he hn lam (fun n=>hlo.trans_le (hl n).1) (fun n=>(hl n).2) hpt j
  · apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_subtype_rng.mpr
    exact (contDiff_cutoffAtomicNode qc i).continuous.continuousAt.tendsto.comp hzt
  · apply tendsto_pi_nhds.mpr
    intro i
    exact hmt.mul ((contDiff_atomicLevel i).continuous.continuousAt.tendsto.comp hzt)
  · intro j
    have hterminal:=tendsto_cutoffEndpointTerminal_of_degree Ξ hε hlo hLH hc hcQ hm0
      p hpt m lam (fun n=>(Q n:ℝ)) hm hl hQ hmt
    have heq (n:ℕ) :
        (Ξ.addHighDegree (p n) (hp n) (he n) (hn n) (lam n) (hlo.trans_le (hl n).1)).first (Q n)-
          (Ξ.addHighDegree (p n) (hp n) (he n) (hn n) (lam n) (hlo.trans_le (hl n).1)).first qc=
        endpointVarianceExpression Ξ (p n) qc (lam n,Q n) :=
      endpointVariance_eq_expression Ξ (p n) (hp n) (he n) (hn n)
        (lam n) (hlo.trans_le (hl n).1) qc (Q n)
    change Tendsto (fun n=>terminalJet (cutoffTerminal (m n) _) j) atTop
      (𝓝 (terminalJet (scaledLogCoshTerminal m0) j))
    simp_rw [heq]
    exact (terminalJetCLM j).continuous.continuousAt.tendsto.comp hterminal

end DepthPaper
