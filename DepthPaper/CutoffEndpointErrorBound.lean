module

public import DepthPaper.CutoffErrorLocalComposition

@[expose] public section


/-! The literal high-degree exponential approximation of the cutoff
terminal datum. Constants are uniform on a compact positive mass/strength
window and the actual exponentially thin endpoint strip. The theorem
bounds genuine Fréchet derivatives, which also control every coordinate
partial derivative of the same total order. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace DepthPaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 64

def cutoffEndpointError (Ξ:AdmissibleCovariance) (p:ℕ) (qc:ℝ)
    (x:ℝ×(ℝ×ℝ)) : TerminalSpace :=
  cutoffErrorTerminal x.1 (endpointVarianceExpression Ξ p qc x.2)

theorem cutoff_endpoint_error_exponential_bound (Ξ:AdmissibleCovariance)
    {ε lamlo lamhi qc cQ CQ:ℝ} (hε:0 < ε) (hlo:0 < lamlo)
    (hLH:lamlo≤lamhi) (hc:qc∈Ioo (0:ℝ) 1) (hcQ:0 < cQ) (N:ℕ) :
    ∃C:ℝ,0 < C ∧ ∃A:ℕ,∃c:ℝ,0 < c ∧ ∃p0:ℕ,1≤p0 ∧
      ∀p:ℕ,p0≤p→∀m∈Icc ε 1,∀lam∈Icc lamlo lamhi,
        ∀Q∈endpointStrip cQ CQ p,
          1 < endpointVarianceExpression Ξ p qc (lam,Q) ∧
          ContDiffAt ℝ ∞ (cutoffEndpointError Ξ p qc) (m,(lam,Q)) ∧
          ∀n≤N,‖iteratedFDeriv ℝ n (cutoffEndpointError Ξ p qc) (m,(lam,Q))‖≤
            C*(p:ℝ)^A*Real.exp (-c*(p:ℝ)) := by
  obtain ⟨C,hC,hg⟩:=cutoffError_low_order_pure_exponential_bound hε N
  obtain ⟨B,hB,hH⟩:=cutoffParameterMap_low_order_jet_bound Ξ
    (L:=lamhi) ⟨hc.1.le,hc.2.le⟩ N
  let E:=endpointVarianceErrorBound Ξ qc cQ lamhi
  let a:=ε^2/4
  have ha:0 < a:=by dsimp only [a];positivity
  have hhi:0≤lamhi:=hlo.le.trans hLH
  obtain ⟨p0,hp0⟩:=exists_nat_gt ((E+1)/lamlo)
  let P:=max 1 p0
  let K:ℝ:=(N.factorial:ℝ)*C*B^N*Real.exp (a*E)
  have hK:0 < K := by
    have hF:0 < (N.factorial:ℝ):=by exact_mod_cast Nat.factorial_pos N
    dsimp only [K]
    positivity
  refine ⟨K,hK,(N+1)*N,a*lamlo,mul_pos ha hlo,P,le_max_left _ _,?_⟩
  intro p hp m hm lam hlam Q hQ
  have hp1:1≤p:=(le_max_left 1 p0).trans hp
  have hpcast:(1:ℝ)≤p:=by exact_mod_cast hp1
  have hpp0:p0≤p:=(le_max_right 1 p0).trans hp
  have hlam0:lam∈Icc (0:ℝ) lamhi:=⟨hlo.le.trans hlam.1,hlam.2⟩
  have hQu:Q∈Icc (0:ℝ) 1:=⟨(endpointStrip_mem_unit hcQ p hQ).1,
    (endpointStrip_mem_unit hcQ p hQ).2.le⟩
  let W:=endpointVarianceExpression Ξ p qc (lam,Q)
  have hWE:|W-lam*(p:ℝ)|≤E:=
    endpointVarianceExpression_sub_linear_bound Ξ hc hcQ hhi p hp1 hlam0 hQ
  have hWlower:lamlo*(p:ℝ)-E≤W := by
    have hll:=mul_le_mul_of_nonneg_right hlam.1 (Nat.cast_nonneg p)
    linarith [(abs_le.mp hWE).1]
  have hPbig:(E+1)/lamlo < (p:ℝ):=
    hp0.trans_le (by exact_mod_cast hpp0)
  have hW:1 < W := by
    have hbig: E+1 < (p:ℝ)*lamlo:=(div_lt_iff₀ hlo).mp hPbig
    nlinarith [hWlower]
  have hmap:cutoffParameterMap Ξ p qc (m,(lam,Q))=(m,W):=rfl
  have hmass:m∈Ioo (0:ℝ) 2:=⟨hε.trans_le hm.1,hm.2.trans_lt (by norm_num)⟩
  have houter:ContDiffAt ℝ ∞ (fun y:ℝ×ℝ=>cutoffErrorTerminal y.1 y.2)
      (cutoffParameterMap Ξ p qc (m,(lam,Q))) := by
    rw [hmap]
    exact contDiffAt_cutoffErrorTerminal hmass (zero_lt_one.trans hW)
  have hsmooth:ContDiffAt ℝ ∞ (cutoffEndpointError Ξ p qc) (m,(lam,Q)) :=
    houter.comp (m,(lam,Q))
      (contDiff_cutoffParameterMap Ξ p qc).contDiffAt
  refine ⟨hW,hsmooth,?_⟩
  intro n hn
  let Dp:=B*(p:ℝ)^(N+1)
  have hDp:1≤Dp := by
    have hh:1≤(p:ℝ)^(N+1):=one_le_pow₀ hpcast
    exact hh.trans (by simpa only [one_mul,Dp] using
      mul_le_mul_of_nonneg_right hB (pow_nonneg (Nat.cast_nonneg p) _))
  have hb:=cutoffError_local_composition_bound (cutoffParameterMap Ξ p qc)
    (contDiff_cutoffParameterMap Ξ p qc) (x:=(m,(lam,Q))) (n:=n) hε hm hW
    (C:=C*Real.exp (-(ε^2)*W/4)) (D:=Dp)
    (fun i hi=>hg i (hi.trans hn) m hm W hW)
    (fun i hi hin=>hH p hp1 (m,(lam,Q)) hlam0 hQu i hi (hin.trans hn))
  have hfact:(n.factorial:ℝ)*C≤(N.factorial:ℝ)*C:=
    mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hn) hC.le
  have hpow:Dp^n≤Dp^N:=pow_le_pow_right₀ hDp hn
  have hprod:(n.factorial:ℝ)*C*Dp^n≤(N.factorial:ℝ)*C*Dp^N:=
    mul_le_mul hfact hpow (pow_nonneg (zero_le_one.trans hDp) _) (by positivity)
  have hexp:Real.exp (-(ε^2)*W/4)≤Real.exp (a*E)*Real.exp (-(a*lamlo)*(p:ℝ)) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp only [a]
    nlinarith [mul_le_mul_of_nonneg_left hWlower ha.le]
  have htotal:=mul_le_mul hprod hexp (Real.exp_pos _).le
    (show 0≤(N.factorial:ℝ)*C*Dp^N by positivity)
  have hcalc:‖iteratedFDeriv ℝ n (cutoffEndpointError Ξ p qc) (m,(lam,Q))‖≤
      (n.factorial:ℝ)*C*Dp^n*Real.exp (-(ε^2)*W/4) := by
    change ‖iteratedFDeriv ℝ n (cutoffEndpointError Ξ p qc) (m,(lam,Q))‖≤
      (n.factorial:ℝ)*(C*Real.exp (-(ε^2)*W/4))*Dp^n at hb
    convert hb using 1 <;> ring
  apply hcalc.trans
  convert htotal using 1 <;> dsimp only [K,Dp] <;> rw [mul_pow,←pow_mul] <;> ring

end DepthPaper
