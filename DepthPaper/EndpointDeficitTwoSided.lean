module

public import DepthPaper.CutoffDeficitBounds
public import DepthPaper.EndpointDeficitScale
public import DepthPaper.EndpointStrip

@[expose] public section


/-! Literal two-sided endpoint deficit estimate of Lemma 4.3. All kernels,
cutoff-state laws and Gaussian moment bounds are instantiated. Constants
are independent of the degree, mass, endpoint and valid atomic coordinates. -/
noncomputable section
open Set
namespace DepthPaper
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 64

def cutoffDriverVarianceBound (Ξ:AdmissibleCovariance) (qc L:ℝ):ℝ :=
  Ξ.first qc+L*Real.exp (-Real.log qc)/(-Real.log qc)

theorem cutoffDriverVarianceBound_nonneg (Ξ:AdmissibleCovariance)
    {qc L:ℝ} (hc:qc∈Ioo (0:ℝ) 1) (hL:0≤L):
    0≤cutoffDriverVarianceBound Ξ qc L:=by
  unfold cutoffDriverVarianceBound
  have hf:=(Ξ.first_pos hc.1).le
  have hl:0 < -Real.log qc:=neg_pos.mpr (Real.log_neg hc.1 hc.2)
  positivity

theorem highDegree_cutoff_variance_le (Ξ:AdmissibleCovariance)
    {qc L:ℝ} (hc:qc∈Ioo (0:ℝ) 1) (hL:0≤L)
    (p:ℕ) (hp:4≤p) (he:Even p) (hn:p∉Ξ.degrees)
    (lam:ℝ) (hlam:0 < lam) (hlamL:lam≤L):
    (Ξ.addHighDegree p hp he hn lam hlam).first qc≤cutoffDriverVarianceBound Ξ qc L:=by
  rw [Ξ.addHighDegree_first]
  have hb:=nat_mul_pow_sub_one_bound hc p (by omega)
  have h1:=mul_le_mul_of_nonneg_left hb hlam.le
  have hl:0 < -Real.log qc:=neg_pos.mpr (Real.log_neg hc.1 hc.2)
  have h2:=mul_le_mul_of_nonneg_right hlamL
    (by positivity : 0≤Real.exp (-Real.log qc)/(-Real.log qc))
  dsimp only [cutoffDriverVarianceBound]
  have hh:=add_le_add_left (h1.trans h2) (Ξ.first qc)
  convert hh using 1 <;> ring

theorem endpoint_deficit_two_sided (Ξ:AdmissibleCovariance)
    {lamlo lamhi qc cQ CQ:ℝ} (hlo:0 < lamlo) (hLH:lamlo≤lamhi)
    (hc:qc∈Ioo (0:ℝ) 1) (hcQ:0 < cQ):
    ∃c:ℝ,0 < c ∧ ∃C:ℝ,0 < C ∧ ∃P:ℕ,
      ∀p:ℕ,P≤p→∀he:Even p,∃hp:4≤p,∃hn:p∉Ξ.degrees,
        ∀lam:ℝ,∀hlam:lam∈Icc lamlo lamhi,∀Q:Overlap,
          (Q:ℝ)∈endpointStrip cQ CQ p→∀m∈Ioc (0:ℝ) 1,
            ∀r:ℕ,∀z:AtomicPoint r,∀hz:IsAtomicPoint z,
              atomicLocation z (Fin.last r) < qc→
                c*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-m^2*lam*(p:ℝ)/2)≤
                  1-Gamma (Ξ.addHighDegree p hp he hn lam (hlo.trans_le hlam.1))
                    (twoLevelMeasure z hz m Q) Q ∧
                1-Gamma (Ξ.addHighDegree p hp he hn lam (hlo.trans_le hlam.1))
                    (twoLevelMeasure z hz m Q) Q≤
                  C*(p:ℝ)^(-(1/2:ℝ))*Real.exp (-m^2*lam*(p:ℝ)/2) := by
  let B:=cutoffDriverVarianceBound Ξ qc lamhi
  let E:=endpointVarianceErrorBound Ξ qc cQ lamhi
  let a:=lamlo/2
  let V:=lamhi+E
  have hhi:0≤lamhi:=hlo.le.trans hLH
  have hB:0≤B:=cutoffDriverVarianceBound_nonneg Ξ hc hhi
  have hE:0≤E:=by
    dsimp only [E,endpointVarianceErrorBound]
    have hf:=(Ξ.first_pos (by norm_num : (0:ℝ) < 1)).le
    have hl:0 < -Real.log qc:=neg_pos.mpr (Real.log_neg hc.1 hc.2)
    positivity
  have ha:0 < a:=by dsimp only [a];positivity
  have hV:0 < V:=by dsimp only [V];linarith
  let R:=3*B+2
  let cl:ℝ:=(1/4)*doobCompactLowerConstant R*(Real.sqrt (2*Real.pi*V))⁻¹*Real.exp (-E/2)
  let cu:ℝ:=8*(Real.sqrt (2*Real.pi*a))⁻¹*Real.exp (E/2)
  have hcl:0 < cl:=by dsimp only [cl];have:=doobCompactLowerConstant_pos R;positivity
  have hcu:0 < cu:=by dsimp only [cu];positivity
  obtain ⟨p0,hp0⟩:=exists_nat_gt (2*(E+1)/lamlo)
  let P:=max p0 (max 4 (Ξ.degrees.sup id+1))
  refine ⟨cl,hcl,cu,hcu,P,?_⟩
  intro p hpP he
  have hp4:4≤p:=(le_max_left _ _).trans ((le_max_right _ _).trans hpP)
  have hp1:1≤p:=by omega
  have hpR:(1:ℝ)≤p:=by exact_mod_cast hp1
  have hpn:p0≤p:=(le_max_left _ _).trans hpP
  have hn:p∉Ξ.degrees:=by
    intro hmem
    have hh:p≤Ξ.degrees.sup id:=Finset.le_sup (f:=id) hmem
    have hbig:Ξ.degrees.sup id+1≤p:=(le_max_right _ _).trans ((le_max_right _ _).trans hpP)
    omega
  refine ⟨hp4,hn,?_⟩
  intro lam hlam Q hQ m hm r z hz hzqc
  let X:=Ξ.addHighDegree p hp4 he hn lam (hlo.trans_le hlam.1)
  let W:=X.first Q-X.first qc
  have herror:|W-lam*(p:ℝ)|≤E:=by
    have hh:=endpointVarianceExpression_sub_linear_bound Ξ hc hcQ hhi p hp1
      (lam:=lam) ⟨hlo.le.trans hlam.1,hlam.2⟩ hQ
    rw [←endpointVariance_eq_expression Ξ p hp4 he hn lam (hlo.trans_le hlam.1) qc Q] at hh
    exact hh
  have hWlo:lamlo*(p:ℝ)-E≤W:=by
    have hl:=mul_le_mul_of_nonneg_right hlam.1 (Nat.cast_nonneg p)
    linarith [(abs_le.mp herror).1]
  have hbig:2*(E+1) < lamlo*(p:ℝ):=by
    have hh:=hp0.trans_le (show (p0:ℝ)≤p by exact_mod_cast hpn)
    have hh2:=(div_lt_iff₀ hlo).mp hh
    nlinarith
  have hW:1≤W:=by linarith
  have hWa:a*(p:ℝ)≤W:=by dsimp only [a];nlinarith
  have hWV:W≤V*(p:ℝ):=by
    have hl:=mul_le_mul_of_nonneg_right hlam.2 (Nat.cast_nonneg p)
    have hEpow:=mul_le_mul_of_nonneg_left hpR hE
    dsimp only [V]
    nlinarith [(abs_le.mp herror).2]
  have hqcQ:qc < (Q:ℝ):=by
    by_contra hh
    have hle:X.first Q≤X.first qc:=X.first_strictMonoOn.monotoneOn
      Q.property.1 hc.1.le (le_of_not_gt hh)
    dsimp only [W] at hW
    linarith
  have hvar:X.first qc≤B:=highDegree_cutoff_variance_le Ξ hc hhi p hp4 he hn
    lam (hlo.trans_le hlam.1) hlam.2
  have hactual:=cutoff_endpoint_deficit_bounds X z hz m hm Q qc hzqc hqcQ hB hvar hW
  have hscale:=variance_endpoint_scale_bounds ⟨hm.1.le,hm.2⟩ hE ha hV p hp1 hWa hWV herror
  have hK:0≤(1/4)*doobCompactLowerConstant R:=by have:=(doobCompactLowerConstant_pos R).le;positivity
  have hl:=mul_le_mul_of_nonneg_left hscale.1 hK
  have hu:=mul_le_mul_of_nonneg_left hscale.2 (by norm_num : (0:ℝ)≤8)
  constructor
  · have hh:(1/4)*doobCompactLowerConstant R*(Real.sqrt (2*Real.pi*V))⁻¹*
        Real.exp (-E/2)*degreeDeficitScale m lam p≤
        (1/4)*doobCompactLowerConstant R*(Real.sqrt (2*Real.pi*W))⁻¹*Real.exp (-m^2*W/2):=by
      convert hl using 1 <;> ring
    have hbound:=hh.trans hactual.1
    rw [degreeDeficitScale_eq_rpow] at hbound
    convert hbound using 1 <;> dsimp only [cl] <;> ring
  · have hh:8*(Real.sqrt (2*Real.pi*W))⁻¹*Real.exp (-m^2*W/2)≤
        8*(Real.sqrt (2*Real.pi*a))⁻¹*Real.exp (E/2)*degreeDeficitScale m lam p:=by
      convert hu using 1 <;> ring
    have hbound:=hactual.2.trans hh
    rw [degreeDeficitScale_eq_rpow] at hbound
    convert hbound using 1 <;> dsimp only [cu] <;> ring

end DepthPaper
