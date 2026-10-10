module

public import DepthPaper.CutoffErrorFrechetBounds
public import DepthPaper.EndpointVarianceJets

@[expose] public section


/-! Actual total derivatives of the endpoint-variance substitution and
local composition estimates for the terminal error. The substitution is
a globally smooth polynomial map; the terminal error is used on its genuine
open positive-mass, positive-variance domain. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff BigOperators
namespace DepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

theorem norm_iteratedFDeriv_precomp_contraction
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E→L[ℝ] F) (hL : ‖L‖≤1) (f:F→G) (hf:ContDiff ℝ ∞ f)
    (j:ℕ) (x:E) :
    ‖iteratedFDeriv ℝ j (fun y=>f (L y)) x‖≤‖iteratedFDeriv ℝ j f (L x)‖ := by
  change ‖iteratedFDeriv ℝ j (f ∘ L) x‖≤_
  rw [L.iteratedFDeriv_comp_right hf x (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hp : (∏i:Fin j,‖L‖)≤1 :=
    Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun _ _=>hL)
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hp (norm_nonneg (iteratedFDeriv ℝ j f (L x)))

def cutoffParameterMap (Ξ:AdmissibleCovariance) (p:ℕ) (qc:ℝ)
    (x:ℝ×(ℝ×ℝ)) : ℝ×ℝ :=
  (x.1,endpointVarianceExpression Ξ p qc x.2)

theorem contDiff_endpointVarianceExpression (Ξ:AdmissibleCovariance) (p:ℕ) (qc:ℝ) :
    ContDiff ℝ ∞ (endpointVarianceExpression Ξ p qc) := by
  change ContDiff ℝ ∞ (fun w:ℝ×ℝ=>
    Ξ.first w.2-Ξ.first qc+w.1*(p:ℝ)*(w.2^(p-1)-qc^(p-1)))
  exact ((Ξ.contDiff_first.comp contDiff_snd).sub contDiff_const).add
    ((contDiff_fst.mul contDiff_const).mul ((contDiff_snd.pow (p-1)).sub contDiff_const))

theorem contDiff_cutoffParameterMap (Ξ:AdmissibleCovariance) (p:ℕ) (qc:ℝ) :
    ContDiff ℝ ∞ (cutoffParameterMap Ξ p qc) := by
  exact contDiff_fst.prodMk ((contDiff_endpointVarianceExpression Ξ p qc).comp contDiff_snd)

theorem cutoffParameterMap_jet_bound (Ξ:AdmissibleCovariance) {qc L:ℝ}
    (hc:qc∈Icc (0:ℝ) 1) (j:ℕ) (hj:1≤j) :
    ∃C:ℝ,1≤C ∧ ∀p:ℕ,1≤p→∀x:ℝ×(ℝ×ℝ),
      x.2.1∈Icc (0:ℝ) L→x.2.2∈Icc (0:ℝ) 1→
      ‖iteratedFDeriv ℝ j (cutoffParameterMap Ξ p qc) x‖≤C*(p:ℝ)^(j+1) := by
  obtain ⟨B,hB,hb⟩:=endpointVarianceExpression_jet_bound Ξ (L:=L) hc j
  refine ⟨max B 1,le_max_right _ _,?_⟩
  intro p hp x hlam hQ
  let W:=endpointVarianceExpression Ξ p qc
  have hW:ContDiff ℝ ∞ W := contDiff_endpointVarianceExpression Ξ p qc
  have hw:=norm_iteratedFDeriv_precomp_contraction
    (ContinuousLinearMap.snd ℝ ℝ (ℝ×ℝ)) (ContinuousLinearMap.norm_snd_le ..) W hW j x
  have hwB:=hw.trans (hb p hp x.2 hlam hQ)
  have hfst : ‖iteratedFDeriv ℝ j (fun y:ℝ×(ℝ×ℝ)=>y.1) x‖≤1 := by
    have hh:=norm_iteratedFDeriv_comp_contraction
      (ContinuousLinearMap.fst ℝ ℝ (ℝ×ℝ)) (ContinuousLinearMap.norm_fst_le ..)
      id contDiff_id j x
    apply hh.trans
    rw [iteratedDeriv_id]
    split_ifs with hzero hone
    · omega
    · simp
    · simp
  change ‖iteratedFDeriv ℝ j (fun y=>(Prod.fst y,(W ∘ Prod.snd) y)) x‖≤_
  rw [iteratedFDeriv_prodMk (contDiff_fst.of_le (show (j:ℕ∞ω)≤∞ by simp)).contDiffAt
    ((hW.comp contDiff_snd).of_le (show (j:ℕ∞ω)≤∞ by simp)).contDiffAt le_rfl,
    ContinuousMultilinearMap.opNorm_prod]
  apply max_le
  · have hpj : (1:ℝ)≤(p:ℝ)^(j+1) := one_le_pow₀ (by exact_mod_cast hp)
    exact hfst.trans ((hpj.trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (le_max_right B 1) (pow_nonneg (Nat.cast_nonneg p) _))))
  · exact hwB.trans (mul_le_mul_of_nonneg_right (le_max_left B 1)
      (pow_nonneg (Nat.cast_nonneg p) _))

end DepthPaper
