module

public import DepthPaper.ImplicitRootJetBounds

@[expose] public section


/-! A third-order genuine implicit-root estimate, used for the reduced C³ objective. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 64

theorem implicit_graph_third_norm_eq {q : E → ℝ} {θ : E}
    (hq : ContDiffAt ℝ ∞ q θ) :
    ‖iteratedFDeriv ℝ 3 (fun u => (u,q u)) θ‖ = ‖iteratedFDeriv ℝ 3 q θ‖ := by
  have hid : ‖iteratedFDeriv ℝ 3 (id : E → E) θ‖ = 0 := by
    rw [←norm_iteratedFDeriv_fderiv (n:=2), ]
    have he : fderiv ℝ (id : E → E) = (fun _ => ContinuousLinearMap.id ℝ E) :=
      funext fun u => fderiv_id
    rw [he]
    simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero]
  change ‖iteratedFDeriv ℝ 3 (fun u => (id u,q u)) θ‖ = _
  rw [iteratedFDeriv_prodMk contDiffAt_id hq (by simp),
    ContinuousMultilinearMap.opNorm_prod, hid,
    max_eq_right (norm_nonneg _)]


theorem implicit_correction_third_jet_bound
    {A : E × ℝ → ℝ} {q : E → ℝ} {θ : E} {ε : ℝ}
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1/2)
    (hA : ContDiffAt ℝ ∞ A (θ,q θ)) (hq : ContDiffAt ℝ ∞ q θ)
    (heq : ∀ᶠ u in 𝓝 θ, q u = 1-A (u,q u))
    (hb : ∀i:ℕ, 1 ≤ i → i ≤ 3 → ‖iteratedFDeriv ℝ i A (θ,q θ)‖ ≤ ε) :
    ‖iteratedFDeriv ℝ 3 q θ‖ ≤ 8*ε := by
  have hq12 := implicit_correction_first_second_jet_bound hε hεsmall hA hq heq
    (hb 1 le_rfl (by omega)) (hb 2 (by omega) (by omega))
  let H : E → E × ℝ := fun u => (u,q u)
  have hH : ContDiffAt ℝ ∞ H θ := contDiffAt_id.prodMk hq
  have hg1 : ‖fderiv ℝ H θ‖ ≤ 1 := (implicit_graph_first_norm_le hq).trans
    (max_le le_rfl (by simpa only [norm_iteratedFDeriv_one] using hq12.1.trans (by linarith)))
  have hg2 : ‖iteratedFDeriv ℝ 2 H θ‖ ≤ 1 :=
    (implicit_graph_second_norm_eq hq).le.trans (hq12.2.trans (by linarith))
  let U : E → (E × ℝ →L[ℝ] ℝ) := fun u => fderiv ℝ A (H u)
  let V : E → (E →L[ℝ] E × ℝ) := fderiv ℝ H
  have hUA : ContDiffAt ℝ ∞ (fderiv ℝ A) (H θ) := hA.fderiv_right (m:=∞) (by simp)
  have hU : ContDiffAt ℝ ∞ U θ := hUA.comp θ hH
  have hV : ContDiffAt ℝ ∞ V θ := hH.fderiv_right (m:=∞) (by simp)
  have hUb (i:ℕ) (hi:i ≤ 2) : ‖iteratedFDeriv ℝ i U θ‖ ≤ (i.factorial:ℝ)*ε := by
    have ho (j:ℕ) (hj:j ≤ i) : ‖iteratedFDeriv ℝ j (fderiv ℝ A) (H θ)‖ ≤ ε := by
      rw [norm_iteratedFDeriv_fderiv]
      exact hb (j+1) (by omega) (by omega)
    have hg (j:ℕ) (hj:1 ≤ j) (hji:j ≤ i) : ‖iteratedFDeriv ℝ j H θ‖ ≤ (1:ℝ)^j := by
      have hcases : j=1 ∨ j=2 := by omega
      rcases hcases with rfl|rfl
      · simpa only [norm_iteratedFDeriv_one,one_pow] using hg1
      · simpa only [one_pow] using hg2
    simpa only [one_pow,mul_one,U,Function.comp_def] using
      norm_iteratedFDeriv_comp_le_at hUA hH i ε 1 ho hg
  have hU0 : ‖U θ‖ ≤ ε := by simpa using hUb 0 (by omega)
  have hU1 : ‖iteratedFDeriv ℝ 1 U θ‖ ≤ ε := by simpa using hUb 1 (by omega)
  have hU2 : ‖iteratedFDeriv ℝ 2 U θ‖ ≤ 2*ε := by simpa using hUb 2 (by omega)
  have hV0 : ‖V θ‖ ≤ 1 := hg1
  have hV1 : ‖iteratedFDeriv ℝ 1 V θ‖ ≤ 2*ε := by
    rw [norm_iteratedFDeriv_fderiv]
    exact (implicit_graph_second_norm_eq hq).le.trans hq12.2
  have hV2 : ‖iteratedFDeriv ℝ 2 V θ‖ = ‖iteratedFDeriv ℝ 3 q θ‖ := by
    rw [norm_iteratedFDeriv_fderiv]
    exact implicit_graph_third_norm_eq hq
  let B := ContinuousLinearMap.compL ℝ E (E × ℝ) ℝ
  have hB : ‖B‖ ≤ 1 := ContinuousLinearMap.norm_compL_le ℝ E (E × ℝ) ℝ
  have hbound := norm_iteratedFDeriv_bilinear_le_at B hU hV 2
  have hbound' : ‖iteratedFDeriv ℝ 2 (fun u=>B (U u) (V u)) θ‖ ≤
      ‖B‖*(‖U θ‖*‖iteratedFDeriv ℝ 2 V θ‖+
        2*‖iteratedFDeriv ℝ 1 U θ‖*‖iteratedFDeriv ℝ 1 V θ‖+
          ‖iteratedFDeriv ℝ 2 U θ‖*‖V θ‖) := by
    simpa [Finset.sum_range_succ, norm_iteratedFDeriv_zero] using hbound
  have he := eventually_fderiv_implicit_correction hA hq heq
  have hq3 : ‖iteratedFDeriv ℝ 3 q θ‖ =
      ‖iteratedFDeriv ℝ 2 (fun u=>B (U u) (V u)) θ‖ := by
    rw [←norm_iteratedFDeriv_fderiv (n:=2)]
    have hen : (fderiv ℝ q) =ᶠ[𝓝 θ] (fun u=>-(B (U u) (V u))) := he
    rw [(hen.iteratedFDeriv ℝ 2).eq_of_nhds]
    have hn : (fun u=>-(B (U u)) (V u)) = -(fun u=>B (U u) (V u)) := by
      funext u
      exact neg_apply (B (U u)) (V u)
    rw [hn,iteratedFDeriv_neg_apply,norm_neg]
  have hb0 : 0 ≤ ‖U θ‖*‖iteratedFDeriv ℝ 2 V θ‖+
      2*‖iteratedFDeriv ℝ 1 U θ‖*‖iteratedFDeriv ℝ 1 V θ‖+
      ‖iteratedFDeriv ℝ 2 U θ‖*‖V θ‖ := by positivity
  have hc := hbound'.trans (mul_le_mul_of_nonneg_right hB hb0)
  rw [one_mul,hV2,←hq3] at hc
  have hp0 := mul_le_mul_of_nonneg_right hU0 (norm_nonneg (iteratedFDeriv ℝ 3 q θ))
  have hp1 := mul_le_mul hU1 hV1 (norm_nonneg _) hε
  have hp2 := mul_le_mul hU2 hV0 (norm_nonneg _) (by positivity : 0≤2*ε)
  nlinarith [norm_nonneg (iteratedFDeriv ℝ 3 q θ)]

end DepthPaper
