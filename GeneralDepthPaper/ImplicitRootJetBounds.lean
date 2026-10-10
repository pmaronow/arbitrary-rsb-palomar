module

public import GeneralDepthPaper.IntervalRootDomain
public import GeneralDepthPaper.PointwiseDerivativeBounds
public import GeneralDepthPaper.CompositionDifferenceBounds
public import Mathlib.Analysis.Normed.Operator.Prod

@[expose] public section


/-! True first and second Fréchet jet bounds for the small implicit
correction Q=1-A(theta,Q). The derivative equations are obtained by actual
differentiation of the local root equation, with the product sup norm. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

theorem implicit_graph_first_norm_le {q : E → ℝ} {θ : E}
    (hq : ContDiffAt ℝ ∞ q θ) :
    ‖fderiv ℝ (fun u => (u,q u)) θ‖ ≤ max 1 ‖fderiv ℝ q θ‖ := by
  change ‖fderiv ℝ (fun u => (id u,q u)) θ‖ ≤ _
  rw [DifferentiableAt.fderiv_prodMk differentiableAt_id (hq.differentiableAt (by simp)),
    ContinuousLinearMap.opNorm_prod, Prod.norm_def, fderiv_id]
  exact max_le_max (show ‖ContinuousLinearMap.id ℝ E‖ ≤ 1 from
    ContinuousLinearMap.norm_id_le) le_rfl

theorem implicit_graph_second_norm_eq {q : E → ℝ} {θ : E}
    (hq : ContDiffAt ℝ ∞ q θ) :
    ‖iteratedFDeriv ℝ 2 (fun u => (u,q u)) θ‖ = ‖iteratedFDeriv ℝ 2 q θ‖ := by
  have hid : ‖iteratedFDeriv ℝ 2 (id : E → E) θ‖ = 0 := by
    rw [←norm_iteratedFDeriv_fderiv (n:=1), norm_iteratedFDeriv_one]
    have he : fderiv ℝ (id : E → E) = (fun _ => ContinuousLinearMap.id ℝ E) :=
      funext fun u => fderiv_id
    rw [he]
    simpa only [norm_zero] using congrArg norm
      (hasFDerivAt_const (𝕜:=ℝ) (x:=θ) (c:=ContinuousLinearMap.id ℝ E)).fderiv
  change ‖iteratedFDeriv ℝ 2 (fun u => (id u,q u)) θ‖ = _
  rw [iteratedFDeriv_prodMk contDiffAt_id hq (by simp),
    ContinuousMultilinearMap.opNorm_prod, hid,
    max_eq_right (norm_nonneg _)]

theorem eventually_fderiv_implicit_correction {A : E × ℝ → ℝ} {q : E → ℝ} {θ : E}
    (hA : ContDiffAt ℝ ∞ A (θ,q θ)) (hq : ContDiffAt ℝ ∞ q θ)
    (heq : ∀ᶠ u in 𝓝 θ, q u = 1-A (u,q u)) :
    (fun u => fderiv ℝ q u) =ᶠ[𝓝 θ]
      (fun u => -(fderiv ℝ A (u,q u)).comp (fderiv ℝ (fun v => (v,q v)) u)) := by
  let H : E → E × ℝ := fun u => (u,q u)
  have hH : ContDiffAt ℝ ∞ H θ := contDiffAt_id.prodMk hq
  have hAe : ∀ᶠ y in 𝓝 (H θ), ContDiffAt ℝ 1 A y :=
    (hA.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
  have hAd : ∀ᶠ u in 𝓝 θ, DifferentiableAt ℝ A (H u) :=
    hH.continuousAt.eventually (hAe.mono (fun _ hy => hy.differentiableAt (by simp)))
  have hHd := eventually_differentiableAt_of_contDiffAt hH
  have heq' : q =ᶠ[𝓝 θ] (fun u => 1-A (u,q u)) := heq
  filter_upwards [heq'.fderiv (𝕜:=ℝ),hAd,hHd] with u hu hAu hHu
  rw [hu, fderiv_const_sub]
  change -fderiv ℝ (A ∘ H) u = -(fderiv ℝ A (H u)).comp (fderiv ℝ H u)
  rw [fderiv_comp u hAu hHu]

theorem implicit_correction_first_second_jet_bound
    {A : E × ℝ → ℝ} {q : E → ℝ} {θ : E} {ε : ℝ}
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1/2)
    (hA : ContDiffAt ℝ ∞ A (θ,q θ)) (hq : ContDiffAt ℝ ∞ q θ)
    (heq : ∀ᶠ u in 𝓝 θ, q u = 1-A (u,q u))
    (h1 : ‖iteratedFDeriv ℝ 1 A (θ,q θ)‖ ≤ ε)
    (h2 : ‖iteratedFDeriv ℝ 2 A (θ,q θ)‖ ≤ ε) :
    ‖iteratedFDeriv ℝ 1 q θ‖ ≤ ε ∧ ‖iteratedFDeriv ℝ 2 q θ‖ ≤ 2*ε := by
  let H : E → E × ℝ := fun u => (u,q u)
  have hH : ContDiffAt ℝ ∞ H θ := contDiffAt_id.prodMk hq
  have he := eventually_fderiv_implicit_correction hA hq heq
  have hA1 : ‖fderiv ℝ A (H θ)‖ ≤ ε := by simpa only [norm_iteratedFDeriv_one] using h1
  have hg := implicit_graph_first_norm_le hq
  have hchain : ‖fderiv ℝ q θ‖ ≤ ε * max 1 ‖fderiv ℝ q θ‖ := by
    have hbound := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ A (H θ)) (fderiv ℝ H θ)
    calc
      _ = ‖(fderiv ℝ A (H θ)).comp (fderiv ℝ H θ)‖ := by rw [he.eq_of_nhds, norm_neg]
      _ ≤ _ := hbound.trans (mul_le_mul hA1 hg (norm_nonneg _) hε)
  have hq1 : ‖fderiv ℝ q θ‖ ≤ ε := by
    by_cases hx : ‖fderiv ℝ q θ‖ ≤ 1
    · simpa only [max_eq_left hx, mul_one] using hchain
    · rw [max_eq_right (le_of_not_ge hx)] at hchain
      have hp : 0 < ‖fderiv ℝ q θ‖ := lt_of_lt_of_le zero_lt_one (le_of_not_ge hx)
      nlinarith
  have hg1 : ‖fderiv ℝ H θ‖ ≤ 1 := by
    apply hg.trans
    exact max_le le_rfl (hq1.trans (by linarith))
  let U : E → (E × ℝ →L[ℝ] ℝ) := fun u => fderiv ℝ A (H u)
  let V : E → (E →L[ℝ] E × ℝ) := fderiv ℝ H
  have hUA : ContDiffAt ℝ ∞ (fderiv ℝ A) (H θ) := hA.fderiv_right (m:=∞) (by simp)
  have hU : ContDiffAt ℝ ∞ U θ := hUA.comp θ hH
  have hV : ContDiffAt ℝ ∞ V θ := hH.fderiv_right (m:=∞) (by simp)
  have hU0 : ‖U θ‖ ≤ ε := hA1
  have hU1 : ‖iteratedFDeriv ℝ 1 U θ‖ ≤ ε := by
    rw [norm_iteratedFDeriv_one]
    change ‖fderiv ℝ ((fderiv ℝ A) ∘ H) θ‖ ≤ ε
    rw [fderiv_comp θ (hUA.differentiableAt (by simp)) (hH.differentiableAt (by simp))]
    have hh := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ (fderiv ℝ A) (H θ)) (fderiv ℝ H θ)
    have hA2 : ‖fderiv ℝ (fderiv ℝ A) (H θ)‖ ≤ ε := by
      simpa only [←norm_iteratedFDeriv_fderiv (n:=1),norm_iteratedFDeriv_one] using h2
    exact hh.trans ((mul_le_mul hA2 hg1 (norm_nonneg _) hε).trans_eq (mul_one ε))
  have hV1 : ‖iteratedFDeriv ℝ 1 V θ‖ = ‖iteratedFDeriv ℝ 2 q θ‖ := by
    rw [norm_iteratedFDeriv_fderiv]
    exact implicit_graph_second_norm_eq hq
  let B := ContinuousLinearMap.compL ℝ E (E × ℝ) ℝ
  have hb := norm_iteratedFDeriv_bilinear_le_at B hU hV 1
  have hb' : ‖iteratedFDeriv ℝ 1 (fun u => B (U u) (V u)) θ‖ ≤
      ‖B‖ * (‖U θ‖ * ‖iteratedFDeriv ℝ 1 V θ‖ +
        ‖iteratedFDeriv ℝ 1 U θ‖ * ‖V θ‖) := by
    simpa [Finset.sum_range_succ, norm_iteratedFDeriv_zero] using hb
  have hq2eq : ‖iteratedFDeriv ℝ 2 q θ‖ =
      ‖iteratedFDeriv ℝ 1 (fun u => B (U u) (V u)) θ‖ := by
    rw [←norm_iteratedFDeriv_fderiv (n:=1), norm_iteratedFDeriv_one]
    have hen : (fderiv ℝ q) =ᶠ[𝓝 θ] (fun u => -(B (U u) (V u))) := he
    rw [hen.fderiv_eq (𝕜:=ℝ)]
    rw [fderiv_fun_neg, norm_neg, ←norm_iteratedFDeriv_one]
  have hsecond : ‖iteratedFDeriv ℝ 2 q θ‖ ≤ ε * ‖iteratedFDeriv ℝ 2 q θ‖ + ε := by
    rw [hq2eq]
    apply hb'.trans
    have hnB : ‖B‖ ≤ 1 := ContinuousLinearMap.norm_compL_le ℝ E (E × ℝ) ℝ
    have hsum0 : 0 ≤ ‖U θ‖ * ‖iteratedFDeriv ℝ 1 V θ‖ +
        ‖iteratedFDeriv ℝ 1 U θ‖ * ‖V θ‖ := by positivity
    apply (mul_le_mul_of_nonneg_right hnB hsum0).trans
    rw [one_mul]
    have hfirst := mul_le_mul_of_nonneg_right hU0 (norm_nonneg (iteratedFDeriv ℝ 1 V θ))
    have hlast := mul_le_mul hU1 hg1 (norm_nonneg _) hε
    rw [hV1] at hfirst
    have hcombine := add_le_add hfirst hlast
    rw [mul_one] at hcombine
    rw [hq2eq] at hcombine
    rw [hV1,hq2eq]
    exact hcombine
  constructor
  · simpa only [norm_iteratedFDeriv_one] using hq1
  · nlinarith [norm_nonneg (iteratedFDeriv ℝ 2 q θ)]

theorem intervalImplicitRoot_first_second_jet_bound
    (A : E × ℝ → ℝ) (U : Set (E × ℝ)) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) {a b : ℝ} (hab : a < b)
    {θ : E} (hθ : θ ∈ intervalRootDomain (fun p => p.2-1+A p) U a b)
    {ε : ℝ} (hε : 0 ≤ ε) (hεsmall : ε ≤ 1/2)
    (h1 : ‖iteratedFDeriv ℝ 1 A
      (θ,intervalImplicitRoot (fun p => p.2-1+A p) a b θ)‖ ≤ ε)
    (h2 : ‖iteratedFDeriv ℝ 2 A
      (θ,intervalImplicitRoot (fun p => p.2-1+A p) a b θ)‖ ≤ ε) :
    ‖iteratedFDeriv ℝ 1 (intervalImplicitRoot (fun p => p.2-1+A p) a b) θ‖ ≤ ε ∧
    ‖iteratedFDeriv ℝ 2 (intervalImplicitRoot (fun p => p.2-1+A p) a b) θ‖ ≤ 2*ε := by
  let G : E × ℝ → ℝ := fun p => p.2-1+A p
  let q := intervalImplicitRoot G a b
  have hG : ContDiffOn ℝ ∞ G U :=
    (contDiff_snd.contDiffOn.sub contDiffOn_const).add hA
  have hO := isOpen_intervalRootDomain G U hU hG hab
  have hq : ContDiffAt ℝ ∞ q θ :=
    (intervalImplicitRoot_smooth_domain G U hU hG hab).contDiffAt (hO.mem_nhds hθ)
  have hs := intervalImplicitRoot_spec_domain G U hU hG hab hθ
  have hAθ : ContDiffAt ℝ ∞ A (θ,q θ) :=
    hA.contDiffAt (hU.mem_nhds (hθ.1 (q θ) (Ioo_subset_Icc_self hs.1)).1)
  have heq : ∀ᶠ u in 𝓝 θ, q u = 1-A (u,q u) := by
    filter_upwards [hO.mem_nhds hθ] with u hu
    have hz := (intervalImplicitRoot_spec_domain G U hU hG hab hu).2
    dsimp [G] at hz
    linarith
  exact implicit_correction_first_second_jet_bound hε hεsmall hAθ hq heq h1 h2

end GeneralDepthPaper
