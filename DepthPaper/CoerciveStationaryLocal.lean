module

public import DepthPaper.ConvexStationaryBall
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Topology.Compactness.Compact

set_option backward.privateInPublic true

@[expose] public section


/-! Local smoothness of the actual compact-ball stationary selector from
pointwise hypotheses on one compact fiber. Only a finite-order common tube
is used; the all-order smoothness comes from the local implicit function. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace DepthPaper
variable {Θ E : Type*}
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 64

/-- Genuine derivative coercivity gives uniqueness even when only one
actual derivative is known on the whole convex region. -/
theorem coercive_dual_map_unique (G : E→E→L[ℝ]ℝ) {s:Set E}
    (hs:Convex ℝ s) (hd:∀z∈s,DifferentiableAt ℝ G z) {κ:ℝ} (hκ:0<κ)
    (hB:∀z∈s,∀v:E,κ*‖v‖^2 ≤ fderiv ℝ G z v v)
    {x y:E} (hx:x∈s) (hy:y∈s) (hx0:G x=0) (hy0:G y=0) : x=y := by
  let δ := y-x
  let L := fun t:ℝ=>x+t • δ
  have hm {t:ℝ} (ht:t∈Icc (0:ℝ) 1) : L t∈s := hs.add_smul_sub_mem hx hy ht
  have hL (t:ℝ) : HasDerivAt L δ t := by
    simpa [L] using ((hasDerivAt_id t).smul_const δ).const_add x
  have hD {t:ℝ} (ht:t∈Icc (0:ℝ) 1) :
      HasDerivAt (fun u=>G (L u) δ-κ*‖δ‖^2*u)
        (fderiv ℝ G (L t) δ δ-κ*‖δ‖^2) t := by
    have hc := (hd _ (hm ht)).hasFDerivAt.comp_hasDerivAt t (hL t)
    have ha := hc.clm_apply (hasDerivAt_const t δ)
    simpa only [Pi.sub_def,id_eq,mul_one,Function.comp_def,map_zero,add_zero] using
      ha.sub ((hasDerivAt_id t).const_mul (κ*‖δ‖^2))
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) 1)
    (fun t ht=>(hD ht).continuousAt.continuousWithinAt)
    (fun t ht=>(hD (interior_subset ht)).hasDerivWithinAt)
    (fun t ht=>sub_nonneg.mpr (hB _ (hm (interior_subset ht)) δ))
  have h := hmono (by simp) (by simp) (show (0:ℝ)≤1 by norm_num)
  simp only [L,zero_smul,one_smul,add_zero,δ,add_sub_cancel,hx0,hy0,
    ContinuousLinearMap.zero_apply,mul_zero,mul_one,zero_sub,sub_zero] at h
  have hn : ‖y-x‖=0 := by
    by_contra hn
    have hp := mul_pos hκ (sq_pos_of_ne_zero hn)
    linarith
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

private theorem eventual_differentiable {X Y:Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {G:X→Y} {p:X} (h:ContDiffAt ℝ ∞ G p) :
    ∀ᶠu in 𝓝 p,DifferentiableAt ℝ G u := by
  have he := (h.of_le (show (1:ℕ∞ω)≤∞ by simp)).eventually (by simp)
  exact he.mono (fun _ hu=>hu.differentiableAt (by simp))

/-- Compactness preserves a positive Jacobian margin on a common parameter
neighborhood; no common C∞ neighborhood is asserted. -/
theorem eventually_coercive_partial_gradient (f:Θ×E→ℝ) (c:E) (R:ℝ)
    {θ:Θ} {κ:ℝ} (hκ:0<κ)
    (hf:∀z∈closedBall c R,ContDiffAt ℝ ∞ f (θ,z))
    (hB:∀z∈closedBall c R,∀v:E,
      κ*‖v‖^2≤fderiv ℝ (partialGradient f θ) z v v) :
    ∀ᶠu in 𝓝 θ,∀z∈closedBall c R,
      DifferentiableAt ℝ (partialGradient f u) z ∧
      ∀v:E,(κ/2)*‖v‖^2≤fderiv ℝ (partialGradient f u) z v v := by
  let G := fun p:Θ×E=>partialGradient f p.1 p.2
  let J := fun p:Θ×E=>fderiv ℝ G p ∘L ContinuousLinearMap.inr ℝ Θ E
  let S : Set (Θ×E) := {p | DifferentiableAt ℝ G p ∧
    ∀v:E,(κ/2)*‖v‖^2≤J p v v}
  have hpoint (z:E) (hz:z∈closedBall c R) : S∈𝓝 (θ,z) := by
    have hG := contDiffAt_partialGradient f (hf z hz)
    have hJ : ContinuousAt J (θ,z) := by
      exact ((hG.fderiv_right (m:=∞) (by simp)).continuousAt).clm_comp continuousAt_const
    have hnear : ∀ᶠp in 𝓝 (θ,z),‖J p-J (θ,z)‖<κ/2 := by
      have he := hJ.eventually (isOpen_ball.mem_nhds (mem_ball_self (by positivity : 0<κ/2)))
      simpa only [mem_ball,dist_eq_norm] using he
    filter_upwards [eventual_differentiable hG,hnear] with p hp hnp
    refine ⟨hp,fun v=>?_⟩
    have hbase : κ*‖v‖^2≤J (θ,z) v v := by
      change κ*‖v‖^2 ≤ (fderiv ℝ (fun p:Θ×E=>partialGradient f p.1 p.2) (θ,z) ∘L
        ContinuousLinearMap.inr ℝ Θ E) v v
      rw [partialGradient_partial_hessian f (hf z hz)]
      exact hB z hz v
    have hn := ((J p-J (θ,z)).le_opNorm v)
    have ha := ((J p-J (θ,z)) v).le_opNorm v
    have hn' : ‖(J p-J (θ,z)) v v‖≤‖J p-J (θ,z)‖*‖v‖^2 := by
      exact ha.trans (by nlinarith [mul_le_mul_of_nonneg_right hn (norm_nonneg v)])
    have hl := (neg_le_abs ((J p-J (θ,z)) v v)).trans
      (by simpa only [Real.norm_eq_abs] using hn')
    simp only [ContinuousLinearMap.sub_apply] at hl
    have hm := mul_le_mul_of_nonneg_right hnp.le (sq_nonneg ‖v‖)
    linarith
  have htube : S∈𝓝 θ ×ˢ nhdsSet (closedBall c R) :=
    (isCompact_closedBall c R).mem_prod_nhdsSet_of_forall
      (fun z hz=>by simpa only [←nhds_prod_eq] using hpoint z hz)
  obtain ⟨U,hU,V,hV,hUV⟩ := Filter.mem_prod_iff.mp htube
  filter_upwards [hU] with u hu
  intro z hz
  have hp := hUV (show (u,z)∈U×ˢV from ⟨hu,subset_of_mem_nhdsSet hV hz⟩)
  have hc := hp.1.hasFDerivAt.comp z
    ((hasFDerivAt_const (𝕜:=ℝ) (x:=z) u).prodMk (hasFDerivAt_id (𝕜:=ℝ) z))
  have he : ContinuousLinearMap.prod (0:E→L[ℝ]Θ) (ContinuousLinearMap.id ℝ E)=
      ContinuousLinearMap.inr ℝ Θ E := rfl
  have hder : fderiv ℝ (partialGradient f u) z=J (u,z) := by
    simpa only [Function.comp_def,he,J,G] using hc.fderiv
  exact ⟨hc.differentiableAt,by simpa only [hder] using hp.2⟩

/-- All-order smoothness of the chosen stationary selector follows from
one compact fiber with a strict gradient margin and genuine coercivity. -/
theorem contDiffAt_coerciveBallStationarySelector (f:Θ×E→ℝ)
    (c z₀:E) (R d κ:ℝ) (θ:Θ) (hd:0<d) (hκ:0<κ)
    (hz₀:dist z₀ c≤R-d)
    (hf:∀z∈closedBall c R,ContDiffAt ℝ ∞ f (θ,z))
    (hB:∀z∈closedBall c R,∀v:E,
      κ*‖v‖^2≤fderiv ℝ (partialGradient f θ) z v v)
    (hsmall:‖partialGradient f θ z₀‖<κ*d/2) :
    ContDiffAt ℝ ∞ (coerciveBallStationarySelector f c R) θ := by
  let q := coerciveBallStationarySelector f c R
  have hs := coerciveBallStationarySelector_spec f c z₀ R d κ θ hd hκ hz₀ hf hB hsmall
  have hq : q θ∈closedBall c R := ball_subset_closedBall hs.1
  have hG := contDiffAt_partialGradient f (hf _ hq)
  have hpos : ∀v:E,v≠0→0<(fderiv ℝ (fun p:Θ×E=>partialGradient f p.1 p.2) (θ,q θ)
      ∘L ContinuousLinearMap.inr ℝ Θ E) v v := by
    rw [partialGradient_partial_hessian f (hf _ hq)]
    intro v hv
    exact (mul_pos hκ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv))).trans_le (hB _ hq v)
  obtain ⟨w,hwθ,hws,hwe,_⟩ := FourPapersCommon.exists_smooth_stationary_selector
    (fun p:Θ×E=>partialGradient f p.1 p.2) (θ,q θ) hG (by simp) hs.2.1 hpos
  have hwb : ∀ᶠu in 𝓝 θ,w u∈ball c R :=
    hws.continuousAt.eventually (isOpen_ball.mem_nhds (hwθ.symm ▸ hs.1))
  have heq : q=ᶠ[𝓝 θ] w := by
    filter_upwards [eventually_coercive_partial_gradient f c R hκ hf hB,hwe,hwb]
      with u hco hwu hwbu
    have hex : ∃z∈ball c R,partialGradient f u z=0 := ⟨w u,hwbu,hwu⟩
    have hsel : q u∈ball c R ∧ partialGradient f u (q u)=0 := by
      simpa only [q,coerciveBallStationarySelector,dif_pos hex] using hex.choose_spec
    exact coercive_dual_map_unique (partialGradient f u) (convex_closedBall c R)
      (fun z hz=>(hco z hz).1) (by positivity : 0<κ/2)
      (fun z hz=>(hco z hz).2) (ball_subset_closedBall hsel.1)
      (ball_subset_closedBall hwbu) hsel.2 hwu
  exact hws.congr_of_eventuallyEq heq

end DepthPaper
