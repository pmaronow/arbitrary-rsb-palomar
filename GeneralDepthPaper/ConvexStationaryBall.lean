module

public import GeneralDepthPaper.ConvexCoerciveCalculus
public import FourPapersCommon.StationarySelector
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option backward.privateInPublic true

@[expose] public section


/-! Genuine stationary selection on a fixed compact ball.  Existence comes
from the extreme value theorem and the Hessian lower bound; smoothness comes
from the implicit function theorem and uniqueness. The norm may be a product
norm, and no stationary point or smooth selector is assumed. -/
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace GeneralDepthPaper
variable {Θ E : Type*}
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
set_option maxHeartbeats 1200000

/-- The partial derivative is a genuine element of the continuous dual. -/
def partialGradient (f : Θ×E → ℝ) (θ : Θ) (z : E) : E→L[ℝ]ℝ :=
  fderiv ℝ (fun w => f (θ,w)) z

theorem contDiffAt_partialGradient (f : Θ×E → ℝ) {θ : Θ} {z : E}
    (hf : ContDiffAt ℝ ∞ f (θ,z)) :
    ContDiffAt ℝ ∞ (fun p : Θ×E => partialGradient f p.1 p.2) (θ,z) := by
  have hL : ContDiffAt ℝ ∞ (fun w : (Θ×E)×E => f (w.1.1,w.2)) ((θ,z),z) :=
    hf.comp ((θ,z),z) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact hL.fderiv contDiffAt_snd (by simp)

theorem partialGradient_partial_hessian (f : Θ×E → ℝ) {θ : Θ} {z : E}
    (hf : ContDiffAt ℝ ∞ f (θ,z)) :
    fderiv ℝ (fun p : Θ×E => partialGradient f p.1 p.2) (θ,z) ∘L
      ContinuousLinearMap.inr ℝ Θ E = fderiv ℝ (partialGradient f θ) z := by
  have hG := (contDiffAt_partialGradient f hf).differentiableAt (by norm_num)
  have hp := (hasFDerivAt_const (𝕜:=ℝ) (x:=z) θ).prodMk (hasFDerivAt_id (𝕜:=ℝ) z)
  have hc := hG.hasFDerivAt.comp z hp
  have he : ContinuousLinearMap.prod (0 : E→L[ℝ]Θ) (ContinuousLinearMap.id ℝ E)=
      ContinuousLinearMap.inr ℝ Θ E := rfl
  have hfun : partialGradient f θ=(fun x=>fderiv ℝ (fun w=>f (θ,w)) x) := rfl
  rw [hfun]
  simpa only [Function.comp_def,partialGradient,he] using hc.fderiv.symm

private theorem continuous_fiber_at (f : Θ×E → ℝ) {θ : Θ} {z : E}
    (hf : ContDiffAt ℝ ∞ f (θ,z)) : ContDiffAt ℝ ∞ (fun w => f (θ,w)) z :=
  hf.comp z (contDiffAt_const.prodMk contDiffAt_id)

/-- A strict margin and a small actual gradient exclude the boundary from
the set of minimizers. -/
theorem coercive_ball_boundary_value (F : E → ℝ) (c z₀ : E) (R d κ : ℝ)
    (hd : 0<d) (hκ : 0<κ) (hz₀ : dist z₀ c ≤ R-d)
    (hf : ∀ z∈closedBall c R, ContDiffAt ℝ ∞ F z)
    (hH : ∀ z∈closedBall c R, ∀ v : E,
      κ*‖v‖^2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (hsmall : ‖fderiv ℝ F z₀‖ < κ*d/2)
    {z : E} (hz : z∈closedBall c R \ ball c R) : F z₀ < F z := by
  have hx : z₀∈closedBall c R := by rw [mem_closedBall];linarith
  have hdR : R ≤ dist z c := le_of_not_gt hz.2
  have ht := dist_triangle z z₀ c
  have hdist : d ≤ ‖z-z₀‖ := by
    have ht' : dist z c ≤ ‖z-z₀‖ + dist z₀ c := by simpa only [dist_eq_norm] using ht
    linarith
  have hpos : 0<‖z-z₀‖ := hd.trans_le hdist
  have hT := coercive_taylor_lower F (convex_closedBall c R) hf κ hH hx hz.1
  have hnorm := (fderiv ℝ F z₀).le_opNorm (z-z₀)
  have hlower : -‖fderiv ℝ F z₀‖*‖z-z₀‖ ≤ fderiv ℝ F z₀ (z-z₀) := by
    have he := (neg_le_abs (fderiv ℝ F z₀ (z-z₀))).trans
      (by simpa only [abs_neg,Real.norm_eq_abs] using hnorm)
    linarith
  have hsp := mul_lt_mul_of_pos_right hsmall hpos
  have hquad := mul_nonneg hκ.le (mul_nonneg hpos.le (sub_nonneg.mpr hdist))
  nlinarith

/-- An interior minimizer and stationary point is constructed by compactness. -/
theorem exists_coercive_ball_stationary (F : E → ℝ) (c z₀ : E) (R d κ : ℝ)
    (hd : 0<d) (hκ : 0<κ) (hz₀ : dist z₀ c ≤ R-d)
    (hf : ∀ z∈closedBall c R, ContDiffAt ℝ ∞ F z)
    (hH : ∀ z∈closedBall c R, ∀ v : E,
      κ*‖v‖^2 ≤ fderiv ℝ (fderiv ℝ F) z v v)
    (hsmall : ‖fderiv ℝ F z₀‖ < κ*d/2) :
    ∃ z∈ball c R, fderiv ℝ F z=0 ∧ IsMinOn F (closedBall c R) z := by
  have hx : z₀∈closedBall c R := by rw [mem_closedBall];linarith
  have hc : ContinuousOn F (closedBall c R) := fun z hz =>
    (hf z hz).continuousAt.continuousWithinAt
  obtain ⟨z,hz,hm⟩ := (isCompact_closedBall c R).exists_isMinOn_mem_subset
    (s:=ball c R) hc hx (fun z hz => coercive_ball_boundary_value F c z₀ R d κ hd hκ
      hz₀ hf hH hsmall hz)
  have hlocal : IsLocalMin F z := hm.isLocalMin
    (mem_nhds_iff.mpr ⟨ball c R,ball_subset_closedBall,isOpen_ball,hz⟩)
  exact ⟨z,hz,hlocal.fderiv_eq_zero,hm⟩

/-- A selector defined from actual stationarity, with a harmless value outside
parameters admitting an interior stationary point. -/
def coerciveBallStationarySelector (f : Θ×E → ℝ) (c : E) (R : ℝ) (θ : Θ) : E :=
  by
    classical
    exact if h : ∃z∈ball c R, partialGradient f θ z=0 then h.choose else c

/-- Complete pointwise selection from smoothness, coercivity and the margin. -/
theorem coerciveBallStationarySelector_spec (f : Θ×E → ℝ) (c z₀ : E) (R d κ : ℝ)
    (θ : Θ) (hd : 0<d) (hκ : 0<κ) (hz₀ : dist z₀ c ≤ R-d)
    (hf : ∀ z∈closedBall c R, ContDiffAt ℝ ∞ f (θ,z))
    (hH : ∀ z∈closedBall c R, ∀ v : E,
      κ*‖v‖^2 ≤ fderiv ℝ (partialGradient f θ) z v v)
    (hsmall : ‖partialGradient f θ z₀‖ < κ*d/2) :
    coerciveBallStationarySelector f c R θ∈ball c R ∧
    partialGradient f θ (coerciveBallStationarySelector f c R θ)=0 ∧
    IsMinOn (fun z => f (θ,z)) (closedBall c R) (coerciveBallStationarySelector f c R θ) ∧
    (∀w∈closedBall c R,partialGradient f θ w=0 → w=coerciveBallStationarySelector f c R θ) ∧
    ‖coerciveBallStationarySelector f c R θ-z₀‖ ≤ ‖partialGradient f θ z₀‖/κ := by
  classical
  have hff : ∀ z∈closedBall c R, ContDiffAt ℝ ∞ (fun w => f (θ,w)) z :=
    fun z hz => continuous_fiber_at f (hf z hz)
  obtain ⟨z,hz,hgrad,hmin⟩ := exists_coercive_ball_stationary (fun w => f (θ,w)) c z₀ R d κ
    hd hκ hz₀ hff hH hsmall
  have hex : ∃z∈ball c R,partialGradient f θ z=0 := ⟨z,hz,hgrad⟩
  have hsel : coerciveBallStationarySelector f c R θ∈ball c R ∧
      partialGradient f θ (coerciveBallStationarySelector f c R θ)=0 := by
    simpa only [coerciveBallStationarySelector,dif_pos hex] using hex.choose_spec
  have hu : ∀w∈closedBall c R,partialGradient f θ w=0 → w=coerciveBallStationarySelector f c R θ := by
    intro w hw hgw
    exact coercive_stationary_unique (fun w => f (θ,w)) (convex_closedBall c R) hff hκ hH
      hw (ball_subset_closedBall hsel.1) hgw hsel.2
  have hzeq := hu z (ball_subset_closedBall hz) hgrad
  have hx : z₀∈closedBall c R := by rw [mem_closedBall];linarith
  refine ⟨hsel.1,hsel.2,hzeq ▸ hmin,hu,?_⟩
  exact coercive_stationary_displacement (fun w => f (θ,w)) (convex_closedBall c R)
    hff hκ hH hx (ball_subset_closedBall hsel.1) hsel.2

/-- The actual selector is smooth throughout an open parameter domain. -/
theorem contDiffOn_coerciveBallStationarySelector (f : Θ×E → ℝ) (O : Set Θ)
    (hO : IsOpen O) (c : E) (R d κ : ℝ) (z₀ : Θ → E)
    (hd : 0<d) (hκ : 0<κ)
    (hz₀ : ∀θ∈O,dist (z₀ θ) c ≤ R-d)
    (hf : ∀θ∈O,∀z∈closedBall c R, ContDiffAt ℝ ∞ f (θ,z))
    (hH : ∀θ∈O,∀z∈closedBall c R,∀v:E,
      κ*‖v‖^2 ≤ fderiv ℝ (partialGradient f θ) z v v)
    (hsmall : ∀θ∈O,‖partialGradient f θ (z₀ θ)‖ < κ*d/2) :
    ContDiffOn ℝ ∞ (coerciveBallStationarySelector f c R) O := by
  intro θ hθ
  let q := coerciveBallStationarySelector f c R
  have hspec := coerciveBallStationarySelector_spec f c (z₀ θ) R d κ θ hd hκ
    (hz₀ θ hθ) (hf θ hθ) (hH θ hθ) (hsmall θ hθ)
  have hq : q θ∈closedBall c R := ball_subset_closedBall hspec.1
  have hG := contDiffAt_partialGradient f (hf θ hθ (q θ) hq)
  have hpos : ∀v:E,v≠0 → 0<(fderiv ℝ (fun p:Θ×E=>partialGradient f p.1 p.2) (θ,q θ)
      ∘L ContinuousLinearMap.inr ℝ Θ E) v v := by
    rw [partialGradient_partial_hessian f (hf θ hθ (q θ) hq)]
    intro v hv
    exact (mul_pos hκ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv))).trans_le (hH θ hθ (q θ) hq v)
  obtain ⟨w,hwθ,hws,hwe,_⟩ := FourPapersCommon.exists_smooth_stationary_selector
    (fun p:Θ×E=>partialGradient f p.1 p.2) (θ,q θ) hG (by simp) hspec.2.1 hpos
  have hwb : ∀ᶠu in 𝓝 θ,w u∈ball c R :=
    hws.continuousAt.eventually (isOpen_ball.mem_nhds (hwθ.symm ▸ hspec.1))
  have heq : q =ᶠ[𝓝 θ] w := by
    filter_upwards [hO.mem_nhds hθ,hwe,hwb] with u hu hgu hbu
    have hs := coerciveBallStationarySelector_spec f c (z₀ u) R d κ u hd hκ
      (hz₀ u hu) (hf u hu) (hH u hu) (hsmall u hu)
    exact (hs.2.2.2.1 (w u) (ball_subset_closedBall hbu) hgu).symm
  exact (hws.congr_of_eventuallyEq heq).contDiffWithinAt

end GeneralDepthPaper
