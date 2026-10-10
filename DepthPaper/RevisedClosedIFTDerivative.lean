module

public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! Relative implicit differentiation at boundary parameters. The existing
root's continuity and the actual equation suffice; no ambient extension,
local root existence, or root derivative is assumed. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace DepthPaper.RevisedClosedIFT
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 64
universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def partialX (L : E×F→L[ℝ]F) : E→L[ℝ]F := L ∘L ContinuousLinearMap.inl ℝ E F
def partialY (L : E×F→L[ℝ]F) : F→L[ℝ]F := L ∘L ContinuousLinearMap.inr ℝ E F
def implicitDerivative (L : E×F→L[ℝ]F) : E→L[ℝ]F :=
  -(partialY L).inverse ∘L partialX L

theorem hasFDerivWithinAt_implicit_root {D : Set E} {K : Set F}
    {Φ : E×F→F} {y : E→F} {θ : E} {L : E×F→L[ℝ]F}
    (hθ : θ∈D) (hyK : ∀u∈D,y u∈K)
    (hyc : ContinuousWithinAt y D θ)
    (hzero : ∀u∈D,Φ (u,y u)=0)
    (hΦ : HasFDerivWithinAt Φ L (D×ˢK) (θ,y θ))
    (hinv : (partialY L).IsInvertible) :
    HasFDerivWithinAt y (implicitDerivative L) D θ := by
  let B := partialX L
  let A := partialY L
  let T : E×F→E×F := fun p=>(p.1,Φ p)
  let TL : E×F→L[ℝ](E×F) := (ContinuousLinearMap.fst ℝ E F).prod L
  let TI : E×F→L[ℝ](E×F) := (ContinuousLinearMap.fst ℝ E F).prod
    (A.inverse ∘L (ContinuousLinearMap.snd ℝ E F-B ∘L ContinuousLinearMap.fst ℝ E F))
  have hleft : Function.LeftInverse TI TL := by
    rintro ⟨v,w⟩
    apply Prod.ext
    · rfl
    · change A.inverse (L (v,w)-B v)=w
      have he : L (v,w)=B v+A w := by
        change L (v,w)=L (v,0)+L (0,w)
        rw [←map_add]
        simp only [Prod.mk_add_mk,add_zero,zero_add]
      rw [he,add_sub_cancel_left]
      exact hinv.inverse_apply_self w
  have hT : HasFDerivWithinAt T TL (D×ˢK) (θ,y θ) :=
    hasFDerivWithinAt_fst.prodMk hΦ
  let g : E→E×F := fun u=>(u,y u)
  let h : E→E×F := fun u=>(u,0)
  have hg : Tendsto g (𝓝[D] θ) (𝓝[D×ˢK] (g θ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuousWithinAt_id.prodMk hyc,?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact ⟨hu,hyK u hu⟩
  have hh : HasFDerivWithinAt h (ContinuousLinearMap.inl ℝ E F) D θ := by
    convert (hasFDerivWithinAt_id θ D).prodMk
      (hasFDerivWithinAt_const (0 : F) θ D) using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro v
      rfl
  have he : T ∘ g =ᶠ[𝓝[D] θ] h := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [Function.comp_def,T,g,h,hzero u hu]
  have hd := HasFDerivWithinAt.of_comp_of_leftInverse hg hT hh he hleft hθ
  have hs := hasFDerivAt_snd.comp_hasFDerivWithinAt θ hd
  convert hs using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro v
    change -(partialY L).inverse (partialX L v)=A.inverse (0-B v)
    simp only [B,A,zero_sub,map_neg]

end DepthPaper.RevisedClosedIFT
