module

public import GeneralDepthPaper.BCFParameterDerivative
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section


/-! Genuine closed-subspace regularity on closed real parameter intervals.
Derivative vectors lie in the subspace because they are limits of actual
difference quotients. This includes one-sided interval endpoints. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 64

theorem hasDerivWithinAt_range_closed {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Submodule ℝ F) (hS : IsClosed (S : Set F))
    {f : ℝ→F} {s : Set ℝ} {x : ℝ} {v : F}
    (hx : x∈s) (hs : UniqueDiffWithinAt ℝ s x)
    (hf : ∀y∈s,f y∈S) (hd : HasDerivWithinAt f v s x) : v∈S := by
  haveI : (𝓝[s\{x}] x).NeBot := by
    rw [←accPt_principal_iff_nhdsWithin,←uniqueDiffWithinAt_iff_accPt]
    exact hs
  apply hS.mem_of_tendsto (hasDerivWithinAt_iff_tendsto_slope.mp hd)
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [slope_def_module]
  exact S.smul_mem _ (S.sub_mem (hf y hy.1) (hf x hx))

theorem hasDerivWithinAt_codomainRestriction {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Submodule ℝ F) (f : ℝ→S)
    {s : Set ℝ} {x : ℝ} {v : S}
    (h : HasDerivWithinAt (fun y=>(f y:F)) (v:F) s x) :
    HasDerivWithinAt f v s x := by
  rw [hasDerivWithinAt_iff_isLittleO,Asymptotics.isLittleO_iff] at h ⊢
  intro c hc
  filter_upwards [h hc] with y hy
  exact hy

def closedSubmoduleChain {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Submodule ℝ F) (G : ℕ→ℝ→F) (j : ℕ) (x : ℝ) : S := by
  classical
  exact if h:G j x∈S then ⟨G j x,h⟩ else 0

theorem derivative_chain_mem_closed_submodule {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Submodule ℝ F) (hS : IsClosed (S : Set F))
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (G : ℕ→ℝ→F)
    (hG : ∀j,∀x∈s,HasDerivWithinAt (G j) (G (j+1) x) s x)
    (hzero : ∀x∈s,G 0 x∈S) : ∀j,∀x∈s,G j x∈S := by
  intro j
  induction j with
  | zero => exact hzero
  | succ j ih =>
    intro x hx
    exact hasDerivWithinAt_range_closed S hS hx (hs x hx) ih (hG j x hx)

theorem contDiffOn_closed_submodule_chain {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Submodule ℝ F) (hS : IsClosed (S : Set F))
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (G : ℕ→ℝ→F)
    (hG : ∀j,∀x∈s,HasDerivWithinAt (G j) (G (j+1) x) s x)
    (hzero : ∀x∈s,G 0 x∈S) (j : ℕ) :
    ContDiffOn ℝ ∞ (closedSubmoduleChain S G j) s := by
  have hmem := derivative_chain_mem_closed_submodule S hS hs G hG hzero
  have he (i : ℕ) (x : ℝ) (hx : x∈s) :
      (closedSubmoduleChain S G i x:F)=G i x := by
    simp only [closedSubmoduleChain,dif_pos (hmem i x hx)]
  apply contDiffOn_of_within_derivative_chain hs (closedSubmoduleChain S G) _ j
  intro i x hx
  apply hasDerivWithinAt_codomainRestriction S
  rw [he (i+1) x hx]
  exact (hG i x hx).congr (fun y hy=>(he i y hy)) (he i x hx)

theorem hasDerivWithinAt_closed_submodule_chain {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Submodule ℝ F) (hS : IsClosed (S : Set F))
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (G : ℕ→ℝ→F)
    (hG : ∀j,∀x∈s,HasDerivWithinAt (G j) (G (j+1) x) s x)
    (hzero : ∀x∈s,G 0 x∈S) (j : ℕ) {x : ℝ} (hx : x∈s) :
    HasDerivWithinAt (closedSubmoduleChain S G j)
      (closedSubmoduleChain S G (j+1) x) s x := by
  have hmem := derivative_chain_mem_closed_submodule S hS hs G hG hzero
  have he (i : ℕ) (y : ℝ) (hy : y∈s) :
      (closedSubmoduleChain S G i y:F)=G i y := by
    simp only [closedSubmoduleChain,dif_pos (hmem i y hy)]
  apply hasDerivWithinAt_codomainRestriction S
  rw [he (j+1) x hx]
  exact (hG j x hx).congr (fun y hy=>(he j y hy)) (he j x hx)

end GeneralDepthPaper
