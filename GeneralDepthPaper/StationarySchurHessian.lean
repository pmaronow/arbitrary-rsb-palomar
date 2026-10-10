module

public import GeneralDepthPaper.CriticalHessianChart
public import GeneralDepthPaper.SchurHessian
public import Mathlib.Analysis.Calculus.FDeriv.Prod

set_option backward.privateInPublic true

@[expose] public section


/-! The actual reduced Hessian after eliminating a stationary coordinate
is the genuine Schur complement. Stationary equations are differentiated,
so no reduced-Hessian formula is assumed. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace GeneralDepthPaper
variable {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 64

private theorem eventual_diff {X Y:Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f:X→Y} {x:X} (hf:ContDiffAt ℝ 2 f x) :
    ∀ᶠu in 𝓝 x,DifferentiableAt ℝ f u :=
  (hf.eventually (by norm_num)).mono (fun _ hu=>hu.differentiableAt (by norm_num))

/-- Genuine derivative of the nonlinear stationary-coordinate graph. -/
theorem stationaryLeftGraph_fderiv {q:F→E} {x:F} (hq:DifferentiableAt ℝ q x) :
    fderiv ℝ (fun y=>(q y,y)) x=(fderiv ℝ q x).prod (ContinuousLinearMap.id ℝ F) := by
  exact (hq.hasFDerivAt.prodMk (hasFDerivAt_id x)).fderiv

/-- Genuine second graph derivative, including its zero affine coordinate. -/
theorem stationaryLeftGraph_second {q:F→E} {x:F} (hq:ContDiffAt ℝ 2 q x) (v w:F) :
    fderiv ℝ (fderiv ℝ (fun y=>(q y,y))) x v w=
      (fderiv ℝ (fderiv ℝ q) x v w,0) := by
  have he : fderiv ℝ (fun y=>(q y,y))=ᶠ[𝓝 x]
      (fun y=>(fderiv ℝ q y).prod (ContinuousLinearMap.id ℝ F)) := by
    filter_upwards [eventual_diff hq] with y hy
    exact stationaryLeftGraph_fderiv hy
  have hd := (hq.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  let L : (F→L[ℝ]E)→L[ℝ](F→L[ℝ](E×F)) :=
    (ContinuousLinearMap.compL ℝ F E (E×F)) (ContinuousLinearMap.inl ℝ E F)
  have hid : (fun y=>(fderiv ℝ q y).prod (ContinuousLinearMap.id ℝ F))=
      (fun y=>L (fderiv ℝ q y)+ContinuousLinearMap.inr ℝ E F) := by
    ext y u <;> simp [L]
  have ha := (L.hasFDerivAt.comp x hd.hasFDerivAt).add_const (ContinuousLinearMap.inr ℝ E F)
  simp only [Function.comp_def] at ha
  rw [he.fderiv_eq,hid,ha.fderiv]
  simp [L]

/-- Differentiating the true local stationary equation gives the eliminated
block equation for L = −Dq. -/
theorem stationary_schur_block_equation {f:E×F→ℝ} {q:F→E} {x:F}
    (hf:ContDiffAt ℝ 2 f (q x,x)) (hq:ContDiffAt ℝ 2 q x)
    (hz:∀ᶠy in 𝓝 x,∀v:E,fderiv ℝ f (q y,y) (v,0)=0) (v:E) (w:F) :
    fderiv ℝ (fderiv ℝ f) (q x,x) (-fderiv ℝ q x w,0) (v,0)=
      fderiv ℝ (fderiv ℝ f) (q x,x) (0,w) (v,0) := by
  let H := fun y:F=>(q y,y)
  let G := fun y:F=>(fderiv ℝ f (H y)).comp (ContinuousLinearMap.inl ℝ E F)
  have hH : ContDiffAt ℝ 2 H x := hq.prodMk contDiffAt_id
  have hDf := (hf.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  change DifferentiableAt ℝ (fderiv ℝ f) (H x) at hDf
  have hG := (hDf.hasFDerivAt.comp x (hH.differentiableAt (by norm_num)).hasFDerivAt).clm_comp
    (hasFDerivAt_const (𝕜:=ℝ) (x:=x) (ContinuousLinearMap.inl ℝ E F))
  have he : G=ᶠ[𝓝 x] (fun _=>0) := by
    filter_upwards [hz] with y hy
    ext u
    exact hy u
  have hzD : fderiv ℝ G x=0 := by rw [he.fderiv_eq];exact fderiv_const_apply _
  simp only [Function.comp_def] at hG
  have hzD' : fderiv ℝ (fun y=>fderiv ℝ f (H y) ∘L ContinuousLinearMap.inl ℝ E F) x=0 := hzD
  have heval := congrArg (fun M:F→L[ℝ](E→L[ℝ]ℝ)=>M w v) (hG.fderiv.symm.trans hzD')
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,zero_apply,
    map_zero,zero_add,ContinuousLinearMap.inl_apply] at heval
  have hdH := stationaryLeftGraph_fderiv (hq.differentiableAt (by norm_num))
  change fderiv ℝ (fderiv ℝ f) (q x,x) (fderiv ℝ H x w) (v,0)=0 at heval
  rw [show H=(fun y=>(q y,y)) by rfl,hdH] at heval
  have hpair : (fderiv ℝ q x w,w)=(fderiv ℝ q x w,0)+(0,w) := by ext <;> simp
  simp only [ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply] at heval
  rw [hpair,map_add] at heval
  simp only [ContinuousLinearMap.add_apply] at heval
  have hneg : (-fderiv ℝ q x w,(0:F))=-(fderiv ℝ q x w,(0:F)) := by ext <;> simp
  rw [hneg,map_neg]
  simp only [ContinuousLinearMap.neg_apply]
  linarith

/-- The true reduced Hessian is the actual Schur complement. -/
theorem stationary_reduced_hessian {f:E×F→ℝ} {q:F→E} {x:F}
    (hf:ContDiffAt ℝ 2 f (q x,x)) (hq:ContDiffAt ℝ 2 q x)
    (hz:∀v:E,fderiv ℝ f (q x,x) (v,0)=0) :
    fderiv ℝ (fderiv ℝ (fun y=>f (q y,y))) x=
      schurComplement (fderiv ℝ (fderiv ℝ f) (q x,x)) (-fderiv ℝ q x) := by
  ext v w
  have he := scalar_hessian_comp (T:=fun y=>(q y,y)) hf (hq.prodMk contDiffAt_id) v w
  simp only [Function.comp_def] at he
  rw [stationaryLeftGraph_second hq, hz] at he
  rw [stationaryLeftGraph_fderiv (hq.differentiableAt (by norm_num))] at he
  simpa [schurComplement,schurElimination] using he

/-- Positive eliminated block and positive actual reduced Hessian imply a
positive full actual Hessian. -/
theorem stationary_full_hessian_positive {f:E×F→ℝ} {q:F→E} {x:F}
    (hf:ContDiffAt ℝ 2 f (q x,x)) (hq:ContDiffAt ℝ 2 q x)
    (hz:∀ᶠy in 𝓝 x,∀v:E,fderiv ℝ f (q y,y) (v,0)=0)
    (hA:∀v:E,v≠0→0<fderiv ℝ (fderiv ℝ f) (q x,x) (v,0) (v,0))
    (hS:∀v:F,v≠0→0<fderiv ℝ (fderiv ℝ (fun y=>f (q y,y))) x v v) :
    ∀v:E×F,v≠0→0<fderiv ℝ (fderiv ℝ f) (q x,x) v v := by
  have hz0 : ∀v:E,fderiv ℝ f (q x,x) (v,0)=0 := hz.self_of_nhds
  apply (schur_positive_iff _ (-fderiv ℝ q x) (scalar_hessian_symmetric hf)
    (stationary_schur_block_equation hf hq hz)).2
  refine ⟨hA,?_⟩
  rw [←stationary_reduced_hessian hf hq hz0]
  exact hS

end GeneralDepthPaper
