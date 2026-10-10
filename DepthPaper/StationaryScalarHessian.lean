module

public import DepthPaper.StationarySchurHessian
public import DepthPaper.PartialJetBounds

@[expose] public section


/-! Actual scalar response derivatives and affine Hessian restrictions.
These are calculus identities used in the two stationary eliminations. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace DepthPaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 64

variable {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem scalar_hessian_affine {f:F→ℝ} (L:E→L[ℝ] F) (c:F) (x:E)
    (hf:ContDiffAt ℝ 2 f (c+L x)) (v w:E) :
    fderiv ℝ (fderiv ℝ (fun y=>f (c+L y))) x v w=
      fderiv ℝ (fderiv ℝ f) (c+L x) (L v) (L w) := by
  let T:E→F:=fun y=>c+L y
  have hT:ContDiffAt ℝ 2 T x := contDiffAt_const.add L.contDiff.contDiffAt
  have hDT: fderiv ℝ T=fun _=>L := by
    funext y
    exact (L.hasFDerivAt.const_add c).fderiv
  have he:=scalar_hessian_comp (f:=f) (T:=T) hf hT v w
  rw [hDT] at he
  simpa only [T,Function.comp_def,fderiv_const_apply,zero_apply,map_zero,add_zero] using he

theorem scalar_hessian_from_response {f:ℝ→ℝ} {x d:ℝ}
    (hf:ContDiffAt ℝ 2 f x) (hd:HasDerivAt (deriv f) d x) (v:ℝ) :
    fderiv ℝ (fderiv ℝ f) x v v=v^2*d := by
  have hDf:=(hf.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hD:HasDerivAt (fun y=>fderiv ℝ f y (1:ℝ))
      (fderiv ℝ (fderiv ℝ f) x 1 1) x :=
    by simpa only [deriv,map_zero,add_zero] using
      hDf.hasDerivAt.clm_apply (hasDerivAt_const x (1:ℝ))
  have he:fderiv ℝ (fderiv ℝ f) x 1 1=d := hD.unique hd
  have ho : fderiv ℝ (fderiv ℝ f) x v=v • fderiv ℝ (fderiv ℝ f) x 1 := by
    simpa using (fderiv ℝ (fderiv ℝ f) x).map_smul v (1:ℝ)
  have hi : fderiv ℝ (fderiv ℝ f) x 1 v=v • fderiv ℝ (fderiv ℝ f) x 1 1 := by
    simpa using (fderiv ℝ (fderiv ℝ f) x 1).map_smul v (1:ℝ)
  rw [ho,smul_apply,hi,he]
  simp only [smul_eq_mul]
  ring

theorem stationary_scalar_response_hessian {f:E×ℝ→ℝ} {q:ℝ→E} {x d:ℝ}
    (hf:ContDiffAt ℝ 2 f (q x,x)) (hq:ContDiffAt ℝ 2 q x)
    (hz:∀ᶠy in 𝓝 x,∀v:E,fderiv ℝ f (q y,y) (v,0)=0)
    (hd:HasDerivAt (fun y=>fderiv ℝ f (q y,y) (0,1)) d x) (v:ℝ) :
    fderiv ℝ (fderiv ℝ (fun y=>f (q y,y))) x v v=v^2*d := by
  have hg:ContDiffAt ℝ 2 (fun y=>f (q y,y)) x :=
    hf.comp (g:=f) (f:=fun y:ℝ=>(q y,y)) x (hq.prodMk contDiffAt_id)
  have he:deriv (fun y=>f (q y,y))=ᶠ[𝓝 x]
      (fun y=>fderiv ℝ f (q y,y) (0,1)) := by
    have hqD:∀ᶠy in 𝓝 x,DifferentiableAt ℝ q y :=
      (hq.eventually (by norm_num)).mono (fun _ hu=>hu.differentiableAt (by norm_num))
    have hfD:∀ᶠy in 𝓝 x,DifferentiableAt ℝ f (q y,y) :=
      ((hq.continuousAt.prodMk continuousAt_id).eventually
        (hf.eventually (by norm_num))).mono (fun _ hu=>hu.differentiableAt (by norm_num))
    filter_upwards [hz,hqD,hfD] with y hy hqy hfy
    have hc:=hfy.hasFDerivAt.comp_hasDerivAt (f:=fun t:ℝ=>(q t,t)) y
      (hqy.hasDerivAt.prodMk (hasDerivAt_id y))
    change deriv (f ∘ fun t:ℝ=>(q t,t)) y=_
    rw [hc.deriv]
    have hp:(deriv q y,(1:ℝ))=(deriv q y,0)+(0,1) := by ext <;> simp
    rw [hp,map_add,hy,zero_add]
  exact scalar_hessian_from_response hg (hd.congr_of_eventuallyEq he) v

/-- The genuine graph derivative and eliminated stationarity transfer a
zero reduced gradient to the whole gradient. -/
theorem stationary_full_gradient_zero {f:E×F→ℝ} {q:F→E} {x:F}
    (hf:DifferentiableAt ℝ f (q x,x)) (hq:DifferentiableAt ℝ q x)
    (hz:∀v:E,fderiv ℝ f (q x,x) (v,0)=0)
    (hc:fderiv ℝ (fun y=>f (q y,y)) x=0) :
    fderiv ℝ f (q x,x)=0 := by
  have hd:=hf.hasFDerivAt.comp (f:=fun y:F=>(q y,y)) x (hq.hasFDerivAt.prodMk (hasFDerivAt_id x))
  have hgrad:∀w:F,fderiv ℝ f (q x,x) (0,w)=0 := by
    intro w
    have he:=congrArg (fun L:F→L[ℝ]ℝ=>L w) hc
    change (fderiv ℝ (f ∘ fun y=>(q y,y)) x) w=0 at he
    rw [hd.fderiv] at he
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply] at he
    have hp:(fderiv ℝ q x w,w)=(fderiv ℝ q x w,0)+(0,w) := by ext <;> simp
    rw [hp,map_add,hz,zero_add] at he
    exact he
  apply ContinuousLinearMap.ext
  intro v
  rw [show v=(v.1,0)+(0,v.2) by ext <;> simp,map_add,hz,hgrad]
  simp

end DepthPaper
