module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Normed.Operator.Bilinear

@[expose] public section


/-! Critical Hessians transform by the true chart derivative. Stationarity
and Hessian positivity are transferred using an actual bijective derivative,
without assuming a coordinate Hessian formula. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace DepthPaper
variable {E F:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
set_option maxHeartbeats 800000

/-- The genuine second chain rule, in curried continuous-dual notation. -/
theorem scalar_hessian_comp {f:F→ℝ} {T:E→F} {x:E}
    (hf:ContDiffAt ℝ 2 f (T x)) (hT:ContDiffAt ℝ 2 T x) (v w:E) :
    fderiv ℝ (fderiv ℝ (f ∘ T)) x v w =
      fderiv ℝ (fderiv ℝ f) (T x) (fderiv ℝ T x v) (fderiv ℝ T x w)+
      fderiv ℝ f (T x) (fderiv ℝ (fderiv ℝ T) x v w) := by
  have hdf := hf.differentiableAt (by norm_num)
  have hdT := hT.differentiableAt (by norm_num)
  have hdDf := (hf.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hdDT := (hT.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hef : ∀ᶠu in 𝓝 (T x),DifferentiableAt ℝ f u :=
    (hf.eventually (by norm_num)).mono (fun _ hu=>hu.differentiableAt (by norm_num))
  have heT : ∀ᶠu in 𝓝 x,DifferentiableAt ℝ T u :=
    (hT.eventually (by norm_num)).mono (fun _ hu=>hu.differentiableAt (by norm_num))
  have he : fderiv ℝ (f ∘ T)=ᶠ[𝓝 x]
      (fun u=>(fderiv ℝ f (T u)).comp (fderiv ℝ T u)) := by
    filter_upwards [heT,hdT.continuousAt.eventually hef] with u hTu hfu
    exact fderiv_comp u hfu hTu
  have hc := (hdDf.hasFDerivAt.comp x hdT.hasFDerivAt).clm_comp hdDT.hasFDerivAt
  simp only [Function.comp_def] at hc
  rw [he.fderiv_eq,hc.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply]
  ring

/-- The chart's curvature term vanishes at an actual critical point. -/
theorem critical_hessian_comp {f:F→ℝ} {T:E→F} {x:E}
    (hf:ContDiffAt ℝ 2 f (T x)) (hT:ContDiffAt ℝ 2 T x)
    (hcrit:fderiv ℝ f (T x)=0) :
    fderiv ℝ (fderiv ℝ (f ∘ T)) x =
      (fderiv ℝ (fderiv ℝ f) (T x)).bilinearComp (fderiv ℝ T x) (fderiv ℝ T x) := by
  ext v w
  rw [scalar_hessian_comp hf hT,hcrit]
  simp

/-- A surjective chart derivative transfers actual stationarity backwards. -/
theorem critical_of_critical_comp {f:F→ℝ} {T:E→F} {x:E}
    (hf:DifferentiableAt ℝ f (T x)) (hT:DifferentiableAt ℝ T x)
    (hs:Function.Surjective (fderiv ℝ T x)) (hc:fderiv ℝ (f ∘ T) x=0) :
    fderiv ℝ f (T x)=0 := by
  ext v
  obtain ⟨u,rfl⟩ := hs v
  have he := congrArg (fun L:E→L[ℝ]ℝ=>L u) hc
  rw [fderiv_comp x hf hT] at he
  exact he

/-- At a critical point, positivity is equivalent in genuine coordinates. -/
theorem critical_hessian_positive_iff {f:F→ℝ} {T:E→F} {x:E}
    (hf:ContDiffAt ℝ 2 f (T x)) (hT:ContDiffAt ℝ 2 T x)
    (hb:Function.Bijective (fderiv ℝ T x)) (hc:fderiv ℝ (f ∘ T) x=0) :
    (∀v:E,v≠0→0<fderiv ℝ (fderiv ℝ (f ∘ T)) x v v) ↔
      (∀v:F,v≠0→0<fderiv ℝ (fderiv ℝ f) (T x) v v) := by
  have hcrit := critical_of_critical_comp (hf.differentiableAt (by norm_num))
    (hT.differentiableAt (by norm_num)) hb.2 hc
  rw [critical_hessian_comp hf hT hcrit]
  constructor
  · intro h v hv
    obtain ⟨u,hu⟩ := hb.2 v
    have hu0 : u≠0 := by intro hu0;rw [hu0,map_zero] at hu;exact hv hu.symm
    simpa only [ContinuousLinearMap.bilinearComp_apply,hu] using h u hu0
  · intro h u hu
    have hv : fderiv ℝ T x u≠0 := by
      intro hz
      have h0 : fderiv ℝ T x u=fderiv ℝ T x 0 := by simpa using hz
      exact hu (hb.1 h0)
    exact h _ hv

end DepthPaper
