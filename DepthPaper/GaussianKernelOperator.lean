module

public import DepthPaper.TerminalKernel
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section


/-! A genuine Gaussian averaging operator from bounded displacement/space
kernels to bounded spatial functions. Its norm is at most one. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace DepthPaper

theorem integrable_gaussianKernel_section (v : ℝ≥0) (f : (ℝ×ℝ) →ᵇ ℝ) (x : ℝ) :
    Integrable (fun d=>f (d,x)) (gaussianReal 0 v) :=
  (integrable_const ‖f‖).mono'
    (f.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    (.of_forall fun d=>f.norm_coe_le_norm (d,x))

theorem norm_gaussianKernel_integral_le (v : ℝ≥0) (f : (ℝ×ℝ) →ᵇ ℝ) (x : ℝ) :
    ‖∫d,f (d,x) ∂gaussianReal 0 v‖≤‖f‖ := by
  simpa using norm_integral_le_of_norm_le_const
    (μ:=gaussianReal 0 v) (.of_forall fun d=>f.norm_coe_le_norm (d,x))

theorem continuous_gaussianKernel_integral (v : ℝ≥0) (f : (ℝ×ℝ) →ᵇ ℝ) :
    Continuous (fun x:ℝ=>∫d,f (d,x) ∂gaussianReal 0 v) := by
  apply continuous_of_dominated (bound:=fun _=>‖f‖)
  · intro x
    exact (f.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · intro x
    exact .of_forall fun d=>f.norm_coe_le_norm (d,x)
  · exact integrable_const _
  · exact .of_forall fun d=>f.continuous.comp (continuous_const.prodMk continuous_id)

def gaussianKernelAverage (v : ℝ≥0) (f : (ℝ×ℝ) →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x=>∫d,f (d,x) ∂gaussianReal 0 v)
    (continuous_gaussianKernel_integral v f) ‖f‖ (norm_gaussianKernel_integral_le v f)

@[simp] theorem gaussianKernelAverage_apply (v : ℝ≥0) (f : (ℝ×ℝ) →ᵇ ℝ) (x : ℝ) :
    gaussianKernelAverage v f x=∫d,f (d,x) ∂gaussianReal 0 v := rfl

theorem norm_gaussianKernelAverage_le (v : ℝ≥0) (f : (ℝ×ℝ) →ᵇ ℝ) :
    ‖gaussianKernelAverage v f‖≤‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr (norm_gaussianKernel_integral_le v f)

def gaussianKernelAverageCLM (v : ℝ≥0) : ((ℝ×ℝ) →ᵇ ℝ)→L[ℝ](ℝ →ᵇ ℝ) :=
  LinearMap.mkContinuous
    {toFun:=gaussianKernelAverage v
     map_add':=fun f g=>by
       ext x
       exact integral_add (integrable_gaussianKernel_section v f x)
         (integrable_gaussianKernel_section v g x)
     map_smul':=fun c f=>by
       ext x
       exact integral_const_mul c (fun d=>f (d,x))}
    1 (fun f=>by
      convert! norm_gaussianKernelAverage_le v f using 1
      simp only [one_mul])

@[simp] theorem gaussianKernelAverageCLM_apply (v : ℝ≥0) (f : (ℝ×ℝ) →ᵇ ℝ) :
    gaussianKernelAverageCLM v f=gaussianKernelAverage v f := rfl

theorem norm_gaussianKernelAverageCLM_le (v : ℝ≥0) : ‖gaussianKernelAverageCLM v‖≤1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def centeredKernelNormalizer (v : ℝ≥0) (p : TerminalParameter) : ℝ →ᵇ ℝ :=
  gaussianKernelAverage v (weightedTerminalKernel p)

theorem analyticAt_centeredKernelNormalizer (v : ℝ≥0) (p : TerminalParameter)
    (hp : 0<p.1) : AnalyticAt ℝ (centeredKernelNormalizer v) p := by
  exact ((gaussianKernelAverageCLM v).analyticAt (weightedTerminalKernel p)).comp
    (analyticAt_weightedTerminalKernel p hp)

end DepthPaper
