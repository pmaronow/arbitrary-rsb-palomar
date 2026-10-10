module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section


/-! A genuine Gaussian averaging operator from bounded displacement/parameter
kernels to bounded spatial functions. Its norm is at most one. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
variable {S : Type*} [TopologicalSpace S] [FirstCountableTopology S]

theorem integrable_parametricGaussianKernel_section (v : ℝ≥0) (f : (ℝ×S) →ᵇ ℝ) (x : S) :
    Integrable (fun d=>f (d,x)) (gaussianReal 0 v) :=
  (integrable_const ‖f‖).mono'
    (f.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    (.of_forall fun d=>f.norm_coe_le_norm (d,x))

theorem norm_parametricGaussianKernel_integral_le (v : ℝ≥0) (f : (ℝ×S) →ᵇ ℝ) (x : S) :
    ‖∫d,f (d,x) ∂gaussianReal 0 v‖≤‖f‖ := by
  simpa using norm_integral_le_of_norm_le_const
    (μ:=gaussianReal 0 v) (.of_forall fun d=>f.norm_coe_le_norm (d,x))

theorem continuous_parametricGaussianKernel_integral (v : ℝ≥0) (f : (ℝ×S) →ᵇ ℝ) :
    Continuous (fun x:S=>∫d,f (d,x) ∂gaussianReal 0 v) := by
  apply continuous_of_dominated (bound:=fun _=>‖f‖)
  · intro x
    exact (f.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · intro x
    exact .of_forall fun d=>f.norm_coe_le_norm (d,x)
  · exact integrable_const _
  · exact .of_forall fun d=>f.continuous.comp (continuous_const.prodMk continuous_id)

def parametricGaussianKernelAverage (v : ℝ≥0) (f : (ℝ×S) →ᵇ ℝ) : S →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x=>∫d,f (d,x) ∂gaussianReal 0 v)
    (continuous_parametricGaussianKernel_integral v f) ‖f‖ (norm_parametricGaussianKernel_integral_le v f)

@[simp] theorem parametricGaussianKernelAverage_apply (v : ℝ≥0) (f : (ℝ×S) →ᵇ ℝ) (x : S) :
    parametricGaussianKernelAverage v f x=∫d,f (d,x) ∂gaussianReal 0 v := rfl

theorem norm_parametricGaussianKernelAverage_le (v : ℝ≥0) (f : (ℝ×S) →ᵇ ℝ) :
    ‖parametricGaussianKernelAverage v f‖≤‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr (norm_parametricGaussianKernel_integral_le v f)

def parametricGaussianKernelAverageCLM (v : ℝ≥0) : ((ℝ×S) →ᵇ ℝ)→L[ℝ](S →ᵇ ℝ) :=
  LinearMap.mkContinuous
    {toFun:=parametricGaussianKernelAverage v
     map_add':=fun f g=>by
       ext x
       exact integral_add (integrable_parametricGaussianKernel_section v f x)
         (integrable_parametricGaussianKernel_section v g x)
     map_smul':=fun c f=>by
       ext x
       exact integral_const_mul c (fun d=>f (d,x))}
    1 (fun f=>by
      convert! norm_parametricGaussianKernelAverage_le v f using 1
      simp only [one_mul])

@[simp] theorem parametricGaussianKernelAverageCLM_apply (v : ℝ≥0) (f : (ℝ×S) →ᵇ ℝ) :
    parametricGaussianKernelAverageCLM v f=parametricGaussianKernelAverage v f := rfl

theorem norm_parametricGaussianKernelAverageCLM_le (v : ℝ≥0) : ‖parametricGaussianKernelAverageCLM (S:=S) v‖≤1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end GeneralDepthPaper
