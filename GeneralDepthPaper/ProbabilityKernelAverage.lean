module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section


/-! A genuine probability averaging operator from bounded displacement/parameter
kernels to bounded spatial functions. Its norm is at most one. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
variable {S : Type*} [TopologicalSpace S] [FirstCountableTopology S]

theorem integrable_probabilityKernel_section (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : (ℝ×S) →ᵇ ℝ) (x : S) :
    Integrable (fun d=>f (d,x)) μ :=
  (integrable_const ‖f‖).mono'
    (f.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    (.of_forall fun d=>f.norm_coe_le_norm (d,x))

theorem norm_probabilityKernel_integral_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : (ℝ×S) →ᵇ ℝ) (x : S) :
    ‖∫d,f (d,x) ∂μ‖≤‖f‖ := by
  simpa using norm_integral_le_of_norm_le_const
    (μ:=μ) (.of_forall fun d=>f.norm_coe_le_norm (d,x))

theorem continuous_probabilityKernel_integral (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : (ℝ×S) →ᵇ ℝ) :
    Continuous (fun x:S=>∫d,f (d,x) ∂μ) := by
  apply continuous_of_dominated (bound:=fun _=>‖f‖)
  · intro x
    exact (f.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · intro x
    exact .of_forall fun d=>f.norm_coe_le_norm (d,x)
  · exact integrable_const _
  · exact .of_forall fun d=>f.continuous.comp (continuous_const.prodMk continuous_id)

def probabilityKernelAverage (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : (ℝ×S) →ᵇ ℝ) : S →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x=>∫d,f (d,x) ∂μ)
    (continuous_probabilityKernel_integral μ f) ‖f‖ (norm_probabilityKernel_integral_le μ f)

@[simp] theorem probabilityKernelAverage_apply (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : (ℝ×S) →ᵇ ℝ) (x : S) :
    probabilityKernelAverage μ f x=∫d,f (d,x) ∂μ := rfl

theorem norm_probabilityKernelAverage_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : (ℝ×S) →ᵇ ℝ) :
    ‖probabilityKernelAverage μ f‖≤‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr (norm_probabilityKernel_integral_le μ f)

def probabilityKernelAverageCLM (μ : Measure ℝ) [IsProbabilityMeasure μ] : ((ℝ×S) →ᵇ ℝ)→L[ℝ](S →ᵇ ℝ) :=
  LinearMap.mkContinuous
    {toFun:=probabilityKernelAverage μ
     map_add':=fun f g=>by
       ext x
       exact integral_add (integrable_probabilityKernel_section μ f x)
         (integrable_probabilityKernel_section μ g x)
     map_smul':=fun c f=>by
       ext x
       exact integral_const_mul c (fun d=>f (d,x))}
    1 (fun f=>by
      convert! norm_probabilityKernelAverage_le μ f using 1
      simp only [one_mul])

@[simp] theorem probabilityKernelAverageCLM_apply (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : (ℝ×S) →ᵇ ℝ) :
    probabilityKernelAverageCLM μ f=probabilityKernelAverage μ f := rfl

theorem norm_probabilityKernelAverageCLM_le (μ : Measure ℝ) [IsProbabilityMeasure μ] : ‖probabilityKernelAverageCLM (S:=S) μ‖≤1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end GeneralDepthPaper
