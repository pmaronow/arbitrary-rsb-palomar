module

public import DepthPaper.GaussianKernelOperator

@[expose] public section


/-! Exact Gaussian change of precision for centered terminal kernels. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace DepthPaper

def gaussianPrecisionDifference (v w : ℝ) : ℝ := 1/(2*v)-1/(2*w)

theorem gaussianPrecisionDifference_pos {v w : ℝ} (hv : 0<v) (hvw : v<w) :
    0<gaussianPrecisionDifference v w := by
  unfold gaussianPrecisionDifference
  exact sub_pos.mpr (one_div_lt_one_div_of_lt (by positivity) (by linarith))

theorem gaussianPDFReal_precision_ratio (v w : ℝ≥0) (hv : 0<v) (hw : 0<w) (d : ℝ) :
    gaussianPDFReal 0 v d=
      (Real.sqrt (2*Real.pi*(w:ℝ))/Real.sqrt (2*Real.pi*(v:ℝ)))*
      gaussianPDFReal 0 w d*Real.exp (-gaussianPrecisionDifference v w*d^2) := by
  have hsv : Real.sqrt (2*Real.pi*(v:ℝ))≠0 := by apply ne_of_gt; positivity
  have hsw : Real.sqrt (2*Real.pi*(w:ℝ))≠0 := by apply ne_of_gt; positivity
  unfold gaussianPDFReal gaussianPrecisionDifference
  simp only [sub_zero,mul_assoc]
  simp only [←mul_assoc]
  have hcoeff : Real.sqrt (2*Real.pi*(w:ℝ))/Real.sqrt (2*Real.pi*(v:ℝ))*
      (Real.sqrt (2*Real.pi*(w:ℝ)))⁻¹=(Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹ := by
    field_simp
  rw [hcoeff]
  simp only [mul_assoc]
  rw [←Real.exp_add]
  have he : -d^2/(2*(w:ℝ)) + -(1/(2*(v:ℝ))-1/(2*(w:ℝ)))*d^2=
      -d^2/(2*(v:ℝ)) := by field_simp; ring
  rw [he]

/-- Exact precision substitution for every Gaussian integral. -/
theorem gaussianPrecision_integral (v w : ℝ≥0) (hv : 0<v) (hw : 0<w) (F : ℝ→ℝ) :
    (∫d,F d ∂gaussianReal 0 v)=
      (Real.sqrt (2*Real.pi*(w:ℝ))/Real.sqrt (2*Real.pi*(v:ℝ)))*
        ∫d,Real.exp (-gaussianPrecisionDifference v w*d^2)*F d ∂gaussianReal 0 w := by
  rw [integral_gaussianReal_eq_integral_smul hv.ne',
    integral_gaussianReal_eq_integral_smul hw.ne',←integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun d=>by
    dsimp only
    simp only [smul_eq_mul]
    rw [gaussianPDFReal_precision_ratio v w hv hw]
    ring

/-- The BCF-valued kernel formula is exactly the original centered Gaussian
normalizer for every positive variance smaller than the reference variance. -/
theorem centeredGaussianNormalizer_eq_kernel (a : ℝ) (g : TerminalSpace)
    (v w : ℝ≥0) (hv : 0<v) (hvw : v<w) (x : ℝ) :
    (∫d,Real.exp (a*(terminalValue g (x+d)-terminalValue g x)) ∂gaussianReal 0 v)=
      (Real.sqrt (2*Real.pi*(w:ℝ))/Real.sqrt (2*Real.pi*(v:ℝ)))*
      centeredKernelNormalizer w (gaussianPrecisionDifference v w,a•g) x := by
  have hw : 0<w := hv.trans hvw
  have hb : 0<gaussianPrecisionDifference v w := gaussianPrecisionDifference_pos hv hvw
  change _=_*(∫d,weightedTerminalKernel (gaussianPrecisionDifference v w,a•g) (d,x) ∂gaussianReal 0 w)
  rw [integral_gaussianReal_eq_integral_smul hv.ne',integral_gaussianReal_eq_integral_smul hw.ne',
    ←integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun d=>by
    dsimp only
    simp only [smul_eq_mul]
    rw [weightedTerminalKernel_apply _ hb]
    rw [gaussianPDFReal_precision_ratio v w hv hw]
    simp only [terminalValue_smul,smul_eq_mul]
    simp only [mul_assoc]
    rw [←Real.exp_add]
    have he : -(gaussianPrecisionDifference v w)*d^2+
        a*(terminalValue g (x+d)-terminalValue g x)=
        terminalValue (a•g) (x+d)-terminalValue (a•g) x-
          gaussianPrecisionDifference v w*d^2 := by simp only [terminalValue_smul]; ring
    rw [he]
    simp only [terminalValue_smul]

end DepthPaper
