module

public import GeneralDepthPaper.GaussianNormalizerRegularity
public import GeneralDepthPaper.ColeHopfMassRegularity

@[expose] public section


/-! A genuine uniform lower bound for the centered normalizer. It makes the
normalizer a unit of the bounded-function Banach algebra, so normalization is
an analytic operation, including at zero mass. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 32
open ColeHopfFoundation.ProbabilityTheory

theorem integrable_centeredGaussianExponential (a : ℝ) (g : TerminalSpace)
    (v : ℝ≥0) (x : ℝ) :
    Integrable (fun d=>Real.exp (a*(terminalValue g (x+d)-terminalValue g x)))
      (gaussianReal 0 v) := by
  have hi := (integrable_exp_mul_comp_add (hasLinearGrowth_terminalValue g)
    (contDiff_terminalValue g).continuous.measurable a v x).const_mul
    (Real.exp (-a*terminalValue g x))
  apply hi.congr
  exact .of_forall fun d=>by
    dsimp only
    rw [←Real.exp_add]
    congr 1
    ring

def gaussianNormalizerLower (p : ColeHopfParameter) : ℝ :=
  ∫d,Real.exp (-‖p.1.1‖*‖p.2‖*‖d‖) ∂gaussianReal 0 p.1.2.toNNReal

theorem integrable_gaussianNormalizerLower (p : ColeHopfParameter) :
    Integrable (fun d=>Real.exp (-‖p.1.1‖*‖p.2‖*‖d‖))
      (gaussianReal 0 p.1.2.toNNReal) := by
  apply (integrable_const (μ:=gaussianReal 0 p.1.2.toNNReal) (1:ℝ)).mono'
  · exact (Real.continuous_exp.comp
      ((continuous_const.mul continuous_const).mul continuous_norm)).aestronglyMeasurable
  · exact .of_forall fun d=>by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_one_iff.mpr
      have := mul_nonneg (mul_nonneg (norm_nonneg p.1.1) (norm_nonneg p.2)) (norm_nonneg d)
      nlinarith

theorem gaussianNormalizerLower_pos (p : ColeHopfParameter) : 0<gaussianNormalizerLower p :=
  integral_exp_pos (integrable_gaussianNormalizerLower p)

theorem gaussianNormalizerLower_le (p : ColeHopfParameter) (hv : 0<p.1.2) (x : ℝ) :
    gaussianNormalizerLower p≤centeredGaussianNormalizer p x := by
  rw [centeredGaussianNormalizer_apply p hv]
  apply integral_mono (integrable_gaussianNormalizerLower p)
    (integrable_centeredGaussianExponential p.1.1 p.2 p.1.2.toNNReal x)
  intro d
  apply Real.exp_le_exp.mpr
  have hd := norm_terminalValue_sub_le p.2 x (x+d)
  simp only [add_sub_cancel_left] at hd
  have hn : ‖p.1.1*(terminalValue p.2 (x+d)-terminalValue p.2 x)‖≤
      ‖p.1.1‖*‖p.2‖*‖d‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hd (norm_nonneg _)).trans
      (by
        have h := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (norm_terminalJet_le p.2 0) (norm_nonneg d))
          (norm_nonneg p.1.1)
        simpa only [mul_assoc] using h)
  have hh : -‖p.1.1‖*‖p.2‖*‖d‖≤-‖p.1.1*(terminalValue p.2 (x+d)-terminalValue p.2 x)‖ := by
    simpa only [neg_mul] using neg_le_neg hn
  exact hh.trans (by
    simpa only [Real.norm_eq_abs] using
      (neg_abs_le (p.1.1*(terminalValue p.2 (x+d)-terminalValue p.2 x))))

def inversePositiveBCF {S : Type*} [TopologicalSpace S] (f : S →ᵇ ℝ) (δ : ℝ) (hδ : 0<δ) (hb : ∀x,δ≤f x) : S →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x=>(f x)⁻¹)
    (f.continuous.inv₀ (fun x=>(hδ.trans_le (hb x)).ne')) (δ⁻¹) (fun x=>by
      rw [Real.norm_of_nonneg (inv_nonneg.mpr (hδ.trans_le (hb x)).le)]
      exact (inv_le_inv₀ (hδ.trans_le (hb x)) hδ).mpr (hb x))

theorem isUnit_centeredGaussianNormalizer (p : ColeHopfParameter) (hv : 0<p.1.2) :
    IsUnit (centeredGaussianNormalizer p) := by
  let f := centeredGaussianNormalizer p
  let δ := gaussianNormalizerLower p
  have hd : 0<δ := gaussianNormalizerLower_pos p
  have hb : ∀x,δ≤f x := gaussianNormalizerLower_le p hv
  refine ⟨⟨f,inversePositiveBCF f δ hd hb,?_,?_⟩,rfl⟩
  · ext x
    exact mul_inv_cancel₀ (hd.trans_le (hb x)).ne'
  · ext x
    exact inv_mul_cancel₀ (hd.trans_le (hb x)).ne'

theorem analyticAt_inverse_centeredGaussianNormalizer (p : ColeHopfParameter)
    (hv : 0<p.1.2) : AnalyticAt ℝ (fun q=>Ring.inverse (centeredGaussianNormalizer q)) p := by
  have hh : AnalyticAt ℝ Ring.inverse (centeredGaussianNormalizer p) := by
    simpa using analyticAt_inverse (𝕜:=ℝ) (IsUnit.unit (isUnit_centeredGaussianNormalizer p hv))
  exact hh.comp (f:=centeredGaussianNormalizer) (analyticAt_centeredGaussianNormalizer p hv)

end GeneralDepthPaper
