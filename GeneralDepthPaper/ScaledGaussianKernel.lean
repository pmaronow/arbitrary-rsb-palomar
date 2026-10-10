module

public import GeneralDepthPaper.GaussianTiltedUniform
public import GeneralDepthPaper.TerminalReconstruction
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section


/-! Gaussian kernels parameterized by their standard deviation. Unlike a
precision chart, this parameterization includes variance zero. The estimates
hold in the supremum norm, including for uniformly continuous highest jets. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
open ColeHopfFoundation.ProbabilityTheory

theorem bcfSpatialTranslate_norm_le (a : ℝ) (G : ℝ →ᵇ ℝ) :
    ‖bcfSpatialTranslate a G‖ ≤ ‖G‖ :=
  BoundedContinuousFunction.norm_compContinuous_le _ _

theorem continuousAt_bcfSpatialTranslate_pair (a : ℝ) (G : ℝ →ᵇ ℝ)
    (hG : UniformContinuous G) :
    ContinuousAt (fun p : ℝ × (ℝ →ᵇ ℝ) => bcfSpatialTranslate p.1 p.2) (a,G) := by
  have hsmall : Tendsto (fun p : ℝ × (ℝ →ᵇ ℝ) =>
      bcfSpatialTranslate p.1 (p.2-G)) (𝓝 (a,G)) (𝓝 0) := by
    have h : Continuous (fun p : ℝ × (ℝ →ᵇ ℝ) => ‖p.2-G‖) :=
      (continuous_snd.sub continuous_const).norm
    have ht : Tendsto (fun p : ℝ × (ℝ →ᵇ ℝ) => ‖p.2-G‖) (𝓝 (a,G)) (𝓝 0) := by
      simpa only [sub_self,norm_zero] using h.tendsto (a,G)
    exact squeeze_zero_norm (f := fun p : ℝ × (ℝ →ᵇ ℝ) =>
      bcfSpatialTranslate p.1 (p.2-G))
      (fun p => bcfSpatialTranslate_norm_le p.1 (p.2-G)) ht
  have hfixed : ContinuousAt (fun p : ℝ × (ℝ →ᵇ ℝ) =>
      bcfSpatialTranslate p.1 G) (a,G) :=
    (continuous_bcfSpatialTranslate G hG).continuousAt.comp
      (continuous_fst : Continuous (fun p : ℝ × (ℝ →ᵇ ℝ) => p.1)).continuousAt
  change Tendsto (fun p : ℝ × (ℝ →ᵇ ℝ) => bcfSpatialTranslate p.1 p.2)
    (𝓝 (a,G)) (𝓝 (bcfSpatialTranslate a G))
  convert! hsmall.add hfixed.tendsto using 1
  · funext p
    ext x
    simp only [bcfSpatialTranslate_apply,BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.sub_apply]
    ring
  · simp

theorem bcf_exp_apply (f : ℝ →ᵇ ℝ) (x : ℝ) :
    NormedSpace.exp f x = Real.exp (f x) := by
  let ev : (ℝ →ᵇ ℝ) →+* ℝ :=
    { toFun := fun F => F x
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (NormedSpace.exp f) = Real.exp (ev f)
  rw [NormedSpace.map_exp ev (BoundedContinuousFunction.evalCLM ℝ x).continuous,
    Real.exp_eq_exp_ℝ]

def scaledGaussianKernel (p : ColeHopfParameter) (z : ℝ) : ℝ →ᵇ ℝ :=
  NormedSpace.exp (p.1.1 • terminalIncrement (p.1.2*z) p.2)

@[simp] theorem scaledGaussianKernel_apply (p : ColeHopfParameter) (z x : ℝ) :
    scaledGaussianKernel p z x =
      Real.exp (p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x)) := by
  simp only [scaledGaussianKernel,bcf_exp_apply,BoundedContinuousFunction.smul_apply,
    smul_eq_mul,terminalIncrement_apply]

theorem continuous_scaledGaussianKernel_parameter (z : ℝ) :
    Continuous (fun p : ColeHopfParameter => scaledGaussianKernel p z) := by
  unfold scaledGaussianKernel
  apply NormedSpace.exp_continuous.comp
  have hinc : Continuous (fun p : ColeHopfParameter =>
      terminalIncrement (p.1.2*z) p.2) :=
    (lipschitzWith_terminalIncrementCLM.continuous.comp
      ((continuous_snd.comp continuous_fst).mul continuous_const)).clm_apply continuous_snd
  exact (continuous_fst.comp continuous_fst).smul hinc

theorem continuous_scaledGaussianKernel_displacement (p : ColeHopfParameter) :
    Continuous (scaledGaussianKernel p) := by
  unfold scaledGaussianKernel
  have hi : Continuous (fun z : ℝ => terminalIncrement (p.1.2*z) p.2) :=
    (lipschitzWith_terminalIncrementCLM.continuous.comp
      ((continuous_const : Continuous (fun _ : ℝ => p.1.2)).mul continuous_id)).clm_apply
        (continuous_const : Continuous (fun _ : ℝ => p.2))
  exact NormedSpace.exp_continuous.comp
    ((continuous_const : Continuous (fun _ : ℝ => p.1.1)).smul hi)

theorem norm_scaledGaussianKernel_le (p : ColeHopfParameter) (z : ℝ) :
    ‖scaledGaussianKernel p z‖ ≤ Real.exp (‖p.1.1‖*‖p.1.2‖*‖p.2‖*‖z‖) := by
  apply (BoundedContinuousFunction.norm_le (Real.exp_pos _).le).mpr
  intro x
  rw [scaledGaussianKernel_apply,Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  calc
    p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x)
      ≤ ‖p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x)‖ := le_abs_self _
    _ ≤ ‖p.1.1‖*(‖p.1.2*z‖*‖p.2‖) := by
      rw [norm_mul]
      gcongr
      exact (BoundedContinuousFunction.norm_coe_le_norm (terminalIncrement (p.1.2*z) p.2) x).trans
        (norm_terminalIncrement_le _ _)
    _ = ‖p.1.1‖*‖p.1.2‖*‖p.2‖*‖z‖ := by rw [norm_mul]; ring

theorem integrable_scaledGaussianKernel (p : ColeHopfParameter) :
    Integrable (scaledGaussianKernel p) (gaussianReal 0 1) := by
  apply (integrable_exp_mul_abs_gaussianReal 0 1
    (‖p.1.1‖*‖p.1.2‖*‖p.2‖)).mono'
    (continuous_scaledGaussianKernel_displacement p).aestronglyMeasurable
  exact .of_forall fun z => by
    simpa only [Real.norm_eq_abs] using norm_scaledGaussianKernel_le p z

def scaledGaussianNormalizer (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  ∫ z,scaledGaussianKernel p z ∂gaussianReal 0 1

theorem continuous_scaledGaussianNormalizer : Continuous scaledGaussianNormalizer := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let R := ‖p‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  apply continuousAt_of_dominated (bound := fun z => Real.exp (R^3*‖z‖))
  · exact .of_forall fun q => (continuous_scaledGaussianKernel_displacement q).aestronglyMeasurable
  · have hloc : ∀ᶠ q in 𝓝 p, ‖q‖ < R :=
      (continuous_norm.tendsto p) (Iio_mem_nhds (by dsimp [R]; linarith))
    exact hloc.mono fun q hq => .of_forall fun z =>
      (norm_scaledGaussianKernel_le q z).trans (Real.exp_le_exp.mpr (by
        have ha : ‖q.1.1‖ ≤ R := (norm_fst_le q.1).trans ((norm_fst_le q).trans hq.le)
        have hs : ‖q.1.2‖ ≤ R := (norm_snd_le q.1).trans ((norm_fst_le q).trans hq.le)
        have hg : ‖q.2‖ ≤ R := (norm_snd_le q).trans hq.le
        calc
          ‖q.1.1‖*‖q.1.2‖*‖q.2‖*‖z‖ ≤ R*R*R*‖z‖ := by gcongr
          _ = R^3*‖z‖ := by ring))
  · simpa only [Real.norm_eq_abs] using integrable_exp_mul_abs_gaussianReal 0 1 (R^3)
  · exact .of_forall fun z => (continuous_scaledGaussianKernel_parameter z).continuousAt

@[simp] theorem scaledGaussianNormalizer_zero (a : ℝ) (g : TerminalSpace) :
    scaledGaussianNormalizer ((a,0),g) = 1 := by
  have he : scaledGaussianKernel ((a,0),g) = fun _ => (1 : ℝ →ᵇ ℝ) := by
    funext z
    ext x
    simp [scaledGaussianKernel_apply]
  rw [scaledGaussianNormalizer,he]
  simp

end GeneralDepthPaper
