module

public import DepthPaper.ScaledGaussianKernel

@[expose] public section


/-! Normalized Gaussian averages remain continuous in the terminal Banach
norm at zero variance. Uniform continuity is required only of the bounded
observable; it is part of the terminal space's highest-jet condition. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace DepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
open ColeHopfFoundation.ProbabilityTheory

theorem scaledGaussianNormalizer_apply (p : ColeHopfParameter) (x : ℝ) :
    scaledGaussianNormalizer p x = ∫z,
      Real.exp (p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x))
        ∂gaussianReal 0 1 := by
  change (BoundedContinuousFunction.evalCLM ℝ x)
    (∫z,scaledGaussianKernel p z ∂gaussianReal 0 1) = _
  rw [←ContinuousLinearMap.integral_comp_comm _ (integrable_scaledGaussianKernel p)]
  simp only [BoundedContinuousFunction.evalCLM_apply,scaledGaussianKernel_apply]

def scaledGaussianLower (c : ℝ) : ℝ :=
  ∫z,Real.exp (-c*‖z‖) ∂gaussianReal 0 1

theorem integrable_scaledGaussianLower (c : ℝ) :
    Integrable (fun z => Real.exp (-c*‖z‖)) (gaussianReal 0 1) := by
  simpa only [Real.norm_eq_abs] using integrable_exp_mul_abs_gaussianReal 0 1 (-c)

theorem scaledGaussianLower_pos (c : ℝ) : 0 < scaledGaussianLower c :=
  integral_exp_pos (integrable_scaledGaussianLower c)

theorem scaledGaussianLower_le (p : ColeHopfParameter) (c : ℝ)
    (hc : ‖p.1.1‖*‖p.1.2‖*‖p.2‖ ≤ c) (x : ℝ) :
    scaledGaussianLower c ≤ scaledGaussianNormalizer p x := by
  rw [scaledGaussianNormalizer_apply]
  have hi : Integrable (fun z =>
      Real.exp (p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x)))
      (gaussianReal 0 1) := by
    simpa only [BoundedContinuousFunction.evalCLM_apply,scaledGaussianKernel_apply] using
      ((BoundedContinuousFunction.evalCLM ℝ x).integrable_comp (integrable_scaledGaussianKernel p))
  change (∫z,Real.exp (-c*‖z‖) ∂gaussianReal 0 1) ≤ _
  apply integral_mono (integrable_scaledGaussianLower c) hi
  intro z
  apply Real.exp_le_exp.mpr
  have hi := norm_terminalValue_sub_le p.2 x (x+p.1.2*z)
  simp only [add_sub_cancel_left] at hi
  have hnorm : ‖p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x)‖ ≤ c*‖z‖ := by
    rw [norm_mul]
    calc
      ‖p.1.1‖*‖terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x‖
        ≤ ‖p.1.1‖*(‖p.2‖*‖p.1.2*z‖) := by
          gcongr
          exact hi.trans (mul_le_mul_of_nonneg_right (norm_terminalJet_le p.2 0) (norm_nonneg _))
      _ = (‖p.1.1‖*‖p.1.2‖*‖p.2‖)*‖z‖ := by rw [norm_mul]; ring
      _ ≤ c*‖z‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  calc
    -c*‖z‖ ≤ -‖p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x)‖ := by
      simpa only [neg_mul] using neg_le_neg hnorm
    _ ≤ p.1.1*(terminalValue p.2 (x+p.1.2*z)-terminalValue p.2 x) := neg_abs_le _

theorem isUnit_scaledGaussianNormalizer (p : ColeHopfParameter) :
    IsUnit (scaledGaussianNormalizer p) := by
  let c := ‖p.1.1‖*‖p.1.2‖*‖p.2‖
  have hd := scaledGaussianLower_pos c
  have hb := scaledGaussianLower_le p c le_rfl
  refine ⟨⟨scaledGaussianNormalizer p,
    inversePositiveBCF (scaledGaussianNormalizer p) (scaledGaussianLower c) hd hb,?_,?_⟩,rfl⟩
  · ext x
    exact mul_inv_cancel₀ (hd.trans_le (hb x)).ne'
  · ext x
    exact inv_mul_cancel₀ (hd.trans_le (hb x)).ne'

theorem continuous_inverse_scaledGaussianNormalizer :
    Continuous (fun p => Ring.inverse (scaledGaussianNormalizer p)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hi : ContinuousAt Ring.inverse (scaledGaussianNormalizer p) := by
    simpa using (analyticAt_inverse (𝕜:=ℝ)
      (IsUnit.unit (isUnit_scaledGaussianNormalizer p))).continuousAt
  exact hi.comp continuous_scaledGaussianNormalizer.continuousAt

theorem inverse_scaledGaussianNormalizer_apply (p : ColeHopfParameter) (x : ℝ) :
    Ring.inverse (scaledGaussianNormalizer p) x = (scaledGaussianNormalizer p x)⁻¹ := by
  have hmul := Ring.mul_inverse_cancel (scaledGaussianNormalizer p)
    (isUnit_scaledGaussianNormalizer p)
  have hx := congrArg (fun f : ℝ →ᵇ ℝ => f x) hmul
  change scaledGaussianNormalizer p x * Ring.inverse (scaledGaussianNormalizer p) x = 1 at hx
  have hn : scaledGaussianNormalizer p x ≠ 0 :=
    ((scaledGaussianLower_pos _).trans_le (scaledGaussianLower_le p _ le_rfl x)).ne'
  apply mul_left_cancel₀ hn
  rw [mul_inv_cancel₀ hn]
  exact hx

def scaledGaussianTiltNumerator (H : ColeHopfParameter → ℝ →ᵇ ℝ)
    (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  ∫z,scaledGaussianKernel p z * bcfSpatialTranslate (p.1.2*z) (H p) ∂gaussianReal 0 1

theorem integrable_scaledGaussianTiltNumerator (H : ColeHopfParameter → ℝ →ᵇ ℝ)
    (p : ColeHopfParameter) (hU : UniformContinuous (H p)) :
    Integrable (fun z => scaledGaussianKernel p z * bcfSpatialTranslate (p.1.2*z) (H p))
      (gaussianReal 0 1) := by
  apply ((integrable_exp_mul_abs_gaussianReal 0 1
    (‖p.1.1‖*‖p.1.2‖*‖p.2‖)).mul_const ‖H p‖).mono'
  · exact ((continuous_scaledGaussianKernel_displacement p).mul
      ((continuous_bcfSpatialTranslate (H p) hU).comp
        ((continuous_const : Continuous (fun _ : ℝ => p.1.2)).mul continuous_id))).aestronglyMeasurable
  · exact .of_forall fun z =>
      (norm_mul_le _ _).trans (mul_le_mul (norm_scaledGaussianKernel_le p z)
        (bcfSpatialTranslate_norm_le _ _) (norm_nonneg _) (Real.exp_pos _).le)

theorem continuousAt_scaledGaussianTiltNumerator (H : ColeHopfParameter → ℝ →ᵇ ℝ)
    (hU : ∀p,UniformContinuous (H p)) (p : ColeHopfParameter)
    (hH : ContinuousAt H p) : ContinuousAt (scaledGaussianTiltNumerator H) p := by
  let R := ‖p‖+1
  let B := ‖H p‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  apply continuousAt_of_dominated (bound := fun z => Real.exp (R^3*‖z‖)*B)
  · exact .of_forall fun q => (integrable_scaledGaussianTiltNumerator H q (hU q)).aestronglyMeasurable
  · have hq : ∀ᶠ q in 𝓝 p, ‖q‖ < R :=
      continuous_norm.continuousAt (Iio_mem_nhds (by dsimp [R]; linarith))
    have hG : ∀ᶠ q in 𝓝 p, ‖H q‖ < B :=
      hH.norm (Iio_mem_nhds (by dsimp [B]; linarith))
    filter_upwards [hq,hG] with q hq hG
    exact .of_forall fun z => (norm_mul_le _ _).trans (mul_le_mul
      ((norm_scaledGaussianKernel_le q z).trans (Real.exp_le_exp.mpr (by
        have ha : ‖q.1.1‖ ≤ R := (norm_fst_le q.1).trans ((norm_fst_le q).trans hq.le)
        have hs : ‖q.1.2‖ ≤ R := (norm_snd_le q.1).trans ((norm_fst_le q).trans hq.le)
        have hg : ‖q.2‖ ≤ R := (norm_snd_le q).trans hq.le
        calc
          ‖q.1.1‖*‖q.1.2‖*‖q.2‖*‖z‖ ≤ R*R*R*‖z‖ := by gcongr
          _ = R^3*‖z‖ := by ring)))
      ((bcfSpatialTranslate_norm_le _ _).trans hG.le) (norm_nonneg _) (Real.exp_pos _).le)
  · simpa only [Real.norm_eq_abs] using
      (integrable_exp_mul_abs_gaussianReal 0 1 (R^3)).mul_const B
  · refine .of_forall fun z => ?_
    have ht : ContinuousAt (fun q : ColeHopfParameter => (q.1.2*z,H q)) p :=
      (((continuous_snd.comp continuous_fst).continuousAt.mul
        (continuousAt_const : ContinuousAt (fun _ : ColeHopfParameter => z) p)).prodMk hH)
    have htr : ContinuousAt (fun q : ColeHopfParameter =>
        bcfSpatialTranslate (q.1.2*z) (H q)) p :=
      (continuousAt_bcfSpatialTranslate_pair (p.1.2*z) (H p) (hU p)).comp
        (f := fun q : ColeHopfParameter => (q.1.2*z,H q)) ht
    exact (continuous_scaledGaussianKernel_parameter z).continuousAt.mul htr

def scaledGaussianTiltMean (H : ColeHopfParameter → ℝ →ᵇ ℝ)
    (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  Ring.inverse (scaledGaussianNormalizer p) * scaledGaussianTiltNumerator H p

theorem continuousAt_scaledGaussianTiltMean (H : ColeHopfParameter → ℝ →ᵇ ℝ)
    (hU : ∀p,UniformContinuous (H p)) (p : ColeHopfParameter) (hH : ContinuousAt H p) :
    ContinuousAt (scaledGaussianTiltMean H) p :=
  continuous_inverse_scaledGaussianNormalizer.continuousAt.mul
    (continuousAt_scaledGaussianTiltNumerator H hU p hH)

@[simp] theorem scaledGaussianTiltNumerator_zero (H : ColeHopfParameter → ℝ →ᵇ ℝ)
    (a : ℝ) (g : TerminalSpace) :
    scaledGaussianTiltNumerator H ((a,0),g) = H ((a,0),g) := by
  have he : (fun z => scaledGaussianKernel ((a,0),g) z *
      bcfSpatialTranslate (0*z) (H ((a,0),g))) = fun _ => H ((a,0),g) := by
    funext z
    ext x
    simp [scaledGaussianKernel_apply,bcfSpatialTranslate_apply]
  rw [scaledGaussianTiltNumerator,he]
  simp

@[simp] theorem scaledGaussianTiltMean_zero (H : ColeHopfParameter → ℝ →ᵇ ℝ)
    (a : ℝ) (g : TerminalSpace) : scaledGaussianTiltMean H ((a,0),g) = H ((a,0),g) := by
  rw [scaledGaussianTiltMean,scaledGaussianNormalizer_zero,scaledGaussianTiltNumerator_zero]
  simp

end DepthPaper
