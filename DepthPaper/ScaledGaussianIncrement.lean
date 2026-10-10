module

public import DepthPaper.ScaledGaussianIdentification
public import DepthPaper.CompactIntervalAverage

@[expose] public section


/-! The genuine centered Cole–Hopf value is a continuous bounded-function
valued map at every nonnegative variance, with no division by the mass. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace DepthPaper
set_option maxSynthPendingDepth 64
set_option maxHeartbeats 800000
open ColeHopfFoundation.ProbabilityTheory

theorem norm_le_exp_norm_real (z : ℝ) : ‖z‖ ≤ Real.exp ‖z‖ := by
  have h := Real.add_one_le_exp ‖z‖
  linarith

def scaledGaussianIncrementNumerator (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  ∫z,scaledGaussianKernel p z * terminalIncrement (p.1.2*z) p.2 ∂gaussianReal 0 1

theorem continuous_scaledGaussianIncrement_integrand_displacement (p : ColeHopfParameter) :
    Continuous (fun z : ℝ => scaledGaussianKernel p z * terminalIncrement (p.1.2*z) p.2) := by
  have hi : Continuous (fun z : ℝ => terminalIncrement (p.1.2*z) p.2) :=
    (lipschitzWith_terminalIncrementCLM.continuous.comp
      ((continuous_const : Continuous (fun _ : ℝ => p.1.2)).mul continuous_id)).clm_apply
        (continuous_const : Continuous (fun _ : ℝ => p.2))
  exact (continuous_scaledGaussianKernel_displacement p).mul hi

theorem norm_scaledGaussianIncrement_integrand_le (p : ColeHopfParameter) (z : ℝ) :
    ‖scaledGaussianKernel p z * terminalIncrement (p.1.2*z) p.2‖ ≤
      (‖p.1.2‖*‖p.2‖)*Real.exp ((‖p.1.1‖*‖p.1.2‖*‖p.2‖+1)*‖z‖) := by
  calc
    ‖scaledGaussianKernel p z * terminalIncrement (p.1.2*z) p.2‖
      ≤ Real.exp (‖p.1.1‖*‖p.1.2‖*‖p.2‖*‖z‖)*(‖p.1.2*z‖*‖p.2‖) :=
        (norm_mul_le _ _).trans (mul_le_mul (norm_scaledGaussianKernel_le p z)
          (norm_terminalIncrement_le _ _) (norm_nonneg _) (Real.exp_pos _).le)
    _ ≤ Real.exp (‖p.1.1‖*‖p.1.2‖*‖p.2‖*‖z‖)*
        (‖p.1.2‖*Real.exp ‖z‖*‖p.2‖) := by
          rw [norm_mul]
          gcongr
          exact norm_le_exp_norm_real z
    _ = (‖p.1.2‖*‖p.2‖)*Real.exp ((‖p.1.1‖*‖p.1.2‖*‖p.2‖+1)*‖z‖) := by
      rw [add_mul,one_mul,Real.exp_add]
      ring

theorem integrable_scaledGaussianIncrement_integrand (p : ColeHopfParameter) :
    Integrable (fun z : ℝ => scaledGaussianKernel p z * terminalIncrement (p.1.2*z) p.2)
      (gaussianReal 0 1) := by
  apply ((integrable_exp_mul_abs_gaussianReal 0 1
    (‖p.1.1‖*‖p.1.2‖*‖p.2‖+1)).const_mul (‖p.1.2‖*‖p.2‖)).mono'
      (continuous_scaledGaussianIncrement_integrand_displacement p).aestronglyMeasurable
  exact .of_forall fun z => by
    simpa only [Real.norm_eq_abs] using norm_scaledGaussianIncrement_integrand_le p z

theorem continuous_scaledGaussianIncrementNumerator :
    Continuous scaledGaussianIncrementNumerator := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let R := ‖p‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  apply continuousAt_of_dominated (bound := fun z => R^2*Real.exp ((R^3+1)*‖z‖))
  · exact .of_forall fun q => (integrable_scaledGaussianIncrement_integrand q).aestronglyMeasurable
  · have hloc : ∀ᶠ q in 𝓝 p, ‖q‖ < R :=
      continuous_norm.continuousAt (Iio_mem_nhds (by dsimp [R]; linarith))
    filter_upwards [hloc] with q hq
    exact .of_forall fun z => (norm_scaledGaussianIncrement_integrand_le q z).trans (by
      have ha : ‖q.1.1‖ ≤ R := (norm_fst_le q.1).trans ((norm_fst_le q).trans hq.le)
      have hs : ‖q.1.2‖ ≤ R := (norm_snd_le q.1).trans ((norm_fst_le q).trans hq.le)
      have hg : ‖q.2‖ ≤ R := (norm_snd_le q).trans hq.le
      have hco : ‖q.1.1‖*‖q.1.2‖*‖q.2‖ ≤ R^3 := by
        calc
          ‖q.1.1‖*‖q.1.2‖*‖q.2‖ ≤ R*R*R := by gcongr
          _ = R^3 := by ring
      apply mul_le_mul
      · simpa only [pow_two] using mul_le_mul hs hg (norm_nonneg _) hR
      · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith :
          ‖q.1.1‖*‖q.1.2‖*‖q.2‖+1 ≤ R^3+1) (norm_nonneg _))
      · exact (Real.exp_pos _).le
      · positivity)
  · simpa only [Real.norm_eq_abs] using
      (integrable_exp_mul_abs_gaussianReal 0 1 (R^3+1)).const_mul (R^2)
  · refine .of_forall fun z => ?_
    have hi : Continuous (fun q : ColeHopfParameter => terminalIncrement (q.1.2*z) q.2) :=
      (lipschitzWith_terminalIncrementCLM.continuous.comp
        ((continuous_snd.comp continuous_fst).mul continuous_const)).clm_apply continuous_snd
    exact ((continuous_scaledGaussianKernel_parameter z).mul hi).continuousAt

def scaledGaussianIncrementMean (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  Ring.inverse (scaledGaussianNormalizer p) * scaledGaussianIncrementNumerator p

theorem continuous_scaledGaussianIncrementMean : Continuous scaledGaussianIncrementMean :=
  continuous_inverse_scaledGaussianNormalizer.mul continuous_scaledGaussianIncrementNumerator

@[simp] theorem scaledGaussianIncrementMean_zero (a : ℝ) (g : TerminalSpace) :
    scaledGaussianIncrementMean ((a,0),g) = 0 := by
  have he : (fun z => scaledGaussianKernel ((a,0),g) z * terminalIncrement (0*z) g) =
      fun _ => (0 : ℝ →ᵇ ℝ) := by
    funext z
    ext x
    simp [terminalIncrement_apply]
  rw [scaledGaussianIncrementMean,scaledGaussianIncrementNumerator,he]
  simp

def scaledGaussianCenteredValue (p : ColeHopfParameter) : ℝ →ᵇ ℝ :=
  ∫t in (0:ℝ)..1,scaledGaussianIncrementMean ((t*p.1.1,p.1.2),p.2)

theorem continuous_scaledGaussianCenteredValue : Continuous scaledGaussianCenteredValue := by
  have hc : Continuous (fun pt : ColeHopfParameter × UnitTilt =>
      scaledGaussianIncrementMean (((pt.2:ℝ)*pt.1.1.1,pt.1.1.2),pt.1.2)) :=
    continuous_scaledGaussianIncrementMean.comp (by fun_prop)
  have h := continuous_unitIntervalIntegral _ hc
  convert! h using 1
  funext p
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [projIcc_of_mem zero_le_one (by simpa only [Set.uIcc_of_le zero_le_one] using ht)]

@[simp] theorem scaledGaussianCenteredValue_zero (a : ℝ) (g : TerminalSpace) :
    scaledGaussianCenteredValue ((a,0),g) = 0 := by
  simp [scaledGaussianCenteredValue]

end DepthPaper
