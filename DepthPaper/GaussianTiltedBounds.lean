module

public import DepthPaper.GaussianTiltedOperator

@[expose] public section


/-! Positivity and norm contraction of the actual normalized Gaussian tilt. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace DepthPaper
set_option maxSynthPendingDepth 32

theorem integrable_tiltedGaussianNumerator (p : TiltedParameter) (x : ℝ) :
    Integrable (fun d=>Real.exp (p.1.1.1*(terminalValue p.1.2 (x+d)-terminalValue p.1.2 x))*p.2 (d,x))
      (gaussianReal 0 p.1.1.2.toNNReal) :=
  (integrable_centeredGaussianExponential p.1.1.1 p.1.2 p.1.1.2.toNNReal x).mul_bdd
    (p.2.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    (.of_forall fun d=>p.2.norm_coe_le_norm (d,x))

theorem norm_tiltedGaussianOperator_apply_le (p : TiltedParameter) (hv : 0<p.1.1.2) (x : ℝ) :
    ‖tiltedGaussianOperator p x‖≤‖p.2‖ := by
  let E : ℝ→ℝ := fun d=>Real.exp (p.1.1.1*(terminalValue p.1.2 (x+d)-terminalValue p.1.2 x))
  let γ := gaussianReal 0 p.1.1.2.toNNReal
  have hE : Integrable E γ := integrable_centeredGaussianExponential _ _ _ _
  have hnum : Integrable (fun d=>E d*p.2 (d,x)) γ := integrable_tiltedGaussianNumerator p x
  have hpos : 0<∫d,E d ∂γ := integral_exp_pos hE
  rw [tiltedGaussianOperator_apply p hv x,norm_div,Real.norm_of_nonneg hpos.le]
  apply (div_le_iff₀ hpos).mpr
  calc
    ‖∫d,E d*p.2 (d,x) ∂γ‖≤∫d,‖E d*p.2 (d,x)‖ ∂γ := norm_integral_le_integral_norm _
    _≤∫d,‖p.2‖*E d ∂γ := by
      apply integral_mono hnum.norm (hE.const_mul ‖p.2‖)
      intro d
      dsimp only
      rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
      exact (mul_le_mul_of_nonneg_left (p.2.norm_coe_le_norm (d,x)) (Real.exp_pos _).le).trans_eq
        (mul_comm _ _)
    _=‖p.2‖*(∫d,E d ∂γ) := integral_const_mul _ _

theorem norm_tiltedGaussianOperator_le (p : TiltedParameter) (hv : 0<p.1.1.2) :
    ‖tiltedGaussianOperator p‖≤‖p.2‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg p.2)).mpr (norm_tiltedGaussianOperator_apply_le p hv)

@[simp] theorem centeredGaussianNormalizer_mass_zero (v : ℝ) (g : TerminalSpace) (hv : 0<v) :
    centeredGaussianNormalizer ((0,v),g)=1 := by
  ext x
  rw [centeredGaussianNormalizer_apply _ hv]
  simp

theorem tiltedGaussianOperator_mass_zero (v : ℝ) (g : TerminalSpace) (hv : 0<v)
    (H : GaussianObservable) :
    tiltedGaussianOperator (((0,v),g),H)=gaussianKernelAverage v.toNNReal H := by
  ext x
  rw [tiltedGaussianOperator_apply _ hv]
  simp

end DepthPaper
