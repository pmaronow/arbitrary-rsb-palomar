module

public import GeneralDepthPaper.CompactTiltResponse
public import GeneralDepthPaper.InverseDerivativeBounds

@[expose] public section


/-! A positive lower normalizer bound uniform over a noncompact terminal
ball. It controls the genuine Banach-algebra inverse without dividing by mass. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace GeneralDepthPaper

def compactNormalizerBallLower (w : ℝ≥0) (B R : ℝ) : ℝ :=
  ∫d,Real.exp (-B*‖d‖-R*d^2) ∂gaussianReal 0 w

theorem integrable_compactNormalizerBallLower (w : ℝ≥0) (B R : ℝ)
    (hB : 0≤B) (hR : 0≤R) :
    Integrable (fun d=>Real.exp (-B*‖d‖-R*d^2)) (gaussianReal 0 w) := by
  apply (integrable_const (μ:=gaussianReal 0 w) (1:ℝ)).mono'
  · exact (Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · exact .of_forall fun d=>by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_one_iff.mpr
      nlinarith [mul_nonneg hB (norm_nonneg d),mul_nonneg hR (sq_nonneg d)]

theorem compactNormalizerBallLower_pos (w : ℝ≥0) (B R : ℝ)
    (hB : 0≤B) (hR : 0≤R) : 0<compactNormalizerBallLower w B R :=
  integral_exp_pos (integrable_compactNormalizerBallLower w B R hB hR)

theorem compactNormalizerBallLower_le (w : ℝ≥0) (B R : ℝ)
    (hB : 0≤B) (hR : 0≤R) (p : CompactTiltParameter) (hp : 0<p.1)
    (hpR : p.1≤R) (hg : ‖p.2.1‖+‖p.2.2‖≤B) (s : CompactTiltLocation) :
    compactNormalizerBallLower w B R≤compactTiltNormalizer w p s := by
  refine (integral_mono (integrable_compactNormalizerBallLower w B R hB hR)
    (integrable_compactTiltLower w p hp) ?_).trans (compactTiltLower_le w p hp s)
  intro d
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_right hg (norm_nonneg d)
  have h2 := mul_le_mul_of_nonneg_right hpR (sq_nonneg d)
  linarith

theorem norm_inverse_compactTiltNormalizer_le (w : ℝ≥0) (B R : ℝ)
    (hB : 0≤B) (hR : 0≤R) (p : CompactTiltParameter) (hp : 0<p.1)
    (hpR : p.1≤R) (hg : ‖p.2.1‖+‖p.2.2‖≤B) :
    ‖Ring.inverse (compactTiltNormalizer w p)‖≤(compactNormalizerBallLower w B R)⁻¹ := by
  have hδ := compactNormalizerBallLower_pos w B R hB hR
  apply (BoundedContinuousFunction.norm_le (inv_nonneg.mpr hδ.le)).mpr
  intro s
  rw [inverse_compactTiltNormalizer_apply w p hp s]
  have hs := compactNormalizerBallLower_le w B R hB hR p hp hpR hg s
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (hδ.trans_le hs).le)]
  exact (inv_le_inv₀ (hδ.trans_le hs) hδ).mpr hs

theorem norm_iteratedFDeriv_inverse_at_compactTiltNormalizer_le
    (w : ℝ≥0) (B R : ℝ) (hB : 0≤B) (hR : 0≤R)
    (p : CompactTiltParameter) (hp : 0<p.1) (hpR : p.1≤R)
    (hg : ‖p.2.1‖+‖p.2.2‖≤B) (n : ℕ) :
    ‖iteratedFDeriv ℝ n Ring.inverse (compactTiltNormalizer w p)‖ ≤
      (n.factorial:ℝ)*((compactNormalizerBallLower w B R)⁻¹)^(n+1) := by
  letI : Nontrivial (CompactTiltLocation→ᵇℝ) := ⟨⟨0,1,by
    intro he
    have hh := congrArg (fun f:CompactTiltLocation→ᵇℝ=>f (⟨0,⟨le_rfl,zero_le_one⟩⟩,0)) he
    norm_num at hh⟩⟩
  have hunit := isUnit_compactTiltNormalizer w p hp
  have h := norm_iteratedFDeriv_inverse_le hunit.unit n
  simp only [IsUnit.unit_spec] at h
  have he : ((hunit.unit⁻¹:((CompactTiltLocation→ᵇℝ)ˣ)):(CompactTiltLocation→ᵇℝ))=
      Ring.inverse (compactTiltNormalizer w p) := by
    simpa only [hunit.unit_spec] using (Ring.inverse_unit hunit.unit).symm
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _)
      (norm_inverse_compactTiltNormalizer_le w B R hB hR p hp hpR hg) (n+1))
    (Nat.cast_nonneg _))

end GeneralDepthPaper
