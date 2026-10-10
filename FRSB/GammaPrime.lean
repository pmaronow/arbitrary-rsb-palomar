module

public import FRSB.GammaIdentity

@[expose] public section


/-! The actual continuous curvature expression for the one-sided Gamma
 derivative, including both closed physical endpoints. -/
noncomputable section
open Set Paper
namespace FRSB

def GammaPrime (β : ℝ) (μ : ParisiMeasure) (t : ℝ) : ℝ :=
  β^2*curvatureMoment2 β μ t

theorem GammaPrime_eq_source (β : ℝ) (hβ : β≠0) (μ : ParisiMeasure)
    {t : ℝ} (ht:t∈Icc (0:ℝ) 1) :
    GammaPrime β μ t=gammaCurvatureSource β hβ μ μ t :=
  (gammaCurvatureSource_self β hβ μ ht).symm

theorem continuousOn_GammaPrime (β : ℝ) (hβ : β≠0) (μ : ParisiMeasure) :
    ContinuousOn (GammaPrime β μ) (Icc (0:ℝ) 1) :=
  (continuous_gammaCurvatureSource β hβ μ μ).continuousOn.congr
    (fun _ ht=>GammaPrime_eq_source β hβ μ ht)

theorem GammaPrime_pos (β : ℝ) (hβ : β≠0) (μ : ParisiMeasure)
    {t : ℝ} (ht:t∈Icc (0:ℝ) 1) : 0<GammaPrime β μ t :=
  mul_pos (sq_pos_of_ne_zero hβ) (curvatureMoment2_pos β hβ μ ht)

theorem GammaPrime_le_beta_sq (β : ℝ) (hβ : β≠0) (μ : ParisiMeasure)
    {t : ℝ} (ht:t∈Icc (0:ℝ) 1) : GammaPrime β μ t≤β^2 := by
  simpa only [GammaPrime,mul_one] using mul_le_mul_of_nonneg_left
    (curvatureMoment2_le_one β hβ μ ht) (sq_nonneg β)

theorem hasDerivWithinAt_Gamma_GammaPrime (β : ℝ) (hβ : β≠0)
    (μ : ParisiMeasure) {t : ℝ} (ht:t∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (Gamma β μ) (GammaPrime β μ t) (Icc (0:ℝ) 1) t :=
  hasDerivWithinAt_Gamma β hβ μ ht

theorem hasDerivAt_Gamma_GammaPrime (β : ℝ) (hβ : β≠0)
    (μ : ParisiMeasure) {t : ℝ} (ht:t∈Ioo (0:ℝ) 1) :
    HasDerivAt (Gamma β μ) (GammaPrime β μ t) t :=
  hasDerivAt_Gamma β hβ μ ht

end FRSB
