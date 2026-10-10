module

public import FourPapersCommon.AllFieldPolynomialMomentIdentity
public import FRSB.MomentConstantBootstrap
public import FRSB.GammaSecond

@[expose] public section


/-! Genuine differentiation and simultaneous smoothness of the actual
polynomial moments. Endpoint coefficients are taken from the continuous
one-sided representative, so a terminal atom does not alter left derivatives. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology ContDiff
namespace FourPapersCommon
open FRSB
set_option maxHeartbeats 1000000

theorem fieldMoment_sub_norm_le (β h : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (f : MomentPolynomial) {r t : ℝ} (hr : r∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1) :
    ‖fieldMoment β h hβ μ f t-fieldMoment β h hβ μ f r‖≤
      β^2*(uniformPolynomialMomentBound β (momentDrift0 f)+
        uniformPolynomialMomentBound β (momentDrift1 f))*|t-r| := by
  rw [moment_interval_integral β h hβ μ f hr ht]
  exact intervalIntegral.norm_integral_le_of_norm_le_const
    (fun s _ => norm_polynomialMomentSource_le β h hβ μ μ f s)

theorem lipschitzOn_fieldMoment (β h : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (f : MomentPolynomial) :
    LipschitzOnWith ⟨β^2*(uniformPolynomialMomentBound β (momentDrift0 f)+
      uniformPolynomialMomentBound β (momentDrift1 f)),
        mul_nonneg (sq_nonneg β) (add_nonneg
          (uniformPolynomialMomentBound_nonneg β _) (uniformPolynomialMomentBound_nonneg β _))⟩
      (fieldMoment β h hβ μ f) (Icc (0:ℝ) 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht r hr
  change dist (fieldMoment β h hβ μ f t) (fieldMoment β h hβ μ f r)≤
    (β^2*(uniformPolynomialMomentBound β (momentDrift0 f)+
      uniformPolynomialMomentBound β (momentDrift1 f)))*dist t r
  simpa [dist_eq_norm,Real.norm_eq_abs] using fieldMoment_sub_norm_le β h hβ μ f hr ht

 theorem hasDerivAt_moment_of_continuousAt_CDF (β h : ℝ) (hβ:β≠0) (μ:Paper.ParisiMeasure)
    (f:MomentPolynomial) {t:ℝ} (ht:t∈Ioo (0:ℝ) 1)
    (hCDF:ContinuousAt (parisiCDF μ) t) :
    HasDerivAt (fieldMoment β h hβ μ f)
      (β^2*(fieldMoment β h hβ μ (momentDrift0 f) t+parisiCDF μ t*fieldMoment β h hβ μ (momentDrift1 f) t)) t := by
  have hc:ContinuousAt (polynomialMomentSource β h hβ μ μ f) t :=
    continuousAt_const.mul (((continuous_fixedStatePolynomialMoment β h hβ μ μ _).continuousAt).add
      (hCDF.mul (continuous_fixedStatePolynomialMoment β h hβ μ μ _).continuousAt))
  have hd:=(intervalIntegral.integral_hasDerivAt_right
    (polynomialMomentSource_intervalIntegrable β h hβ μ μ f 0 t)
    (polynomialMomentSource_measurable β h hβ μ μ f).aestronglyMeasurable.stronglyMeasurableAtFilter hc).const_add
      (fieldMoment β h hβ μ f 0)
  have he:fieldMoment β h hβ μ f =ᶠ[nhds t] fun r=>fieldMoment β h hβ μ f 0+
      ∫s in 0..r,polynomialMomentSource β h hβ μ μ f s := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact moment_integral β h hβ μ f ⟨hr.1.le,hr.2.le⟩
  rw [polynomialMomentSource_self_physical β h hβ μ f ⟨ht.1.le,ht.2.le⟩] at hd
  exact hd.congr_of_eventuallyEq he

 theorem hasDerivAt_moment_of_constant_CDF (β h : ℝ) (hβ:β≠0) (μ:Paper.ParisiMeasure)
    (m a b:ℝ) (hI:Ioo a b⊆Ioo (0:ℝ) 1)
    (hCDF:∀s∈Ioo a b,parisiCDF μ s=m) (f:MomentPolynomial)
    {t:ℝ} (ht:t∈Ioo a b) : HasDerivAt (fieldMoment β h hβ μ f)
      (β^2*(fieldMoment β h hβ μ (momentDrift0 f) t+m*fieldMoment β h hβ μ (momentDrift1 f) t)) t := by
  have hh:=hasDerivAt_moment_of_continuousAt_CDF β h hβ μ f (hI ht)
    (continuousAt_CDF_of_constant_on_Ioo μ m a b hCDF ht)
  rwa [hCDF t ht] at hh

 theorem contDiffOn_moment_of_constant_CDF (β h : ℝ) (hβ:β≠0) (μ:Paper.ParisiMeasure)
    (m a b:ℝ) (hI:Ioo a b⊆Ioo (0:ℝ) 1)
    (hCDF:∀s∈Ioo a b,parisiCDF μ s=m) (f:MomentPolynomial) :
    ContDiffOn ℝ ∞ (fieldMoment β h hβ μ f) (Ioo a b) := by
  apply moments_contDiffOn_constant_hierarchy (fieldMoment β h hβ μ) momentDrift0 momentDrift1 β m a b
  · intro g
    exact (continuous_fieldMoment β h hβ μ g).continuousOn
  · intro g t ht
    exact hasDerivAt_moment_of_constant_CDF β h hβ μ m a b hI hCDF g ht

 theorem hasDerivWithinAt_moment_of_continuous_coefficient (β h : ℝ) (hβ:β≠0)
    (μ:Paper.ParisiMeasure) (q:ℝ) (hq:0≤q) (hq1:q≤1) (c:ℝ→ℝ)
    (hc:ContinuousOn c (Icc (0:ℝ) q))
    (hcoeff:∀s∈Ioo (0:ℝ) q,parisiCDF μ s=c s)
    (f:MomentPolynomial) {t:ℝ} (ht:t∈Icc (0:ℝ) q) :
    HasDerivWithinAt (fieldMoment β h hβ μ f)
      (β^2*(fieldMoment β h hβ μ (momentDrift0 f) t+c t*fieldMoment β h hβ μ (momentDrift1 f) t))
      (Icc (0:ℝ) q) t := by
  have hsub:Icc (0:ℝ) q⊆Icc (0:ℝ) 1:=Icc_subset_Icc le_rfl hq1
  have he:∀u∈Icc (0:ℝ) q,fieldMoment β h hβ μ f u=fieldMoment β h hβ μ f 0+
      ∫s in 0..u,β^2*(fieldMoment β h hβ μ (momentDrift0 f) s+c s*fieldMoment β h hβ μ (momentDrift1 f) s) := by
    intro u hu
    have hh:=moment_interval_integral_physical β h hβ μ f ⟨le_rfl,hq.trans hq1⟩ (hsub hu)
    have hi:(β^2*∫s in 0..u,fieldMoment β h hβ μ (momentDrift0 f) s+
        parisiCDF μ s*fieldMoment β h hβ μ (momentDrift1 f) s)=
      ∫s in 0..u,β^2*(fieldMoment β h hβ μ (momentDrift0 f) s+c s*fieldMoment β h hβ μ (momentDrift1 f) s) := by
      rw [←intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_Ioo_of_le hu.1
      intro s hs
      dsimp only
      rw [hcoeff s ⟨hs.1,hs.2.trans_le hu.2⟩]
    rw [hi] at hh
    linarith
  apply hasDerivWithinAt_of_interval_identity _ _ q _ he t ht
  exact continuousOn_const.mul (((continuous_fieldMoment β h hβ μ _).continuousOn).add
    (hc.mul (continuous_fieldMoment β h hβ μ _).continuousOn))

end FourPapersCommon
