module

public import FourPapersCommon.AllFieldPolynomialMomentGrid
public import FRSB.ParisiGridTopology

@[expose] public section


/-! The actual all-polynomial moment evolution for every overlap law. The
identity comes from genuine finite-cell Itô calculus and weak approximation;
no stochastic or evolution identity is supplied as a premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped Topology NNReal
namespace FourPapersCommon
open FRSB

theorem tendsto_fixedStatePolynomialMoment_of_weak {ι : Type*} {L : Filter ι}
    (β h : ℝ) (hβ : β ≠ 0) (μ ρ : Paper.ParisiMeasure) (ν : ι → Paper.ParisiMeasure)
    (hν : Tendsto ν L (nhds ρ)) (f : MomentPolynomial) (t : ℝ) :
    Tendsto (fun i => fixedStatePolynomialMoment β h hβ μ (ν i) f t) L
      (nhds (fixedStatePolynomialMoment β h hβ μ ρ f t)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun i => norm_nonneg _)
    (fun i => fixedStatePolynomialMoment_sub_norm_le β h hβ μ (ν i) ρ f t)
  have hh := ((continuous_polynomialJetBCF β f).tendsto ρ).comp hν
    |>.sub_const (polynomialJetBCF β ρ f) |>.norm
  simpa only [Function.comp_apply,sub_self,norm_zero] using hh

theorem moment_tail_integral (β h : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (f : MomentPolynomial) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    fieldMoment β h hβ μ f 1-fieldMoment β h hβ μ f s =
      ∫t in s..1,polynomialMomentSource β h hβ μ μ f t := by
  have hF (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Tendsto (fun n => gridPolynomialMoment β h hβ μ f n t) atTop
        (nhds (fieldMoment β h hβ μ f t)) := by
    have hh := tendsto_fixedStatePolynomialMoment_of_weak β h hβ μ μ
      (parisiGridMeasure μ) (tendsto_parisiGridMeasure μ) f t
    rw [fixedStatePolynomialMoment_self_physical β h hβ μ f ht] at hh
    exact hh
  have hS := tendsto_polynomialMomentSource_integral_of_weak β h hβ μ μ
    (parisiGridMeasure μ) (tendsto_parisiGridMeasure μ) f s 1
  have hleft := ((hF 1 ⟨by norm_num,le_rfl⟩).sub (hF s hs)).sub hS |>.norm
  have hright : Tendsto (fun n => β^2*((uniformPolynomialMomentBound β (momentDrift1 f)+
      uniformPolynomialMomentBound β (polynomialSpatialDerivative f))*
      parisiCDFDistance μ (parisiGridMeasure μ n)+
        uniformPolynomialMomentBound β (polynomialSpatialDerivative f)*
          parisiHJBGradientError β μ n)) atTop (nhds 0) := by
    simpa only [mul_zero,zero_add] using
      (((tendsto_parisiCDFDistance_grid μ).const_mul
        (uniformPolynomialMomentBound β (momentDrift1 f)+
          uniformPolynomialMomentBound β (polynomialSpatialDerivative f))).add
      ((tendsto_parisiHJBGradientError β hβ μ).const_mul
        (uniformPolynomialMomentBound β (polynomialSpatialDerivative f)))).const_mul (β^2)
  have hh := le_of_tendsto_of_tendsto hleft hright
    (.of_forall fun n => gridPolynomial_tail_remainder_le β h hβ μ f n hs)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))

/-- Endpoint order is unrestricted, so this is the full interval identity. -/
theorem moment_interval_integral (β h : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (f : MomentPolynomial) {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    fieldMoment β h hβ μ f t-fieldMoment β h hβ μ f r =
      ∫s in r..t,polynomialMomentSource β h hβ μ μ f s := by
  have hR := moment_tail_integral β h hβ μ f hr
  have hT := moment_tail_integral β h hβ μ f ht
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (polynomialMomentSource_intervalIntegrable β h hβ μ μ f r t)
    (polynomialMomentSource_intervalIntegrable β h hβ μ μ f t 1)
  linarith

theorem moment_integral (β h : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (f : MomentPolynomial) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    fieldMoment β h hβ μ f t = fieldMoment β h hβ μ f 0+
      ∫s in 0..t,polynomialMomentSource β h hβ μ μ f s := by
  have hh := moment_interval_integral β h hβ μ f ⟨le_rfl,by norm_num⟩ ht
  linarith

theorem polynomialMomentSource_self_physical (β h : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (f : MomentPolynomial) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    polynomialMomentSource β h hβ μ μ f t =
      β^2*(fieldMoment β h hβ μ (momentDrift0 f) t+parisiCDF μ t*fieldMoment β h hβ μ (momentDrift1 f) t) := by
  unfold polynomialMomentSource
  rw [fixedStatePolynomialMoment_self_physical β h hβ μ (momentDrift0 f) ht,
    fixedStatePolynomialMoment_self_physical β h hβ μ (momentDrift1 f) ht]

/-- Literal universal Itô polynomial law, with both drift polynomials evaluated
on the actual state and actual spatial jets. -/
theorem moment_interval_integral_physical (β h : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (f : MomentPolynomial) {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    fieldMoment β h hβ μ f t-fieldMoment β h hβ μ f r = β^2*∫s in r..t,
      fieldMoment β h hβ μ (momentDrift0 f) s+parisiCDF μ s*fieldMoment β h hβ μ (momentDrift1 f) s := by
  rw [moment_interval_integral β h hβ μ f hr ht,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_uIoo
  intro s hs
  exact polynomialMomentSource_self_physical β h hβ μ f
    (uIcc_subset_Icc hr ht ⟨hs.1.le,hs.2.le⟩)

end FourPapersCommon
