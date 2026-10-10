module

public import PositiveFieldPaper.Foundation
public import FourPapersCommon.AllFieldMomentRegularity

@[expose] public section


/-! Actual polynomial moments and their universal evolution in the paper's t clock. -/
noncomputable section
open Set MeasureTheory Filter MvPolynomial
open scoped Topology ContDiff
namespace PositiveFieldPaper
open FRSB

abbrev MomentPolynomial := FRSB.MomentPolynomial

theorem D_succ_eq_jet (β : ℝ) (ν : Paper.ParisiMeasure) (j : ℕ) (t x : ℝ) :
    D β ν (j+1) t x=FRSB.parisiSpatialJet β ν (j+1) (t/β^2) x := by
  simp [D,Paper.parisiSpatialField,FRSB.parisiSpatialJet]

def polynomialMoment (β h : ℝ) (hβ : β≠0) (ν : Paper.ParisiMeasure)
    (f : MomentPolynomial) (t : ℝ) : ℝ :=
  ∫sample,eval (fun j => D β ν (j+1) t (Y β h hβ ν t sample)) f ∂brownianMeasure

theorem integrable_polynomialMoment_integrand (β h:ℝ) (hβ:β≠0) (ν:Paper.ParisiMeasure)
    (f:MomentPolynomial) (t:ℝ) :
    Integrable (fun sample=>eval (fun j=>D β ν (j+1) t (Y β h hβ ν t sample)) f) brownianMeasure := by
  have hh:=FourPapersCommon.integrable_fixedStatePolynomialField β h hβ ν ν f (t/β^2)
  convert hh using 1
  funext sample
  unfold FRSB.polynomialJetField
  congr 1

theorem integrable_D_succ_Y_pow (β h:ℝ) (hβ:β≠0) (ν:Paper.ParisiMeasure)
    (j n:ℕ) (t:ℝ) :
    Integrable (fun sample=>(D β ν (j+1) t (Y β h hβ ν t sample))^n) brownianMeasure := by
  simpa only [map_pow,eval_X] using
    integrable_polynomialMoment_integrand β h hβ ν (MvPolynomial.X j^n) t

theorem polynomialMoment_eq_fieldMoment (β h : ℝ) (hβ : β≠0) (ν : Paper.ParisiMeasure)
    (f : MomentPolynomial) (t : ℝ) :
    polynomialMoment β h hβ ν f t=FourPapersCommon.fieldMoment β h hβ ν f (t/β^2) := by
  unfold polynomialMoment FourPapersCommon.fieldMoment FourPapersCommon.fixedStatePolynomialMoment
    FRSB.polynomialJetField
  apply integral_congr_ae
  exact .of_forall fun sample => by
    congr 1

theorem continuous_polynomialMoment (β h : ℝ) (hβ : β≠0) (ν : Paper.ParisiMeasure)
    (f : MomentPolynomial) : Continuous (polynomialMoment β h hβ ν f) := by
  have he := funext (polynomialMoment_eq_fieldMoment β h hβ ν f)
  rw [he]
  exact (FourPapersCommon.continuous_fieldMoment β h hβ ν f).comp (continuous_id.div_const _)

theorem polynomialMoment_interval_integral (β h : ℝ) (hβ : β≠0)
    (ν : Paper.ParisiMeasure) (f : MomentPolynomial) {r t : ℝ}
    (hr : r∈Icc (0:ℝ) (L β)) (ht : t∈Icc (0:ℝ) (L β)) :
    polynomialMoment β h hβ ν f t-polynomialMoment β h hβ ν f r=
      ∫s in r..t,polynomialMoment β h hβ ν (momentDrift0 f) s+
        mass β ν s*polynomialMoment β h hβ ν (momentDrift1 f) s := by
  have hh := FourPapersCommon.moment_interval_integral_physical β h hβ ν f
    (overlapTime_mem hβ hr) (overlapTime_mem hβ ht)
  have hi := intervalIntegral.integral_comp_div
    (fun s => FourPapersCommon.fieldMoment β h hβ ν (momentDrift0 f) s+
      Paper.parisiCDF ν s*FourPapersCommon.fieldMoment β h hβ ν (momentDrift1 f) s)
    (a:=r) (b:=t) (c:=β^2) (pow_ne_zero 2 hβ)
  simp only [smul_eq_mul] at hi
  rw [←hi] at hh
  simpa only [polynomialMoment_eq_fieldMoment,mass] using hh

theorem polynomialMoment_sub_norm_le (β h : ℝ) (hβ : β≠0)
    (ν : Paper.ParisiMeasure) (f : MomentPolynomial) {r t : ℝ}
    (hr : r∈Icc (0:ℝ) (L β)) (ht : t∈Icc (0:ℝ) (L β)) :
    ‖polynomialMoment β h hβ ν f t-polynomialMoment β h hβ ν f r‖≤
      (uniformPolynomialMomentBound β (momentDrift0 f)+
        uniformPolynomialMomentBound β (momentDrift1 f))*|t-r| := by
  rw [polynomialMoment_eq_fieldMoment,polynomialMoment_eq_fieldMoment]
  have hh := FourPapersCommon.fieldMoment_sub_norm_le β h hβ ν f
    (overlapTime_mem hβ hr) (overlapTime_mem hβ ht)
  have he : β^2*(uniformPolynomialMomentBound β (momentDrift0 f)+
      uniformPolynomialMomentBound β (momentDrift1 f))*|t/β^2-r/β^2|=
      (uniformPolynomialMomentBound β (momentDrift0 f)+
        uniformPolynomialMomentBound β (momentDrift1 f))*|t-r| := by
    rw [←sub_div,abs_div,abs_of_nonneg (sq_nonneg β)]
    field_simp [hβ]
  rwa [he] at hh

end PositiveFieldPaper
