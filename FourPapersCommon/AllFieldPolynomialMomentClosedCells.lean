module

public import FourPapersCommon.AllFieldPolynomialMomentCells
public import FRSB.ClosedIntervalBounds

@[expose] public section


/-! Actual arbitrary-polynomial moment estimates at both finite-cell endpoints. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped NNReal Topology
namespace FourPapersCommon
open FRSB
open SpinGlass.Targets

def polynomialCellError (β : ℝ) (μ : Paper.ParisiMeasure) (F : MomentPolynomial)
    (m eps t : ℝ) : ℝ :=
  β^2*((uniformPolynomialMomentBound β (momentDrift1 F)+
    uniformPolynomialMomentBound β (polynomialSpatialDerivative F))*|parisiCDF μ t-m|+
      uniformPolynomialMomentBound β (polynomialSpatialDerivative F)*eps)

theorem polynomialCellError_intervalIntegrable (β : ℝ) (μ : Paper.ParisiMeasure)
    (F : MomentPolynomial) (m eps a b : ℝ) :
    IntervalIntegrable (polynomialCellError β μ F m eps) volume a b :=
  (((((parisiCDF_monotone μ).intervalIntegrable).sub intervalIntegrable_const).norm.const_mul
    (uniformPolynomialMomentBound β (momentDrift1 F)+
      uniformPolynomialMomentBound β (polynomialSpatialDerivative F))).add
        intervalIntegrable_const).const_mul (β^2)

theorem polynomial_moment_finite_cell_bound (β h : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) {k : ℕ} (s : RSBScheme k) {p : ℕ} (hp : p ≤ k+1)
    (hq : s.q p < s.q (p+1)) (F : MomentPolynomial)
    {l r : ℝ} (hl : s.q p ≤ l) (hlr : l ≤ r) (hr : r ≤ s.q (p+1))
    (eps : ℝ) (heps : 0 ≤ eps)
    (hclose : ∀ t ∈ Icc (s.q p) (s.q (p+1)), ∀ x,
      ‖parisiGradient β μ (t,x)-parisiSpatialJet β (parisiSchemeMeasure s) 1 t x‖ ≤ eps) :
    ‖fixedStatePolynomialMoment β h hβ μ (parisiSchemeMeasure s) F r-
      fixedStatePolynomialMoment β h hβ μ (parisiSchemeMeasure s) F l-
      ∫t in l..r,polynomialMomentSource β h hβ μ (parisiSchemeMeasure s) F t‖ ≤
    ∫t in l..r,polynomialCellError β μ F (s.m p) eps t := by
  apply closed_interval_increment_bound
    (fixedStatePolynomialMoment β h hβ μ (parisiSchemeMeasure s) F)
    (polynomialMomentSource β h hβ μ (parisiSchemeMeasure s) F)
    (polynomialCellError β μ F (s.m p) eps)
    (continuous_fixedStatePolynomialMoment β h hβ μ (parisiSchemeMeasure s) F)
    (polynomialMomentSource_intervalIntegrable β h hβ μ (parisiSchemeMeasure s) F)
    (polynomialCellError_intervalIntegrable β μ F (s.m p) eps) hq _ hl hlr hr
  intro x y hx hxy hy
  have hx0 : 0 ≤ x := (s.q_nonneg (by omega)).trans hx.le
  have hy0 : 0 ≤ y := hx0.trans hxy
  let xN : ℝ≥0 := ⟨x, hx0⟩
  let yN : ℝ≥0 := ⟨y, hy0⟩
  exact polynomial_moment_finite_cell_cropped_bound β h hβ μ s hp hq F
    xN yN hx (NNReal.coe_le_coe.mp hxy) hy eps heps
      (fun t ht z => hclose t ⟨hx.le.trans ht.1,ht.2.trans hy.le⟩ z)

end FourPapersCommon
