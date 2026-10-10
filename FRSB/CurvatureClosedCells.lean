module

public import FRSB.CurvatureCells
public import FRSB.ClosedIntervalBounds

@[expose] public section


/-! Genuine finite-cell curvature estimates at both cell endpoints. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped NNReal Topology
namespace FRSB
open SpinGlass.Targets

def curvatureCellError (β : ℝ) (μ : ParisiMeasure) (m eps t : ℝ) : ℝ :=
  2 * β ^ 2 * ((1+uniformSpatialConstant β 2) * |parisiCDF μ t-m| +
    uniformSpatialConstant β 2 * eps)

theorem curvatureCellError_intervalIntegrable (β : ℝ) (μ : ParisiMeasure)
    (m eps a b : ℝ) : IntervalIntegrable (curvatureCellError β μ m eps) volume a b :=
  (((((parisiCDF_monotone μ).intervalIntegrable).sub intervalIntegrable_const).norm.const_mul
    (1+uniformSpatialConstant β 2)).add intervalIntegrable_const).const_mul (2*β^2)

theorem curvature_square_finite_cell_bound (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {k : ℕ} (s : RSBScheme k) {p : ℕ} (hp : p ≤ k+1)
    (hq : s.q p < s.q (p+1)) {l r : ℝ} (hl : s.q p ≤ l) (hlr : l ≤ r)
    (hr : r ≤ s.q (p+1)) (eps : ℝ) (heps : 0 ≤ eps)
    (hclose : ∀ t ∈ Icc (s.q p) (s.q (p+1)), ∀ x,
      ‖parisiGradient β μ (t,x)-parisiSpatialJet β (parisiSchemeMeasure s) 1 t x‖ ≤ eps) :
    ‖fixedStateJetPower β hβ μ (parisiSchemeMeasure s) 1 2 r-
      fixedStateJetPower β hβ μ (parisiSchemeMeasure s) 1 2 l-
      ∫t in l..r,curvatureEvolutionSource β hβ μ (parisiSchemeMeasure s) t‖ ≤
    ∫t in l..r,curvatureCellError β μ (s.m p) eps t := by
  apply closed_interval_increment_bound
    (fixedStateJetPower β hβ μ (parisiSchemeMeasure s) 1 2)
    (curvatureEvolutionSource β hβ μ (parisiSchemeMeasure s))
    (curvatureCellError β μ (s.m p) eps)
    (continuous_fixedStateJetPower β hβ μ (parisiSchemeMeasure s) 1 2)
    (curvatureEvolutionSource_intervalIntegrable β hβ μ (parisiSchemeMeasure s))
    (curvatureCellError_intervalIntegrable β μ (s.m p) eps) hq _ hl hlr hr
  intro x y hx hxy hy
  have hx0 : 0 ≤ x := (s.q_nonneg (by omega)).trans hx.le
  have hy0 : 0 ≤ y := hx0.trans hxy
  let xN : ℝ≥0 := ⟨x, hx0⟩
  let yN : ℝ≥0 := ⟨y, hy0⟩
  have hh := curvature_square_finite_cell_cropped_bound β hβ μ s hp hq
    xN yN hx (NNReal.coe_le_coe.mp hxy) hy eps heps (fun t ht z =>
      hclose t ⟨hx.le.trans ht.1, ht.2.trans hy.le⟩ z)
  exact hh

end FRSB
