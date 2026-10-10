module

public import FourPapersCommon.AllFieldPolynomialMomentClosedCells
public import FRSB.GridMeasureIdentification
public import Paper.ParisiGradientMesh

@[expose] public section


/-! Actual arbitrary-polynomial moment grid estimates along the fixed optimal diffusion. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped Topology NNReal
namespace FourPapersCommon
open FRSB
set_option maxHeartbeats 1000000

def gridPolynomialMoment (β h : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (f : MomentPolynomial) (n : ℕ) (t : ℝ) : ℝ :=
  fixedStatePolynomialMoment β h hβ μ (parisiGridMeasure μ n) f t

def polynomialGridError (β : ℝ) (μ : Paper.ParisiMeasure) (f : MomentPolynomial) (n : ℕ) (t : ℝ) : ℝ :=
  β^2*((uniformPolynomialMomentBound β (momentDrift1 f)+uniformPolynomialMomentBound β (polynomialSpatialDerivative f))*
    |parisiCDF μ t-parisiCDF (parisiGridMeasure μ n) t|+
      uniformPolynomialMomentBound β (polynomialSpatialDerivative f)*parisiHJBGradientError β μ n)

theorem polynomialGridError_intervalIntegrable (β : ℝ) (μ : Paper.ParisiMeasure) (f : MomentPolynomial)
    (n : ℕ) (a b : ℝ) : IntervalIntegrable (polynomialGridError β μ f n) volume a b :=
  (((parisiCDF_abs_diff_intervalIntegrable μ (parisiGridMeasure μ n) a b).const_mul
    (uniformPolynomialMomentBound β (momentDrift1 f)+uniformPolynomialMomentBound β (polynomialSpatialDerivative f))).add intervalIntegrable_const).const_mul (β^2)

theorem polynomialGridError_nonneg (β : ℝ) (μ : Paper.ParisiMeasure) (f : MomentPolynomial) (n : ℕ) (t : ℝ) :
    0 ≤ polynomialGridError β μ f n t := by
  unfold polynomialGridError
  have hK := uniformPolynomialMomentBound_nonneg β (polynomialSpatialDerivative f)
  have hD := uniformPolynomialMomentBound_nonneg β (momentDrift1 f)
  have hE := parisiHJBGradientError_nonneg β μ n
  positivity

theorem polynomial_moment_grid_cell_bound (β h : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (f : MomentPolynomial) (n i : ℕ) (hi : i < n+1) {a b : ℝ} (hab : a < b)
    (ha : a ∈ Icc (hjbGridTime n i) (hjbGridTime n (i+1)))
    (hb : b = hjbGridTime n (i+1)) :
    ‖gridPolynomialMoment β h hβ μ f n b-gridPolynomialMoment β h hβ μ f n a-
      ∫t in a..b,polynomialMomentSource β h hβ μ (parisiGridMeasure μ n) f t‖ ≤
    ∫t in a..b,polynomialGridError β μ f n t := by
  let s := parisiGridRSBScheme μ n
  obtain ⟨hq0,hq1⟩ := hjbGrid_cell_q μ n i hi
  have hq : s.q (i+1) < s.q (i+1+1) := by
    simpa only [s,hq0,show i+1+1=i+2 by omega,hq1] using hjbGridTime_step_lt n i
  have hh := polynomial_moment_finite_cell_bound β h hβ μ s (p := i+1) (by omega) hq f
    (l := a) (r := b) (by simpa only [s,hq0] using ha.1) hab.le
    (by simpa only [s,show i+1+1=i+2 by omega,hq1] using hb.le)
    (parisiHJBGradientError β μ n) (parisiHJBGradientError_nonneg β μ n) (by
      intro t _ x
      rw [parisiSpatialJet_one,parisiSchemeMeasure_grid_eq μ n,
        parisiGradient_grid_eq_finite β hβ μ n]
      exact parisiHJBGradientError_bound β μ n t x)
  rw [parisiSchemeMeasure_grid_eq μ n] at hh
  have heE : (∫t in a..b,polynomialCellError β μ f (s.m (i+1))
      (parisiHJBGradientError β μ n) t) = ∫t in a..b,polynomialGridError β μ f n t := by
    apply intervalIntegral.integral_congr_Ioo_of_le hab.le
    intro t ht
    have htc : t ∈ Ico ((parisiGridRSBScheme μ n).q (i+1))
        ((parisiGridRSBScheme μ n).q (i+1+1)) := by
      simpa only [hq0,show i+1+1=i+2 by omega,hq1] using
        (show t ∈ Ico (hjbGridTime n i) (hjbGridTime n (i+1)) from
          ⟨ha.1.trans ht.1.le,ht.2.trans_eq hb⟩)
    unfold polynomialCellError polynomialGridError
    rw [parisiCDF_grid_eq_scheme_mass μ n (i+1) (by omega) (by omega) htc]
  rw [heE] at hh
  exact hh

theorem gridPolynomial_tail_remainder_le (β h : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (f : MomentPolynomial)
    (n : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖gridPolynomialMoment β h hβ μ f n 1-gridPolynomialMoment β h hβ μ f n s-
      ∫t in s..1,polynomialMomentSource β h hβ μ (parisiGridMeasure μ n) f t‖ ≤
    β^2*((uniformPolynomialMomentBound β (momentDrift1 f)+uniformPolynomialMomentBound β (polynomialSpatialDerivative f))*parisiCDFDistance μ (parisiGridMeasure μ n)+
      uniformPolynomialMomentBound β (polynomialSpatialDerivative f)*parisiHJBGradientError β μ n) := by
  let T := parisiGradientMeshTime n s
  let S := polynomialMomentSource β h hβ μ (parisiGridMeasure μ n) f
  let F : ℕ → ℝ := fun i => gridPolynomialMoment β h hβ μ f n (T i)-∫t in s..T i,S t
  have hSi : ∀ a b, IntervalIntegrable S volume a b :=
    polynomialMomentSource_intervalIntegrable β h hβ μ (parisiGridMeasure μ n) f
  have htel := parisiGradientMesh_norm_telescope F (polynomialGridError β μ f n) T (n+1)
    (fun i _ => polynomialGridError_intervalIntegrable β μ f n _ _) (by
      intro i hi
      rcases parisiGradientMeshTime_step_cases n s i with heq | hlt
      · change T i=T (i+1) at heq
        simp only [F,heq,sub_self,intervalIntegral.integral_same,norm_zero,le_refl]
      · have hcell := parisiGradientMeshTime_cell_subset n s i hlt
        have hh := polynomial_moment_grid_cell_bound β h hβ μ f n i hi hlt
          (hcell ⟨le_rfl,hlt.le⟩) (parisiGradientMeshTime_step_lt_terminal n s i hlt)
        have heF : F (i+1)-F i = gridPolynomialMoment β h hβ μ f n (T (i+1))-
            gridPolynomialMoment β h hβ μ f n (T i)-∫t in T i..T (i+1),S t := by
          have hii := intervalIntegral.integral_interval_sub_left (hSi s (T (i+1))) (hSi s (T i))
          dsimp only [F]
          linarith
        rw [heF]
        exact hh)
  have hfull : (∫t in s..1,polynomialGridError β μ f n t) ≤
      β^2*((uniformPolynomialMomentBound β (momentDrift1 f)+uniformPolynomialMomentBound β (polynomialSpatialDerivative f))*parisiCDFDistance μ (parisiGridMeasure μ n)+
        uniformPolynomialMomentBound β (polynomialSpatialDerivative f)*parisiHJBGradientError β μ n) := by
    have hh := parisiGradientMesh_integral_le_full hs
      (polynomialGridError_intervalIntegrable β μ f n 0 1) (polynomialGridError_nonneg β μ f n)
    apply hh.trans_eq
    unfold polynomialGridError parisiCDFDistance
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
      ((parisiCDF_abs_diff_intervalIntegrable μ (parisiGridMeasure μ n) 0 1).const_mul _)
      intervalIntegrable_const,intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_const,sub_zero,one_smul]
  simp only [T,parisiGradientMeshTime_terminal n hs.2,parisiGradientMeshTime_zero n hs.1] at htel
  have hh : ‖(gridPolynomialMoment β h hβ μ f n 1-(∫t in s..1,S t))-
      gridPolynomialMoment β h hβ μ f n s‖ ≤
      β^2*((uniformPolynomialMomentBound β (momentDrift1 f)+uniformPolynomialMomentBound β (polynomialSpatialDerivative f))*parisiCDFDistance μ (parisiGridMeasure μ n)+
        uniformPolynomialMomentBound β (polynomialSpatialDerivative f)*parisiHJBGradientError β μ n) := by
    simpa only [F,T,parisiGradientMeshTime_terminal n hs.2,parisiGradientMeshTime_zero n hs.1,
      intervalIntegral.integral_same,sub_zero] using htel.trans hfull
  convert hh using 2
  ring

end FourPapersCommon
