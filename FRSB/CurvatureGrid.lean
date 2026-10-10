module

public import FRSB.CurvatureClosedCells
public import FRSB.GridMeasureIdentification
public import Paper.ParisiGradientMesh

@[expose] public section


/-! Actual curvature-square grid estimates along the fixed optimal diffusion. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped Topology NNReal
namespace FRSB
set_option maxHeartbeats 1000000

def gridCurvatureMoment (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (n : ℕ) (t : ℝ) : ℝ :=
  fixedStateJetPower β hβ μ (parisiGridMeasure μ n) 1 2 t

def curvatureGridError (β : ℝ) (μ : ParisiMeasure) (n : ℕ) (t : ℝ) : ℝ :=
  2*β^2*((1+uniformSpatialConstant β 2)*
    |parisiCDF μ t-parisiCDF (parisiGridMeasure μ n) t|+
      uniformSpatialConstant β 2*parisiHJBGradientError β μ n)

theorem curvatureGridError_intervalIntegrable (β : ℝ) (μ : ParisiMeasure)
    (n : ℕ) (a b : ℝ) : IntervalIntegrable (curvatureGridError β μ n) volume a b :=
  (((parisiCDF_abs_diff_intervalIntegrable μ (parisiGridMeasure μ n) a b).const_mul
    (1+uniformSpatialConstant β 2)).add intervalIntegrable_const).const_mul (2*β^2)

theorem curvatureGridError_nonneg (β : ℝ) (μ : ParisiMeasure) (n : ℕ) (t : ℝ) :
    0 ≤ curvatureGridError β μ n t := by
  unfold curvatureGridError
  have hK := (uniformSpatialConstant_pos β 2).le
  have hE := parisiHJBGradientError_nonneg β μ n
  positivity

theorem curvature_square_grid_cell_bound (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (n i : ℕ) (hi : i < n+1) {a b : ℝ} (hab : a < b)
    (ha : a ∈ Icc (hjbGridTime n i) (hjbGridTime n (i+1)))
    (hb : b = hjbGridTime n (i+1)) :
    ‖gridCurvatureMoment β hβ μ n b-gridCurvatureMoment β hβ μ n a-
      ∫t in a..b,curvatureEvolutionSource β hβ μ (parisiGridMeasure μ n) t‖ ≤
    ∫t in a..b,curvatureGridError β μ n t := by
  let s := parisiGridRSBScheme μ n
  obtain ⟨hq0,hq1⟩ := hjbGrid_cell_q μ n i hi
  have hq : s.q (i+1) < s.q (i+1+1) := by
    simpa only [s,hq0,show i+1+1=i+2 by omega,hq1] using hjbGridTime_step_lt n i
  have hh := curvature_square_finite_cell_bound β hβ μ s (p := i+1) (by omega) hq
    (l := a) (r := b) (by simpa only [s,hq0] using ha.1) hab.le
    (by simpa only [s,show i+1+1=i+2 by omega,hq1] using hb.le)
    (parisiHJBGradientError β μ n) (parisiHJBGradientError_nonneg β μ n) (by
      intro t _ x
      rw [parisiSpatialJet_one,parisiSchemeMeasure_grid_eq μ n,
        parisiGradient_grid_eq_finite β hβ μ n]
      exact parisiHJBGradientError_bound β μ n t x)
  rw [parisiSchemeMeasure_grid_eq μ n] at hh
  have heE : (∫t in a..b,curvatureCellError β μ (s.m (i+1))
      (parisiHJBGradientError β μ n) t) = ∫t in a..b,curvatureGridError β μ n t := by
    apply intervalIntegral.integral_congr_Ioo_of_le hab.le
    intro t ht
    have htc : t ∈ Ico ((parisiGridRSBScheme μ n).q (i+1))
        ((parisiGridRSBScheme μ n).q (i+1+1)) := by
      simpa only [hq0,show i+1+1=i+2 by omega,hq1] using
        (show t ∈ Ico (hjbGridTime n i) (hjbGridTime n (i+1)) from
          ⟨ha.1.trans ht.1.le,ht.2.trans_eq hb⟩)
    unfold curvatureCellError curvatureGridError
    rw [parisiCDF_grid_eq_scheme_mass μ n (i+1) (by omega) (by omega) htc]
  rw [heE] at hh
  exact hh

theorem gridCurvature_tail_remainder_le (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (n : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖gridCurvatureMoment β hβ μ n 1-gridCurvatureMoment β hβ μ n s-
      ∫t in s..1,curvatureEvolutionSource β hβ μ (parisiGridMeasure μ n) t‖ ≤
    2*β^2*((1+uniformSpatialConstant β 2)*parisiCDFDistance μ (parisiGridMeasure μ n)+
      uniformSpatialConstant β 2*parisiHJBGradientError β μ n) := by
  let T := parisiGradientMeshTime n s
  let S := curvatureEvolutionSource β hβ μ (parisiGridMeasure μ n)
  let F : ℕ → ℝ := fun i => gridCurvatureMoment β hβ μ n (T i)-∫t in s..T i,S t
  have hSi : ∀ a b, IntervalIntegrable S volume a b :=
    curvatureEvolutionSource_intervalIntegrable β hβ μ (parisiGridMeasure μ n)
  have htel := parisiGradientMesh_norm_telescope F (curvatureGridError β μ n) T (n+1)
    (fun i _ => curvatureGridError_intervalIntegrable β μ n _ _) (by
      intro i hi
      rcases parisiGradientMeshTime_step_cases n s i with heq | hlt
      · change T i=T (i+1) at heq
        simp only [F,heq,sub_self,intervalIntegral.integral_same,norm_zero,le_refl]
      · have hcell := parisiGradientMeshTime_cell_subset n s i hlt
        have hh := curvature_square_grid_cell_bound β hβ μ n i hi hlt
          (hcell ⟨le_rfl,hlt.le⟩) (parisiGradientMeshTime_step_lt_terminal n s i hlt)
        have heF : F (i+1)-F i = gridCurvatureMoment β hβ μ n (T (i+1))-
            gridCurvatureMoment β hβ μ n (T i)-∫t in T i..T (i+1),S t := by
          have hii := intervalIntegral.integral_interval_sub_left (hSi s (T (i+1))) (hSi s (T i))
          dsimp only [F]
          linarith
        rw [heF]
        exact hh)
  have hfull : (∫t in s..1,curvatureGridError β μ n t) ≤
      2*β^2*((1+uniformSpatialConstant β 2)*parisiCDFDistance μ (parisiGridMeasure μ n)+
        uniformSpatialConstant β 2*parisiHJBGradientError β μ n) := by
    have hh := parisiGradientMesh_integral_le_full hs
      (curvatureGridError_intervalIntegrable β μ n 0 1) (curvatureGridError_nonneg β μ n)
    apply hh.trans_eq
    unfold curvatureGridError parisiCDFDistance
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
      ((parisiCDF_abs_diff_intervalIntegrable μ (parisiGridMeasure μ n) 0 1).const_mul _)
      intervalIntegrable_const,intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_const,sub_zero,one_smul]
  simp only [T,parisiGradientMeshTime_terminal n hs.2,parisiGradientMeshTime_zero n hs.1] at htel
  have hh : ‖(gridCurvatureMoment β hβ μ n 1-(∫t in s..1,S t))-
      gridCurvatureMoment β hβ μ n s‖ ≤
      2*β^2*((1+uniformSpatialConstant β 2)*parisiCDFDistance μ (parisiGridMeasure μ n)+
        uniformSpatialConstant β 2*parisiHJBGradientError β μ n) := by
    simpa only [F,T,parisiGradientMeshTime_terminal n hs.2,parisiGradientMeshTime_zero n hs.1,
      intervalIntegral.integral_same,sub_zero] using htel.trans hfull
  convert hh using 2
  ring

end FRSB
