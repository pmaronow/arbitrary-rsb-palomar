module

public import FourPapersCommon.ParisiGradientL1State
public import Paper.HJBGridCells

set_option backward.privateInPublic true

@[expose] public section


/-! The actual uniform-grid CDF distance converges to the original distance.
Within a common grid cell its Lebesgue integral is the cell length times the
actual mass difference. Endpoint atoms are retained by the grid measures;
only the null endpoints of the time integral are omitted in the cell proof. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace FourPapersCommon
open Paper

private theorem gridDistance_triangle (μ ν τ : ParisiMeasure) :
    parisiCDFDistance μ τ ≤ parisiCDFDistance μ ν + parisiCDFDistance ν τ := by
  have hi := parisiCDF_difference_intervalIntegrable μ ν 0 1
  have hj := parisiCDF_difference_intervalIntegrable ν τ 0 1
  have hk := parisiCDF_difference_intervalIntegrable μ τ 0 1
  have hh := intervalIntegral.integral_mono_on zero_le_one hk (hi.add hj)
    (fun x _ => norm_sub_le_norm_sub_add_norm_sub
      (parisiCDF μ x) (parisiCDF ν x) (parisiCDF τ x))
  rw [intervalIntegral.integral_add hi hj] at hh
  exact hh

private theorem gridDistance_symm (μ ν : ParisiMeasure) :
    parisiCDFDistance μ ν = parisiCDFDistance ν μ := by
  unfold parisiCDFDistance
  apply intervalIntegral.integral_congr
  intro x _
  exact norm_sub_rev _ _

/-- Quantitative convergence uses the true upward-rounding CDF errors of
both probability measures, including their endpoint atoms. -/
theorem parisiCDFDistance_grid_pair_norm_le (μ ν : ParisiMeasure) (n : ℕ) :
    ‖parisiCDFDistance (parisiGridMeasure μ n) (parisiGridMeasure ν n) -
      parisiCDFDistance μ ν‖ ≤ 2 / (n + 1 : ℕ) := by
  have hμ := parisiCDF_grid_norm_integral_le μ n
  have hν := parisiCDF_grid_norm_integral_le ν n
  change parisiCDFDistance μ (parisiGridMeasure μ n) ≤ 1 / (n + 1 : ℕ) at hμ
  change parisiCDFDistance ν (parisiGridMeasure ν n) ≤ 1 / (n + 1 : ℕ) at hν
  have h₁ := gridDistance_triangle (parisiGridMeasure μ n) μ (parisiGridMeasure ν n)
  have h₂ := gridDistance_triangle μ ν (parisiGridMeasure ν n)
  have h₃ := gridDistance_triangle μ (parisiGridMeasure μ n) ν
  have h₄ := gridDistance_triangle (parisiGridMeasure μ n) (parisiGridMeasure ν n) ν
  rw [gridDistance_symm (parisiGridMeasure μ n) μ] at h₁
  rw [gridDistance_symm (parisiGridMeasure ν n) ν] at h₄
  have hmesh : (2 : ℝ) / (n + 1 : ℕ) =
      1 / (n + 1 : ℕ) + 1 / (n + 1 : ℕ) := by ring
  rw [hmesh, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

theorem tendsto_parisiCDFDistance_grid_pair (μ ν : ParisiMeasure) :
    Tendsto (fun n : ℕ =>
      parisiCDFDistance (parisiGridMeasure μ n) (parisiGridMeasure ν n))
      atTop (𝓝 (parisiCDFDistance μ ν)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => parisiCDFDistance_grid_pair_norm_le μ ν n)
  have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  simpa only [Nat.cast_add, Nat.cast_one, mul_one_div, mul_zero] using hh

/-- Exact CDF-distance integral on any ordered subinterval of a common
uniform-grid cell. Both CDFs equal their actual scheme masses in its interior. -/
theorem parisiCDFDistance_grid_cell_integral (μ ν : ParisiMeasure)
    (n i : ℕ) (hi : i < n + 1) (a b : ℝ) (hab : a ≤ b)
    (ha : hjbGridTime n i ≤ a) (hb : b ≤ hjbGridTime n (i + 1)) :
    (∫ t in a..b, ‖parisiCDF (parisiGridMeasure μ n) t -
      parisiCDF (parisiGridMeasure ν n) t‖) =
      (b - a) * |(parisiGridRSBScheme μ n).m (i + 1) -
        (parisiGridRSBScheme ν n).m (i + 1)| := by
  have heq : EqOn
      (fun t => ‖parisiCDF (parisiGridMeasure μ n) t -
        parisiCDF (parisiGridMeasure ν n) t‖)
      (fun _ => |(parisiGridRSBScheme μ n).m (i + 1) -
        (parisiGridRSBScheme ν n).m (i + 1)|) (uIoo a b) := by
    intro t ht
    rw [uIoo_of_le hab] at ht
    have htμ : t ∈ Ico ((parisiGridRSBScheme μ n).q (i + 1))
        ((parisiGridRSBScheme μ n).q ((i + 1) + 1)) := by
      obtain ⟨hq₀, hq₁⟩ := hjbGrid_cell_q μ n i hi
      simpa only [show i + 1 + 1 = i + 2 by omega, hq₀, hq₁] using
        (show t ∈ Ico (hjbGridTime n i) (hjbGridTime n (i + 1)) from
          ⟨ha.trans ht.1.le, ht.2.trans_le hb⟩)
    have htν : t ∈ Ico ((parisiGridRSBScheme ν n).q (i + 1))
        ((parisiGridRSBScheme ν n).q ((i + 1) + 1)) := by
      obtain ⟨hq₀, hq₁⟩ := hjbGrid_cell_q ν n i hi
      simpa only [show i + 1 + 1 = i + 2 by omega, hq₀, hq₁] using
        (show t ∈ Ico (hjbGridTime n i) (hjbGridTime n (i + 1)) from
          ⟨ha.trans ht.1.le, ht.2.trans_le hb⟩)
    change ‖parisiCDF (parisiGridMeasure μ n) t -
      parisiCDF (parisiGridMeasure ν n) t‖ = _
    rw [parisiCDF_grid_eq_scheme_mass μ n (i + 1) (by omega) (by omega) htμ,
      parisiCDF_grid_eq_scheme_mass ν n (i + 1) (by omega) (by omega) htν,
      Real.norm_eq_abs]
  rw [intervalIntegral.integral_congr_uIoo heq, intervalIntegral.integral_const,
    smul_eq_mul]

end FourPapersCommon
