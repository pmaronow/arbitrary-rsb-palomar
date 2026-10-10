module

public import GeneralDepthPaper.Covariance
public import FourPapersCommon.RateClock

@[expose] public section

/-! The literal physical-overlap volatility `sqrt (Ξ''(q))` for every
finite positive even covariance, including both a retained quadratic term
and vanishing volatility at the origin. No Brownian or stochastic-integral
representation is assumed in this deterministic interface. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology NNReal
namespace GeneralDepthPaper
open FourPapersCommon

/-- The actual covariance rate, in nonnegative physical overlap time. -/
def physicalCovarianceRate (Ξ : AdmissibleCovariance) : NonnegativeRate where
  rate t := Ξ.second t
  continuous_rate := Ξ.continuous_second.comp NNReal.continuous_coe
  nonneg t := Ξ.second_nonneg t.coe_nonneg

/-- The square-root volatility in the manuscript's physical-time SDE. -/
def physicalVolatility (Ξ : AdmissibleCovariance) (t : ℝ≥0) : ℝ :=
  rateVolatility (physicalCovarianceRate Ξ) t

theorem physicalVolatility_eq (Ξ : AdmissibleCovariance) (t : ℝ≥0) :
    physicalVolatility Ξ t = Real.sqrt (Ξ.second t) := rfl

theorem continuous_physicalVolatility (Ξ : AdmissibleCovariance) :
    Continuous (physicalVolatility Ξ) :=
  continuous_rateVolatility (physicalCovarianceRate Ξ)

theorem physicalVolatility_nonneg (Ξ : AdmissibleCovariance) (t : ℝ≥0) :
    0 ≤ physicalVolatility Ξ t := Real.sqrt_nonneg _

theorem physicalVolatility_sq (Ξ : AdmissibleCovariance) (t : ℝ≥0) :
    (physicalVolatility Ξ t)^2 = Ξ.second t :=
  rateVolatility_sq (physicalCovarianceRate Ξ) t

theorem physicalVolatility_pos (Ξ : AdmissibleCovariance) {t : ℝ≥0} (ht : 0<t) :
    0 < physicalVolatility Ξ t :=
  Real.sqrt_pos.mpr (Ξ.second_pos (by exact_mod_cast ht))

theorem physicalVolatility_zero_eq (Ξ : AdmissibleCovariance) :
    physicalVolatility Ξ 0 =
      Real.sqrt (2 * (if 2 ∈ Ξ.degrees then Ξ.coefficient 2 else 0)) := by
  rw [physicalVolatility_eq, NNReal.coe_zero, Ξ.second_zero]

theorem physicalCovarianceSecond_monotone (Ξ : AdmissibleCovariance) :
    Monotone (fun t : ℝ≥0 => Ξ.second t) := by
  intro s t hst
  unfold AdmissibleCovariance.second
  apply Finset.sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ s.coe_nonneg (NNReal.coe_le_coe.mpr hst) (p-2))
    (mul_nonneg (mul_nonneg (Ξ.coefficient_pos p hp).le (Nat.cast_nonneg p))
      (Nat.cast_nonneg (p-1)))

theorem physicalVolatility_monotone (Ξ : AdmissibleCovariance) :
    Monotone (physicalVolatility Ξ) := by
  intro s t hst
  exact Real.sqrt_le_sqrt (physicalCovarianceSecond_monotone Ξ hst)

theorem physicalVolatility_le_one (Ξ : AdmissibleCovariance) {t : ℝ≥0} (ht : t≤1) :
    physicalVolatility Ξ t ≤ Real.sqrt (Ξ.second 1) := by
  simpa only [physicalVolatility_eq, NNReal.coe_one] using
    physicalVolatility_monotone Ξ ht

theorem physicalCovarianceRate_clock (Ξ : AdmissibleCovariance) (t : ℝ≥0) :
    (rateClock (physicalCovarianceRate Ξ) t : ℝ) = Ξ.first t := by
  change (∫ s in (0:ℝ)..(t:ℝ), Ξ.second (s.toNNReal:ℝ)) = Ξ.first t
  calc
    _ = ∫ s in (0:ℝ)..(t:ℝ), Ξ.second s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le t.coe_nonneg] at hs
      dsimp only
      rw [Real.coe_toNNReal _ hs.1]
    _ = Ξ.first t - Ξ.first 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s _ => Ξ.hasDerivAt_first s) (Ξ.continuous_second.intervalIntegrable _ _)
    _ = Ξ.first t := by rw [Ξ.first_zero, sub_zero]

/-- Exact normalization of the square-root physical volatility; no
strictly positive origin-rate assumption is required. -/
theorem integral_physicalVolatility_sq (Ξ : AdmissibleCovariance) (t : ℝ≥0) :
    (∫ s in Ioc (0:ℝ≥0) t, (physicalVolatility Ξ s)^2
      ∂nonnegativeLebesgueMeasure) = Ξ.first t := by
  unfold physicalVolatility
  rw [←rateClock_eq_volatility_integral (physicalCovarianceRate Ξ) t]
  exact physicalCovarianceRate_clock Ξ t

end GeneralDepthPaper
