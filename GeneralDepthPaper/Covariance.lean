module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section


/-! Actual finite mixed even-spin effective covariances, with positive coefficients.
No PDE or optimization assertion is included in the covariance data. -/
noncomputable section
open Set
open scoped BigOperators
namespace GeneralDepthPaper

structure AdmissibleCovariance where
  degrees : Finset ℕ
  nonempty : degrees.Nonempty
  coefficient : ℕ → ℝ
  coefficient_pos : ∀ p ∈ degrees, 0 < coefficient p
  degree_ge_two : ∀ p ∈ degrees, 2 ≤ p
  degree_even : ∀ p ∈ degrees, Even p

namespace AdmissibleCovariance

def value (Ξ : AdmissibleCovariance) (q : ℝ) : ℝ :=
  ∑ p ∈ Ξ.degrees, Ξ.coefficient p * q ^ p

def first (Ξ : AdmissibleCovariance) (q : ℝ) : ℝ :=
  ∑ p ∈ Ξ.degrees, Ξ.coefficient p * (p : ℝ) * q ^ (p-1)

def second (Ξ : AdmissibleCovariance) (q : ℝ) : ℝ :=
  ∑ p ∈ Ξ.degrees, Ξ.coefficient p * (p : ℝ) * ((p-1 : ℕ) : ℝ) * q ^ (p-2)

theorem hasDerivAt_value (Ξ : AdmissibleCovariance) (q : ℝ) :
    HasDerivAt Ξ.value (Ξ.first q) q := by
  unfold value first
  simpa [mul_assoc] using
    (HasDerivAt.fun_sum fun p (_hp : p ∈ Ξ.degrees) =>
      ((hasDerivAt_id q).pow p).const_mul (Ξ.coefficient p))

theorem hasDerivAt_first (Ξ : AdmissibleCovariance) (q : ℝ) :
    HasDerivAt Ξ.first (Ξ.second q) q := by
  have hn (p : ℕ) (hp : p ∈ Ξ.degrees) : p-1-1=p-2 := by omega
  unfold first second
  simpa [mul_assoc, Nat.sub_sub] using
    (HasDerivAt.fun_sum fun p (hp : p ∈ Ξ.degrees) =>
      ((hasDerivAt_id q).pow (p-1)).const_mul (Ξ.coefficient p * (p:ℝ)))

theorem continuous_value (Ξ : AdmissibleCovariance) : Continuous Ξ.value :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_id.pow _)

theorem continuous_first (Ξ : AdmissibleCovariance) : Continuous Ξ.first :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_id.pow _)

theorem continuous_second (Ξ : AdmissibleCovariance) : Continuous Ξ.second :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul (continuous_id.pow _)

@[simp] theorem value_zero (Ξ : AdmissibleCovariance) : Ξ.value 0 = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  have hn : p ≠ 0 := by have := Ξ.degree_ge_two p hp; omega
  simp [hn]

@[simp] theorem first_zero (Ξ : AdmissibleCovariance) : Ξ.first 0 = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  have hn : p-1 ≠ 0 := by have := Ξ.degree_ge_two p hp; omega
  simp [hn]

/-- The quadratic coefficient is retained in the revised model. -/
@[simp] theorem second_zero (Ξ : AdmissibleCovariance) :
    Ξ.second 0 = 2 * (if 2 ∈ Ξ.degrees then Ξ.coefficient 2 else 0) := by
  classical
  by_cases h2 : 2 ∈ Ξ.degrees
  · simp only [if_pos h2]
    unfold second
    rw [Finset.sum_eq_single 2]
    · norm_num
      ring
    · intro p hp hpn
      have hn : p - 2 ≠ 0 := by have := Ξ.degree_ge_two p hp; omega
      simp [hn]
    · exact fun hn => False.elim (hn h2)
  · simp only [if_neg h2, mul_zero]
    apply Finset.sum_eq_zero
    intro p hp
    have hpn : p ≠ 2 := by intro he; exact h2 (he ▸ hp)
    have hn : p - 2 ≠ 0 := by have := Ξ.degree_ge_two p hp; omega
    simp [hn]

def IsSubcritical (Ξ : AdmissibleCovariance) : Prop := Ξ.second 0 < 1

theorem value_even (Ξ : AdmissibleCovariance) (q : ℝ) : Ξ.value (-q)=Ξ.value q := by
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Ξ.degree_even p hp).neg_pow]

theorem first_nonneg (Ξ : AdmissibleCovariance) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ Ξ.first q := by
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (mul_nonneg (Ξ.coefficient_pos p hp).le (Nat.cast_nonneg p))
    (pow_nonneg hq _)

theorem second_nonneg (Ξ : AdmissibleCovariance) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ Ξ.second q := by
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (mul_nonneg (mul_nonneg (Ξ.coefficient_pos p hp).le
    (Nat.cast_nonneg p)) (Nat.cast_nonneg _)) (pow_nonneg hq _)

theorem first_pos (Ξ : AdmissibleCovariance) {q : ℝ} (hq : 0 < q) :
    0 < Ξ.first q := by
  apply Finset.sum_pos
  · intro p hp
    have hn : 0 < p := by have := Ξ.degree_ge_two p hp; omega
    exact mul_pos (mul_pos (Ξ.coefficient_pos p hp) (Nat.cast_pos.mpr hn)) (pow_pos hq _)
  · exact Ξ.nonempty

theorem second_pos (Ξ : AdmissibleCovariance) {q : ℝ} (hq : 0 < q) :
    0 < Ξ.second q := by
  apply Finset.sum_pos
  · intro p hp
    have hn : 0 < p := by have := Ξ.degree_ge_two p hp; omega
    have hn1 : 0 < p-1 := by have := Ξ.degree_ge_two p hp; omega
    exact mul_pos (mul_pos (mul_pos (Ξ.coefficient_pos p hp)
      (Nat.cast_pos.mpr hn)) (Nat.cast_pos.mpr hn1)) (pow_pos hq _)
  · exact Ξ.nonempty

theorem first_strictMonoOn (Ξ : AdmissibleCovariance) : StrictMonoOn Ξ.first (Ici 0) := by
  intro x hx y hy hxy
  apply Finset.sum_lt_sum
  · intro p hp
    have hn : p-1 ≠ 0 := by have := Ξ.degree_ge_two p hp; omega
    have hc : 0 < Ξ.coefficient p * (p:ℝ) := mul_pos (Ξ.coefficient_pos p hp)
      (Nat.cast_pos.mpr (by have := Ξ.degree_ge_two p hp; omega))
    exact (mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hxy hx hn) hc).le
  · obtain ⟨p,hp⟩ := Ξ.nonempty
    refine ⟨p,hp,?_⟩
    have hn : p-1 ≠ 0 := by have := Ξ.degree_ge_two p hp; omega
    exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hxy hx hn)
      (mul_pos (Ξ.coefficient_pos p hp)
        (Nat.cast_pos.mpr (by have := Ξ.degree_ge_two p hp; omega)))

/-- Total variance of the time-changed Gaussian driver. -/
def variance (Ξ : AdmissibleCovariance) : ℝ := Ξ.first 1

theorem variance_pos (Ξ : AdmissibleCovariance) : 0 < Ξ.variance :=
  Ξ.first_pos zero_lt_one

/-- Normalized variance clock; the original overlap coordinate is retained. -/
def clock (Ξ : AdmissibleCovariance) (q : ℝ) : ℝ := Ξ.first q / Ξ.variance

theorem continuous_clock (Ξ : AdmissibleCovariance) : Continuous Ξ.clock :=
  Ξ.continuous_first.div_const _

@[simp] theorem clock_zero (Ξ : AdmissibleCovariance) : Ξ.clock 0=0 := by simp [clock]
@[simp] theorem clock_one (Ξ : AdmissibleCovariance) : Ξ.clock 1=1 := by
  simp [clock,variance,ne_of_gt (Ξ.first_pos zero_lt_one)]

theorem clock_strictMonoOn (Ξ : AdmissibleCovariance) : StrictMonoOn Ξ.clock (Ici 0) := by
  intro x hx y hy hxy
  exact (div_lt_div_iff_of_pos_right Ξ.variance_pos).mpr (Ξ.first_strictMonoOn hx hy hxy)

theorem clock_mem_unit (Ξ : AdmissibleCovariance) {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) :
    Ξ.clock q ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact div_nonneg (Ξ.first_nonneg hq.1) Ξ.variance_pos.le
  · rw [← Ξ.clock_one]
    exact Ξ.clock_strictMonoOn.monotoneOn hq.1 (by norm_num) hq.2

theorem hasDerivAt_clock (Ξ : AdmissibleCovariance) (q : ℝ) :
    HasDerivAt Ξ.clock (Ξ.second q / Ξ.variance) q :=
  (Ξ.hasDerivAt_first q).div_const _

end AdmissibleCovariance
end GeneralDepthPaper
