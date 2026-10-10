module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section


/-! Relative bounds on derivatives of a positive density give explicit
bounds on every positive-order derivative of its negative logarithm. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace FRSB

def negativeLogDerivativeConstant (L : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => L + L * ∑ i ∈ Finset.range n, (n.choose i : ℝ) * negativeLogDerivativeConstant L (min (i + 1) n)
termination_by n => n
decreasing_by omega

lemma negativeLogDerivativeConstant_succ (L : ℝ) (n : ℕ) :
    negativeLogDerivativeConstant L (n + 1) =
      L + L * ∑ i ∈ Finset.range n, (n.choose i : ℝ) * negativeLogDerivativeConstant L (i + 1) := by
  rw [negativeLogDerivativeConstant]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  rw [min_eq_left (by have hh := Finset.mem_range.mp hi; omega)]

theorem negativeLogDerivativeConstant_nonneg (L : ℝ) (hL : 0 ≤ L) (n : ℕ) :
    0 ≤ negativeLogDerivativeConstant L n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [negativeLogDerivativeConstant]
    | succ n =>
      rw [negativeLogDerivativeConstant_succ]
      apply add_nonneg hL
      apply mul_nonneg hL
      exact Finset.sum_nonneg (fun i hi => mul_nonneg (Nat.cast_nonneg _)
        (ih (i + 1) (by have hh := Finset.mem_range.mp hi; omega)))

lemma negativeLog_iteratedDeriv_recursion (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (hpos : ∀ x, 0 < F x) (n : ℕ) (x : ℝ) :
    iteratedDeriv (n + 1) (fun y => -Real.log (F y)) x * F x =
      -iteratedDeriv (n + 1) F x -
        ∑ i ∈ Finset.range n, (n.choose i : ℝ) *
          iteratedDeriv (i + 1) (fun y => -Real.log (F y)) x * iteratedDeriv (n - i) F x := by
  let W := fun y => -Real.log (F y)
  have hW : ContDiff ℝ ∞ W := (hF.log (fun y => (hpos y).ne')).neg
  have hder : deriv W * F = -(deriv F) := by
    funext y
    have hh := (hF.differentiable (by simp) y).hasDerivAt.log (hpos y).ne' |>.neg
    change deriv W y * F y = -deriv F y
    have hfun : (-fun y => Real.log (F y)) = W := by funext y; rfl
    rw [hfun] at hh
    have hwd : deriv W y = -(deriv F y / F y) := hh.deriv
    rw [hwd]
    field_simp [(hpos y).ne']
  have hh := congrArg (fun f => iteratedDeriv n f x) hder
  rw [iteratedDeriv_mul (((contDiff_infty_iff_deriv.mp hW).2).of_le (by simp)).contDiffAt
    (hF.of_le (by simp)).contDiffAt, iteratedDeriv_neg, ← iteratedDeriv_succ', Finset.sum_range_succ] at hh
  simp only [← iteratedDeriv_succ', Nat.choose_self, Nat.cast_one, one_mul,
    Nat.sub_self, iteratedDeriv_zero] at hh
  change _ = _
  linarith

set_option maxHeartbeats 1000000 in
/-- No positive lower bound for the density is needed: its relative
spatial derivative bounds suffice for all derivatives of -log F. -/
theorem norm_iteratedDeriv_negativeLog_le (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hpos : ∀ x, 0 < F x) (L : ℝ) (hL : 0 ≤ L) (k : ℕ)
    (hrelative : ∀ j ≤ k, ∀ x, ‖iteratedDeriv j F x‖ ≤ L * F x)
    (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) (x : ℝ) :
    ‖iteratedDeriv j (fun y => -Real.log (F y)) x‖ ≤ negativeLogDerivativeConstant L j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => omega
    | succ n =>
      have he := negativeLog_iteratedDeriv_recursion F hF hpos n x
      have hsum : ‖∑ i ∈ Finset.range n, (n.choose i : ℝ) *
          iteratedDeriv (i + 1) (fun y => -Real.log (F y)) x * iteratedDeriv (n - i) F x‖ ≤
          (L * ∑ i ∈ Finset.range n, (n.choose i : ℝ) * negativeLogDerivativeConstant L (i + 1)) * F x := by
        calc
          _ ≤ ∑ i ∈ Finset.range n, ‖(n.choose i : ℝ) *
              iteratedDeriv (i + 1) (fun y => -Real.log (F y)) x * iteratedDeriv (n - i) F x‖ := norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.range n, (n.choose i : ℝ) * negativeLogDerivativeConstant L (i + 1) * (L * F x) := by
            apply Finset.sum_le_sum
            intro i hi
            have hiN := Finset.mem_range.mp hi
            have hiC := negativeLogDerivativeConstant_nonneg L hL (i + 1)
            have hiW := ih (i + 1) (by omega) (by omega) (by omega)
            have hiF := hrelative (n - i) (by omega) x
            simp only [norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg _)]
            exact mul_le_mul (mul_le_mul_of_nonneg_left hiW (Nat.cast_nonneg _)) hiF
              (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hiC)
          _ = _ := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      have hh : ‖iteratedDeriv (n + 1) (fun y => -Real.log (F y)) x‖ * F x ≤
          negativeLogDerivativeConstant L (n + 1) * F x := by
        calc
          _ = ‖iteratedDeriv (n + 1) (fun y => -Real.log (F y)) x * F x‖ := by
            rw [norm_mul, Real.norm_of_nonneg (hpos x).le]
          _ ≤ ‖iteratedDeriv (n + 1) F x‖ + ‖∑ i ∈ Finset.range n, (n.choose i : ℝ) *
              iteratedDeriv (i + 1) (fun y => -Real.log (F y)) x * iteratedDeriv (n - i) F x‖ := by
            rw [he]
            simpa only [norm_neg] using norm_sub_le (-iteratedDeriv (n + 1) F x) _
          _ ≤ L * F x + (L * ∑ i ∈ Finset.range n, (n.choose i : ℝ) * negativeLogDerivativeConstant L (i + 1)) * F x :=
            add_le_add (hrelative (n + 1) hjk x) hsum
          _ = _ := by rw [negativeLogDerivativeConstant_succ]; ring
      exact (mul_le_mul_iff_left₀ (hpos x)).mp hh

end FRSB
