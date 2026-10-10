module

public import FRSB.QuotientContinuity

@[expose] public section


/-! Exact differentiation of the moment quotient and its zero-time
 specialization. These algebra/calculus lemmas retain the actual moment
 derivative inputs explicitly. -/
noncomputable section
open Set
namespace FRSB

/-- The quotient rule gives the precise density numerator in Theorem 1.1;
 the cancellation uses A=2*alpha*B and both moment derivatives. -/
theorem moment_quotient_density_hasDerivWithinAt
    (A B : ℝ → ℝ) (β α AA CDD CCCC t : ℝ) (s : Set ℝ)
    (hB : B t ≠ 0) (hquot : A t = 2 * α * B t)
    (hA : HasDerivWithinAt A (β ^ 2 * (AA - 6 * α * CDD)) s t)
    (hBD : HasDerivWithinAt B (3 * β ^ 2 * (CDD - α * CCCC)) s t) :
    HasDerivWithinAt (fun r => A r / (2 * B r))
      (β ^ 2 * (AA - 12 * α * CDD + 6 * α ^ 2 * CCCC) / (2 * B t)) s t := by
  convert hA.div (hBD.const_mul 2) (mul_ne_zero (by norm_num) hB) using 1
  rw [hquot]
  field_simp
  ring

/-- At the origin, alpha=D=0 and C=1/beta reduce the density to the
 paper's beta^5 times the squared fourth jet, divided by two. -/
theorem quotient_density_at_zero (β U₄ : ℝ) (hβ : β ≠ 0) :
    β ^ 2 * U₄ ^ 2 / (2 * (1 / β) ^ 3) = β ^ 5 * U₄ ^ 2 / 2 := by
  field_simp

/-- The initial self-consistency identity picks the positive curvature
 root; the negative algebraic root is excluded by actual positive Hessian. -/
theorem curvature_at_zero_of_self_consistency (β C : ℝ)
    (hβ : 0 < β) (hC : 0 < C) (hself : β ^ 2 * C ^ 2 = 1) : C = 1 / β := by
  apply (eq_div_iff hβ.ne').mpr
  nlinarith [mul_pos hβ hC, sq_nonneg (β * C - 1)]

end FRSB
