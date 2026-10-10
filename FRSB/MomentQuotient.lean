module

public import FRSB.MomentPolynomials
public import FRSB.JetMomentContinuity
public import FRSB.OptimalCurvatureMoment
public import FRSB.BackwardsParity
public import FRSB.QuotientDensity

set_option backward.privateInPublic true

@[expose] public section


/-! Actual numerator and positive denominator of the density quotient,
with the polynomial generator computations and zero-field initial values. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial Paper
open scoped Topology BigOperators
namespace FRSB

def quotientNumeratorPolynomial : MomentPolynomial := X 2 ^ 2
def quotientDenominatorPolynomial : MomentPolynomial := X 1 ^ 3
def quotientNumerator (β : ℝ) (μ : ParisiMeasure) : ℝ → ℝ :=
  moment β μ quotientNumeratorPolynomial
def quotientDenominator (β : ℝ) (μ : ParisiMeasure) : ℝ → ℝ :=
  moment β μ quotientDenominatorPolynomial
def momentQuotient (β : ℝ) (μ : ParisiMeasure) (s : ℝ) : ℝ :=
  quotientNumerator β μ s / (2 * quotientDenominator β μ s)

@[simp] theorem moment_X_pow (β : ℝ) (μ : ParisiMeasure) (j n : ℕ) (s : ℝ) :
    moment β μ (X j ^ n) s =
      ∫ ω, jetProcess β μ (j+1) s ω ^ n ∂canonicalBrownianMeasure := by
  simp only [moment, momentPolynomialValue, map_pow, eval_X]

theorem continuousOn_quotientNumerator (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    ContinuousOn (quotientNumerator β μ) (Icc (0 : ℝ) 1) := by
  have he : quotientNumerator β μ = fun s =>
      ∫ ω, jetProcess β μ (2+1) s ω ^ 2 ∂canonicalBrownianMeasure :=
    funext (fun s => moment_X_pow β μ 2 2 s)
  rw [he]
  exact continuousOn_integral_jetProcess_pow β hβ μ 2 2

theorem continuousOn_quotientDenominator (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    ContinuousOn (quotientDenominator β μ) (Icc (0 : ℝ) 1) := by
  have he : quotientDenominator β μ = fun s =>
      ∫ ω, jetProcess β μ (1+1) s ω ^ 3 ∂canonicalBrownianMeasure :=
    funext (fun s => moment_X_pow β μ 1 3 s)
  rw [he]
  exact continuousOn_integral_jetProcess_pow β hβ μ 1 3

theorem quotientDenominator_pos (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : 0 < quotientDenominator β μ s := by
  simp only [quotientDenominator, quotientDenominatorPolynomial, moment_X_pow]
  apply (integral_pos_iff_support_of_nonneg (fun ω => (pow_pos (C_pos β μ hs ω) 3).le)
    (integrable_jetProcess_pow β hβ μ 1 3 hs)).mpr
  have he : Function.support (fun ω => C β μ s ω ^ 3) = univ := by
    ext ω
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (pow_pos (C_pos β μ hs ω) 3).ne'
  rw [he]
  simp

theorem quotientNumerator_nonneg (β : ℝ) (μ : ParisiMeasure) (s : ℝ) :
    0 ≤ quotientNumerator β μ s := by
  simp only [quotientNumerator, quotientNumeratorPolynomial, moment_X_pow]
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem continuousOn_momentQuotient (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    ContinuousOn (momentQuotient β μ) (Icc (0 : ℝ) 1) := by
  unfold momentQuotient
  apply (continuousOn_quotientNumerator β hβ μ).div
    (continuousOn_const.mul (continuousOn_quotientDenominator β hβ μ))
  intro s hs
  exact mul_ne_zero (by norm_num) (quotientDenominator_pos β hβ μ s hs).ne'

theorem jetProcess_three_initial_zero (β : ℝ) (μ : ParisiMeasure) (ω : BrownianSample) :
    jetProcess β μ 3 0 ω = 0 := by
  unfold jetProcess
  rw [optimalState_initial, parisiSpatialJet_eq_iteratedDeriv β μ 3 0 0 (by constructor <;> norm_num)]
  have hp := parisiPotential_iteratedDeriv_parity β μ 0 (by constructor <;> norm_num) 3 0
  norm_num at hp
  linarith

@[simp] theorem quotientNumerator_initial_zero (β : ℝ) (μ : ParisiMeasure) :
    quotientNumerator β μ 0 = 0 := by
  simp only [quotientNumerator, quotientNumeratorPolynomial, moment_X_pow,
    Nat.reduceAdd, jetProcess_three_initial_zero,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), integral_zero]

@[simp] theorem momentQuotient_initial_zero (β : ℝ) (μ : ParisiMeasure) :
    momentQuotient β μ 0 = 0 := by simp [momentQuotient]

private theorem vars_X_pow_singleton (j n : ℕ) (hn : n ≠ 0) :
    (X j ^ n : MomentPolynomial).vars = {j} := by
  rw [X_pow_eq_monomial, vars_monomial_single j hn one_ne_zero]

theorem eval_momentDrift0_quotientNumerator (r : ℕ → ℝ) :
    eval r (momentDrift0 quotientNumeratorPolynomial) = r 3 ^ 2 := by
  classical
  unfold momentDrift0 quotientNumeratorPolynomial
  rw [vars_X_pow_singleton 2 2 (by norm_num)]
  have hp : pderiv 2 (2 : MomentPolynomial) = 0 := by
    change pderiv 2 (MvPolynomial.C (2 : ℝ)) = 0
    exact pderiv_C
  simp [hp]
  ring

theorem eval_momentDrift1_quotientNumerator (r : ℕ → ℝ) :
    eval r (momentDrift1 quotientNumeratorPolynomial) = -6 * r 1 * r 2 ^ 2 := by
  classical
  unfold momentDrift1 quotientNumeratorPolynomial
  rw [vars_X_pow_singleton 2 2 (by norm_num)]
  norm_num [pderiv_pow, Finset.sum_Icc_succ_top]
  ring

theorem eval_momentDrift0_quotientDenominator (r : ℕ → ℝ) :
    eval r (momentDrift0 quotientDenominatorPolynomial) = 3 * r 1 * r 2 ^ 2 := by
  classical
  unfold momentDrift0 quotientDenominatorPolynomial
  rw [vars_X_pow_singleton 1 3 (by norm_num)]
  have hp : pderiv 1 (3 : MomentPolynomial) = 0 := by
    change pderiv 1 (MvPolynomial.C (3 : ℝ)) = 0
    exact pderiv_C
  simp [hp]
  ring

theorem eval_momentDrift1_quotientDenominator (r : ℕ → ℝ) :
    eval r (momentDrift1 quotientDenominatorPolynomial) = -3 * r 1 ^ 4 := by
  classical
  unfold momentDrift1 quotientDenominatorPolynomial
  rw [vars_X_pow_singleton 1 3 (by norm_num)]
  norm_num [pderiv_pow]
  ring

theorem momentDrift0_quotientNumerator_value (β : ℝ) (μ : ParisiMeasure) (s : ℝ) :
    moment β μ (momentDrift0 quotientNumeratorPolynomial) s =
      ∫ ω, A β μ s ω ^ 2 ∂canonicalBrownianMeasure := by
  unfold moment momentPolynomialValue
  apply integral_congr_ae
  exact .of_forall fun ω => eval_momentDrift0_quotientNumerator _

theorem momentDrift1_quotientNumerator_value (β : ℝ) (μ : ParisiMeasure) (s : ℝ) :
    moment β μ (momentDrift1 quotientNumeratorPolynomial) s =
      ∫ ω, -6 * C β μ s ω * D β μ s ω ^ 2 ∂canonicalBrownianMeasure := by
  unfold moment momentPolynomialValue
  apply integral_congr_ae
  exact .of_forall fun ω => eval_momentDrift1_quotientNumerator _

theorem momentDrift0_quotientDenominator_value (β : ℝ) (μ : ParisiMeasure) (s : ℝ) :
    moment β μ (momentDrift0 quotientDenominatorPolynomial) s =
      ∫ ω, 3 * C β μ s ω * D β μ s ω ^ 2 ∂canonicalBrownianMeasure := by
  unfold moment momentPolynomialValue
  apply integral_congr_ae
  exact .of_forall fun ω => eval_momentDrift0_quotientDenominator _

theorem momentDrift1_quotientDenominator_value (β : ℝ) (μ : ParisiMeasure) (s : ℝ) :
    moment β μ (momentDrift1 quotientDenominatorPolynomial) s =
      ∫ ω, -3 * C β μ s ω ^ 4 ∂canonicalBrownianMeasure := by
  unfold moment momentPolynomialValue
  apply integral_congr_ae
  exact .of_forall fun ω => eval_momentDrift1_quotientDenominator _

@[simp] theorem quotientDenominator_initial (β : ℝ) (μ : ParisiMeasure) :
    quotientDenominator β μ 0 = parisiHessian β μ (0, 0) ^ 3 := by
  simp only [quotientDenominator, quotientDenominatorPolynomial, moment_X_pow,
    Nat.reduceAdd, C_eq_hessian, optimalState_initial]
  simp

@[simp] theorem quotientFourthSquared_initial (β : ℝ) (μ : ParisiMeasure) :
    moment β μ (X 3 ^ 2) 0 = parisiSpatialJet β μ 4 0 0 ^ 2 := by
  simp only [moment_X_pow, Nat.reduceAdd, jetProcess, optimalState_initial]
  simp

end FRSB
