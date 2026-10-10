module

public import FRSB.OptimalDiffusion
public import Mathlib.Algebra.MvPolynomial.PDeriv

@[expose] public section


/-! Actual polynomial moments and their universal Itô drift polynomials. -/
noncomputable section
open Set MeasureTheory MvPolynomial
open scoped BigOperators
namespace FRSB

/-- Variable `X j` stands for the positive-order spatial jet `U_(j+1)`. -/
abbrev MomentPolynomial := MvPolynomial ℕ ℝ

def momentPolynomialValue (β : ℝ) (μ : ParisiMeasure) (f : MomentPolynomial)
    (s : ℝ) (ω : BrownianSample) : ℝ :=
  MvPolynomial.eval (fun j => jetProcess β μ (j+1) s ω) f

def moment (β : ℝ) (μ : ParisiMeasure) (f : MomentPolynomial) (s : ℝ) : ℝ :=
  ∫ ω, momentPolynomialValue β μ f s ω ∂Paper.canonicalBrownianMeasure

/-- The diffusion covariance contribution. -/
def momentDrift0 (f : MomentPolynomial) : MomentPolynomial :=
  MvPolynomial.C (1/2 : ℝ) * ∑ i ∈ f.vars, ∑ j ∈ f.vars,
    MvPolynomial.pderiv j (MvPolynomial.pderiv i f) *
      MvPolynomial.X (i+1) * MvPolynomial.X (j+1)

/-- The differentiated nonlinear PDE contribution, after transport cancellation. -/
def momentDrift1 (f : MomentPolynomial) : MomentPolynomial :=
  MvPolynomial.C (-1/2 : ℝ) * ∑ j ∈ f.vars,
    MvPolynomial.pderiv j f * ∑ k ∈ Finset.Icc 1 j,
      MvPolynomial.C ((j+1).choose k : ℝ) * MvPolynomial.X k * MvPolynomial.X (j+1-k)

@[simp] theorem momentPolynomialValue_X (β : ℝ) (μ : ParisiMeasure) (j : ℕ)
    (s : ℝ) (ω : BrownianSample) :
    momentPolynomialValue β μ (MvPolynomial.X j) s ω = jetProcess β μ (j+1) s ω := by
  simp [momentPolynomialValue]

@[simp] theorem Gamma_eq_moment (β : ℝ) (μ : ParisiMeasure) (s : ℝ) :
    Gamma β μ s = moment β μ (MvPolynomial.X 0 ^ 2) s := by
  simp only [Gamma, moment, momentPolynomialValue, map_pow, eval_X, zero_add, M]

end FRSB
