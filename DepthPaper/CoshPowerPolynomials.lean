module

public import DepthPaper.LargeVarianceMassJets
public import Paper.TanhPolynomial
public import Mathlib.Algebra.Polynomial.Derivative

@[expose] public section


/-! All spatial derivatives of cosh^m are controlled by actual bivariate
polynomials in mass and tanh. Endpoint values encode the cancellation needed
for the exponentially decaying residual in Appendix B.1. -/
noncomputable section
open scoped Polynomial
namespace DepthPaper

 def coshPowerPolynomial : ℕ→Polynomial (Polynomial ℝ)
 | 0=>1
 | i+1=>Polynomial.C Polynomial.X*Polynomial.X*coshPowerPolynomial i+
     (1-Polynomial.X^2)*(coshPowerPolynomial i).derivative

 def coshPowerPolynomialAt (i:ℕ) (m:ℝ):Polynomial ℝ :=
   (coshPowerPolynomial i).map (Polynomial.evalRingHom m)

 theorem coshPowerPolynomialAt_zero (m:ℝ):coshPowerPolynomialAt 0 m=1:=by
   simp [coshPowerPolynomialAt,coshPowerPolynomial]

 theorem coshPowerPolynomialAt_succ (i:ℕ) (m:ℝ):
     coshPowerPolynomialAt (i+1) m=Polynomial.C m*Polynomial.X*coshPowerPolynomialAt i m+
       (1-Polynomial.X^2)*(coshPowerPolynomialAt i m).derivative:=by
   simp [coshPowerPolynomialAt,coshPowerPolynomial,Polynomial.derivative_map]

 theorem coshPowerPolynomialAt_eval_one (i:ℕ) (m:ℝ):
     (coshPowerPolynomialAt i m).eval 1=m^i:=by
   induction i with
   | zero=>simp [coshPowerPolynomialAt_zero]
   | succ i ih=>
     rw [coshPowerPolynomialAt_succ]
     simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_sub,
       Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_pow]
     norm_num only
     rw [ih,pow_succ]
     ring

 theorem coshPowerPolynomialAt_eval_neg_one (i:ℕ) (m:ℝ):
     (coshPowerPolynomialAt i m).eval (-1)=(-m)^i:=by
   induction i with
   | zero=>simp [coshPowerPolynomialAt_zero]
   | succ i ih=>
     rw [coshPowerPolynomialAt_succ]
     simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_sub,
       Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_pow]
     norm_num only
     rw [ih,pow_succ]
     ring

 def coshPowerSpatialJet (i:ℕ) (m x:ℝ):ℝ :=
   (coshPowerPolynomialAt i m).eval (Real.tanh x)*coshPower m x

 theorem hasDerivAt_coshPower (m x:ℝ):
     HasDerivAt (coshPower m) (m*Real.tanh x*coshPower m x) x:=by
   have hh:=((Paper.hasDerivAt_log_cosh x).const_mul m).exp
   convert hh using 1
   · rfl
   · unfold coshPower
     ring

 theorem hasDerivAt_coshPowerSpatialJet (i:ℕ) (m x:ℝ):
     HasDerivAt (coshPowerSpatialJet i m) (coshPowerSpatialJet (i+1) m x) x:=by
   have hh:=(Paper.hasDerivAt_tanhPolynomial (coshPowerPolynomialAt i m) x).mul
     (hasDerivAt_coshPower m x)
   convert hh using 1
   · rfl
   · simp only [coshPowerSpatialJet,coshPowerPolynomialAt_succ,Paper.tanhPolynomialDeriv,
       Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_one,
       Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow]
     ring

 theorem iteratedDeriv_coshPower (i:ℕ) (m x:ℝ):
     iteratedDeriv i (coshPower m) x=coshPowerSpatialJet i m x:=by
   induction i generalizing x with
   | zero=>simp [coshPowerSpatialJet,coshPowerPolynomialAt_zero]
   | succ i ih=>
     rw [iteratedDeriv_succ]
     have he:iteratedDeriv i (coshPower m)=coshPowerSpatialJet i m:=funext ih
     rw [he]
     exact (hasDerivAt_coshPowerSpatialJet i m x).deriv

end DepthPaper
