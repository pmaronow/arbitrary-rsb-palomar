module

public import DepthPaper.CoshPowerPolynomials

@[expose] public section


/-! Actual polynomial factorization of the spatial cosh-power jets at tanh=1.
The factor is constructed recursively; no divisibility conclusion is assumed. -/
noncomputable section
open scoped Polynomial
namespace DepthPaper

 def coshPowerEndpointQuotient : ℕ→Polynomial (Polynomial ℝ)
 | 0=>0
 | i+1=>Polynomial.C (Polynomial.X^(i+1))+
     (Polynomial.C Polynomial.X*Polynomial.X-(Polynomial.X+1))*coshPowerEndpointQuotient i+
       (1-Polynomial.X^2)*(coshPowerEndpointQuotient i).derivative

 theorem coshPowerPolynomial_factor (i:ℕ) :
     coshPowerPolynomial i=Polynomial.C (Polynomial.X^i)+
       (Polynomial.X-1)*coshPowerEndpointQuotient i := by
   induction i with
   | zero=>simp [coshPowerPolynomial,coshPowerEndpointQuotient]
   | succ i ih=>
     rw [coshPowerPolynomial,ih,coshPowerEndpointQuotient]
     simp only [Polynomial.derivative_add,Polynomial.derivative_C,Polynomial.derivative_mul,
       Polynomial.derivative_sub,Polynomial.derivative_X,Polynomial.derivative_one,sub_zero,
       one_mul,zero_add]
     simp only [pow_succ,Polynomial.C_mul,Polynomial.C_pow]
     ring

 theorem coshPowerPolynomialAt_factor (i:ℕ) (m:ℝ):
     coshPowerPolynomialAt i m=Polynomial.C (m^i)+
       (Polynomial.X-1)*(coshPowerEndpointQuotient i).map (Polynomial.evalRingHom m) := by
   unfold coshPowerPolynomialAt
   rw [coshPowerPolynomial_factor]
   simp

 theorem coshPowerSpatialJet_endpoint_decomposition (i:ℕ) (m x:ℝ):
     coshPowerSpatialJet i m x=m^i*coshPower m x+
       (Real.tanh x-1)*((coshPowerEndpointQuotient i).map (Polynomial.evalRingHom m)).eval
         (Real.tanh x)*coshPower m x := by
   unfold coshPowerSpatialJet
   rw [coshPowerPolynomialAt_factor]
   simp only [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,
     Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_one]
   ring

end DepthPaper
