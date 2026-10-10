module

public import DepthPaper.BivariateJetRegularity
public import DepthPaper.LargeVarianceMassDecay

@[expose] public section


/-! Actual spatial derivatives of the residual and their endpoint cancellation.
These identities are prerequisites for B.1, not its mixed error estimate. -/
noncomputable section
open Set
open scoped ContDiff
namespace DepthPaper

 def largeVarianceResidualSpatialJet (i:ℕ) (m x:ℝ):ℝ :=
   m^i*Real.exp (m*(x-Real.log 2))+(-m)^i*Real.exp (m*(-x-Real.log 2))-
     coshPowerSpatialJet i m x

 theorem hasDerivAt_largeVarianceResidualSpatialJet (i:ℕ) (m x:ℝ):
     HasDerivAt (largeVarianceResidualSpatialJet i m)
       (largeVarianceResidualSpatialJet (i+1) m x) x:=by
   have hplus:=(((hasDerivAt_id x).sub_const (Real.log 2)).const_mul m).exp.const_mul (m^i)
   have hminus:=((((hasDerivAt_id x).neg).sub_const (Real.log 2)).const_mul m).exp.const_mul ((-m)^i)
   have hh:=(hplus.add hminus).sub (hasDerivAt_coshPowerSpatialJet i m x)
   convert hh using 1
   · rfl
   · simp only [largeVarianceResidualSpatialJet,pow_succ,id_eq,Pi.neg_apply]
     ring

 theorem iteratedDeriv_largeVarianceResidual_spatial (i:ℕ) (m x:ℝ):
     iteratedDeriv i (largeVarianceResidual m) x=largeVarianceResidualSpatialJet i m x:=by
   induction i generalizing x with
   | zero=>
     rw [iteratedDeriv_zero,largeVarianceResidual_exp_terms]
     simp [largeVarianceResidualSpatialJet,coshPowerSpatialJet,coshPowerPolynomialAt_zero,coshPower]
   | succ i ih=>
     rw [iteratedDeriv_succ]
     have he:iteratedDeriv i (largeVarianceResidual m)=largeVarianceResidualSpatialJet i m:=funext ih
     rw [he]
     exact (hasDerivAt_largeVarianceResidualSpatialJet i m x).deriv

 theorem largeVarianceResidualSpatialJet_neg (i:ℕ) (m x:ℝ):
     largeVarianceResidualSpatialJet i m (-x)=(-1:ℝ)^i*largeVarianceResidualSpatialJet i m x:=by
   have he:(fun y=>largeVarianceResidual m (-y))=largeVarianceResidual m:=by
     funext y;exact largeVarianceResidual_even m y
   have hh:=iteratedDeriv_comp_neg i (largeVarianceResidual m) x
   rw [he,iteratedDeriv_largeVarianceResidual_spatial,iteratedDeriv_largeVarianceResidual_spatial] at hh
   have hsign:((-1:ℝ)^i)^2=1:=by rw [←pow_mul,mul_comm, pow_mul];norm_num
   have hh':=congrArg (fun r:ℝ=>(-1:ℝ)^i*r) hh
   simpa only [smul_eq_mul,←mul_assoc,←sq,hsign,one_mul] using hh'.symm

 theorem largeVarianceResidualSpatialJet_endpoint_decomposition (i:ℕ) (m x:ℝ):
     largeVarianceResidualSpatialJet i m x=m^i*largeVarianceResidual m x+
       ((-m)^i-m^i)*Real.exp (m*(-x-Real.log 2))-
         (Real.tanh x-1)*bivariateValue (coshPowerEndpointQuotient i) m (Real.tanh x)*coshPower m x:=by
   rw [largeVarianceResidualSpatialJet,largeVarianceResidual_exp_terms,
     coshPowerSpatialJet_endpoint_decomposition]
   unfold bivariateValue coshPower
   ring

 theorem contDiff_residual_mass (x:ℝ):ContDiff ℝ ∞ (fun m=>largeVarianceResidual m x):=by
   simp only [largeVarianceResidual_exp_terms]
   exact ((contDiff_id.mul contDiff_const).exp.add (contDiff_id.mul contDiff_const).exp).sub
     (contDiff_id.mul contDiff_const).exp

 theorem contDiff_coshPower_mass (x:ℝ):ContDiff ℝ ∞ (fun m=>coshPower m x):=by
   unfold coshPower
   exact (contDiff_id.mul contDiff_const).exp

 theorem contDiff_largeVarianceResidualSpatialJet_mass (i:ℕ) (x:ℝ):
     ContDiff ℝ ∞ (fun m=>largeVarianceResidualSpatialJet i m x):=by
   have hb:ContDiff ℝ ∞ (fun m=>bivariateValue (coshPowerPolynomial i) m (Real.tanh x)):=by
     have he:(fun m=>bivariateValue (coshPowerPolynomial i) m (Real.tanh x))=
       fun m=>bivariateMassJet (coshPowerPolynomial i) 0 m (Real.tanh x):=by
       funext m;simp [bivariateValue_sum,bivariateMassJet]
     rw [he]
     exact (contDiff_bivariateMassJet _ 0).comp (contDiff_id.prodMk contDiff_const)
   unfold largeVarianceResidualSpatialJet coshPowerSpatialJet coshPowerPolynomialAt
   exact (((contDiff_id.pow i).mul (contDiff_id.mul contDiff_const).exp).add
     ((contDiff_id.neg.pow i).mul (contDiff_id.mul contDiff_const).exp)).sub
       (hb.mul (contDiff_coshPower_mass x))

end DepthPaper
