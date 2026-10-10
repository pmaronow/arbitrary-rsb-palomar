module

public import DepthPaper.LargeVarianceNormalization
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section


/-! Actual derivatives in the mass parameter of the Cole–Hopf residual.
These identities are prerequisites for B.1; uniform all-order error estimates
are not inferred from smoothness alone. -/
noncomputable section
open Set
open scoped ContDiff
namespace DepthPaper

 def largeVarianceResidualMassJet (j:ℕ) (m x:ℝ):ℝ :=
   (x-Real.log 2)^j*Real.exp (m*(x-Real.log 2))+
     (-x-Real.log 2)^j*Real.exp (m*(-x-Real.log 2))-
       Real.log (Real.cosh x)^j*Real.exp (m*Real.log (Real.cosh x))

 theorem largeVarianceResidual_exp_terms (m x:ℝ) :
     largeVarianceResidual m x=Real.exp (m*(x-Real.log 2))+
       Real.exp (m*(-x-Real.log 2))-Real.exp (m*Real.log (Real.cosh x)) := by
   unfold largeVarianceResidual coshPower
   rw [Real.cosh_eq]
   simp only [mul_sub,mul_neg,neg_mul,Real.exp_sub,Real.exp_neg]
   ring

 theorem hasDerivAt_largeVarianceResidualMassJet (j:ℕ) (m x:ℝ) :
     HasDerivAt (fun r=>largeVarianceResidualMassJet j r x)
       (largeVarianceResidualMassJet (j+1) m x) m := by
   have hd (a:ℝ):HasDerivAt (fun r=>a^j*Real.exp (r*a))
       (a^(j+1)*Real.exp (m*a)) m:=by
     have hh:=((hasDerivAt_id m).mul_const a).exp.const_mul (a^j)
     convert hh using 1 <;> simp [pow_succ,mul_assoc,mul_comm,mul_left_comm]
   exact (hd (x-Real.log 2)).add (hd (-x-Real.log 2)) |>.sub (hd (Real.log (Real.cosh x)))

 theorem iteratedDeriv_largeVarianceResidual_mass (j:ℕ) (m x:ℝ) :
     iteratedDeriv j (fun r=>largeVarianceResidual r x) m=
       largeVarianceResidualMassJet j m x := by
   induction j generalizing m with
   | zero => simp only [iteratedDeriv_zero];rw [largeVarianceResidual_exp_terms];simp only [largeVarianceResidualMassJet,pow_zero,one_mul]
   | succ j ih =>
     rw [iteratedDeriv_succ]
     have he:iteratedDeriv j (fun r=>largeVarianceResidual r x)=
         fun r=>largeVarianceResidualMassJet j r x:=funext ih
     rw [he]
     exact (hasDerivAt_largeVarianceResidualMassJet j m x).deriv

 theorem largeVarianceResidual_even (m x:ℝ) : largeVarianceResidual m (-x)=largeVarianceResidual m x := by
   simp only [largeVarianceResidual,coshPower,mul_neg,Real.cosh_neg]

 theorem largeVarianceResidualMassJet_even (j:ℕ) (m x:ℝ) :
     largeVarianceResidualMassJet j m (-x)=largeVarianceResidualMassJet j m x := by
   unfold largeVarianceResidualMassJet
   simp only [neg_neg,Real.cosh_neg]
   ring

 theorem logCosh_positive_asymptotic (x:ℝ) :
     Real.log (Real.cosh x)=x-Real.log 2+Real.log (1+Real.exp (-2*x)) := by
   have hc:Real.cosh x=Real.exp x/2*(1+Real.exp (-2*x)):=by
     rw [Real.cosh_eq]
     have he:Real.exp x*Real.exp (-2*x)=Real.exp (-x):=by
       rw [←Real.exp_add];congr 1;ring
     calc
       (Real.exp x+Real.exp (-x))/2=(Real.exp x+Real.exp x*Real.exp (-2*x))/2:=by rw [he]
       _=Real.exp x/2*(1+Real.exp (-2*x)):=by ring
   rw [hc,Real.log_mul (by positivity) (by positivity),
     Real.log_div (Real.exp_pos x).ne' (by norm_num),Real.log_exp]

 theorem logCosh_positive_gap_bounds (x:ℝ) :
     0≤Real.log (Real.cosh x)-(x-Real.log 2) ∧
       Real.log (Real.cosh x)-(x-Real.log 2)≤Real.exp (-2*x) := by
   rw [logCosh_positive_asymptotic]
   have hg:0≤Real.log (1+Real.exp (-2*x)):=Real.log_nonneg (by linarith [Real.exp_pos (-2*x)])
   have hu:=Real.log_le_sub_one_of_pos (show 0<1+Real.exp (-2*x) by positivity)
   constructor <;> linarith

end DepthPaper
