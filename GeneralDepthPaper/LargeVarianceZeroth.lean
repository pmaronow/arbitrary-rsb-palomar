module

public import GeneralDepthPaper.LargeVarianceNormalization

@[expose] public section


/-! The actual Cole–Hopf expansion and a uniform-in-space zeroth-order error
estimate. Higher mixed parameter derivatives in Appendix B.1 are not asserted
by the zeroth-order theorem. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open ColeHopfFoundation.ProbabilityTheory
open scoped NNReal
namespace GeneralDepthPaper

 theorem largeVarianceMoment_pos (m : ℝ) (V : ℝ≥0) (x : ℝ) :
     0 < largeVarianceMoment m V x :=
   integral_exp_mul_comp_add_pos hasLinearGrowth_logCosh (by fun_prop) m V x

 theorem largeVarianceMain_pos (m : ℝ) (V : ℝ≥0) (x : ℝ) :
     0 < largeVarianceMain m V x := mul_pos (Real.exp_pos _) (Real.cosh_pos _)

 theorem largeVarianceMain_ge_exp {m : ℝ} (hm1 : m ≤ 1) (V : ℝ≥0) (x : ℝ) :
     Real.exp ((V:ℝ)*m^2/2) ≤ largeVarianceMain m V x := by
   have he : Real.exp ((V:ℝ)*m^2/2) ≤
       Real.exp ((1-m)*Real.log 2+(V:ℝ)*m^2/2) :=
     Real.exp_le_exp.mpr (le_add_of_nonneg_left
       (mul_nonneg (sub_nonneg.mpr hm1) (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))))
   exact he.trans (le_mul_of_one_le_right (Real.exp_pos _).le (Real.one_le_cosh _))

 theorem largeVarianceError_eq_log_ratio {m : ℝ} (hm : m ≠ 0) (V : ℝ≥0) (x : ℝ) :
     largeVarianceError m V x=(1/m)*Real.log (largeVarianceMoment m V x/largeVarianceMain m V x) := by
   unfold largeVarianceError
   rw [coleHopf_of_ne hm]
   change (1/m)*Real.log (largeVarianceMoment m V x)-_=_
   rw [Real.log_div (largeVarianceMoment_pos m V x).ne' (largeVarianceMain_pos m V x).ne']
   unfold largeVarianceMain
   rw [Real.log_mul (Real.exp_pos _).ne' (Real.cosh_pos _).ne',Real.log_exp]
   field_simp
   ring

 theorem coleHopf_largeVariance_expansion (m : ℝ) (V : ℝ≥0) (x : ℝ) :
     coleHopf m V (fun y=>Real.log (Real.cosh y)) x=
       m*(V:ℝ)/2+(1/m-1)*Real.log 2+(1/m)*Real.log (Real.cosh (m*x))+
         largeVarianceError m V x := by
   unfold largeVarianceError
   ring

 theorem largeVarianceError_zeroth_bound {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1)
     (V : ℝ≥0) (hV : 2 ≤ Real.exp ((V:ℝ)*m^2/2)) (x : ℝ) :
     |largeVarianceError m V x| ≤ (2/m)*Real.exp (-(V:ℝ)*m^2/2) := by
   have hD := largeVarianceMoment_deficit hm.le hm1 V x
   have hH := largeVarianceMoment_pos m V x
   have hM := largeVarianceMain_pos m V x
   have hMexp := largeVarianceMain_ge_exp hm1 V x
   have h2 : 2 ≤ largeVarianceMain m V x := hV.trans hMexp
   have hhalf : largeVarianceMain m V x/2 ≤ largeVarianceMoment m V x := by linarith
   have hlog : 0 ≤ Real.log (largeVarianceMain m V x)-Real.log (largeVarianceMoment m V x) :=
     sub_nonneg.mpr (Real.log_le_log hH (sub_nonneg.mp hD.1))
   have hlogbound := Real.log_le_sub_one_of_pos (div_pos hM hH)
   rw [Real.log_div hM.ne' hH.ne'] at hlogbound
   have hb : (Real.log (largeVarianceMain m V x)-Real.log (largeVarianceMoment m V x))*
       largeVarianceMoment m V x ≤ 1 := by
     have hh := (le_div_iff₀ hH).mp (show
       Real.log (largeVarianceMain m V x)-Real.log (largeVarianceMoment m V x) ≤
         (largeVarianceMain m V x-largeVarianceMoment m V x)/largeVarianceMoment m V x by
       simpa only [sub_div,div_self hH.ne'] using hlogbound)
     exact hh.trans hD.2
   have hb2 : Real.log (largeVarianceMain m V x)-Real.log (largeVarianceMoment m V x) ≤
       2/largeVarianceMain m V x := by
     apply (le_div_iff₀ hM).mpr
     nlinarith [mul_le_mul_of_nonneg_left hhalf hlog]
   have hb3 : 2/largeVarianceMain m V x ≤ 2*Real.exp (-(V:ℝ)*m^2/2) := by
     calc
       _ ≤ 2/Real.exp ((V:ℝ)*m^2/2) := div_le_div_of_nonneg_left (by norm_num) (Real.exp_pos _) hMexp
       _ = _ := by rw [div_eq_mul_inv,←Real.exp_neg];congr 1;ring
   rw [largeVarianceError_eq_log_ratio hm.ne' V x,
     Real.log_div hH.ne' hM.ne',abs_mul,abs_of_pos (one_div_pos.mpr hm),
     abs_of_nonpos (by linarith)]
   have hh := mul_le_mul_of_nonneg_left (hb2.trans hb3) (one_div_pos.mpr hm).le
   convert hh using 1 <;> ring

end GeneralDepthPaper
