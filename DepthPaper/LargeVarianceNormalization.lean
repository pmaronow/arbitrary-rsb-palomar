module

public import Common.Mathlib.Probability.Distributions.Gaussian.ColeHopf
public import Paper.ParisiMildDerivative
public import Mathlib.Analysis.MeanInequalitiesPow

@[expose] public section


/-! Exact Gaussian normalization and the zeroth-order exponentially small
remainder in Appendix B.1. This module does not assert the mixed higher-order
parameter-derivative estimate of B.1; those estimates require further proofs. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open ColeHopfFoundation.ProbabilityTheory
open scoped NNReal
namespace DepthPaper

 def coshPower (m x : ℝ) : ℝ := Real.exp (m*Real.log (Real.cosh x))
 def largeVarianceMain (m : ℝ) (V : ℝ≥0) (x : ℝ) : ℝ :=
   Real.exp ((1-m)*Real.log 2+(V:ℝ)*m^2/2)*Real.cosh (m*x)
 def largeVarianceMoment (m : ℝ) (V : ℝ≥0) (x : ℝ) : ℝ :=
   ∫z,coshPower m (x+z) ∂gaussianReal 0 V
 def largeVarianceResidual (m x : ℝ) : ℝ :=
   2*Real.exp (-m*Real.log 2)*Real.cosh (m*x)-coshPower m x
 def largeVarianceError (m : ℝ) (V : ℝ≥0) (x : ℝ) : ℝ :=
   coleHopf m V (fun y=>Real.log (Real.cosh y)) x-
     (m*(V:ℝ)/2+(1/m-1)*Real.log 2+(1/m)*Real.log (Real.cosh (m*x)))

 theorem coshPower_exp_sum (m x : ℝ) :
     coshPower m x=Real.exp (-m*Real.log 2)*(Real.exp x+Real.exp (-x))^m := by
   unfold coshPower
   rw [Real.cosh_eq,Real.log_div (by positivity) (by norm_num),
     Real.rpow_def_of_pos (by positivity),←Real.exp_add]
   congr 1
   ring

 theorem coshPower_sum_upper {m : ℝ} (hm : 0 ≤ m) (hm1 : m ≤ 1) (x : ℝ) :
     coshPower m x ≤ 2*Real.exp (-m*Real.log 2)*Real.cosh (m*x) := by
   rw [coshPower_exp_sum]
   have he := Real.rpow_add_le_add_rpow (Real.exp_pos x).le (Real.exp_pos (-x)).le hm hm1
   rw [←Real.exp_mul,←Real.exp_mul] at he
   rw [mul_comm x m,show (-x)*m=-(m*x) by ring] at he
   have hh := mul_le_mul_of_nonneg_left he (Real.exp_pos (-m*Real.log 2)).le
   rw [Real.cosh_eq]
   convert hh using 1 <;> ring

 theorem largeVarianceResidual_bounds {m : ℝ} (hm : 0 ≤ m) (hm1 : m ≤ 1) (x : ℝ) :
     0 ≤ largeVarianceResidual m x ∧ largeVarianceResidual m x ≤ 1 := by
   refine ⟨sub_nonneg.mpr (coshPower_sum_upper hm hm1 x),?_⟩
   have hfactor : Real.exp (-m*Real.log 2) ≤ 1 := Real.exp_le_one_iff.mpr
     (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hm)
       (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)))
   have hl (a b : ℝ) : Real.exp (a*m) ≤ (Real.exp a+Real.exp b)^m := by
     rw [Real.exp_mul]
     exact Real.rpow_le_rpow (Real.exp_pos a).le (le_add_of_nonneg_right (Real.exp_pos b).le) hm
   rw [largeVarianceResidual,coshPower_exp_sum,Real.cosh_eq]
   rcases le_total 0 x with hx|hx
   · have he := mul_le_mul_of_nonneg_left (hl x (-x)) (Real.exp_pos (-m*Real.log 2)).le
     have hsmall : Real.exp ((-x)*m) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) hm)
     have hp := mul_le_mul hfactor hsmall (Real.exp_pos ((-x)*m)).le zero_le_one
     rw [show x*m=m*x by ring] at he
     rw [show (-x)*m=-(m*x) by ring] at hp
     simp only [one_mul] at hp
     nlinarith
   · have he := mul_le_mul_of_nonneg_left (hl (-x) x) (Real.exp_pos (-m*Real.log 2)).le
     rw [add_comm (Real.exp (-x)) (Real.exp x)] at he
     have hsmall : Real.exp (x*m) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hx hm)
     have hp := mul_le_mul hfactor hsmall (Real.exp_pos (x*m)).le zero_le_one
     rw [show (-x)*m=-(m*x) by ring] at he
     rw [show x*m=m*x by ring] at hp
     simp only [one_mul] at hp
     nlinarith

 theorem hasLinearGrowth_logCosh : HasLinearGrowth (fun y:ℝ=>Real.log (Real.cosh y)) := by
   refine ⟨0,1,zero_le_one,fun y=>?_⟩
   simpa only [zero_add,one_mul,Real.norm_eq_abs] using Paper.norm_logcosh_le_abs y

 theorem integrable_coshPower (m : ℝ) (V : ℝ≥0) (x : ℝ) :
     Integrable (fun z=>coshPower m (x+z)) (gaussianReal 0 V) :=
   integrable_exp_mul_comp_add hasLinearGrowth_logCosh (by fun_prop) m V x

 theorem integral_exp_affine_gaussian (m x : ℝ) (V : ℝ≥0) :
     (∫z,Real.exp (m*(x+z)) ∂gaussianReal 0 V)=Real.exp (m*x+(V:ℝ)*m^2/2) := by
   simp_rw [mul_add,Real.exp_add]
   rw [integral_const_mul]
   have he : (∫z,Real.exp (m*z) ∂gaussianReal 0 V)=Real.exp ((V:ℝ)*m^2/2) := by
     simpa only [mgf,zero_mul,zero_add,id_eq] using congrFun (mgf_id_gaussianReal (μ:=0) (v:=V)) m
   rw [he,←Real.exp_add]

 theorem integral_largeVarianceMain (m x : ℝ) (V : ℝ≥0) :
     (∫z,2*Real.exp (-m*Real.log 2)*Real.cosh (m*(x+z)) ∂gaussianReal 0 V)=
       largeVarianceMain m V x := by
   have hform (z:ℝ) : 2*Real.exp (-m*Real.log 2)*Real.cosh (m*(x+z))=
       Real.exp (-m*Real.log 2)*(Real.exp (m*(x+z))+Real.exp (-(m*(x+z)))) := by
     rw [Real.cosh_eq]
     ring
   simp_rw [hform]
   have h1 : Integrable (fun z=>Real.exp (m*(x+z))) (gaussianReal 0 V) := by
     simp_rw [mul_add,Real.exp_add]
     exact (integrable_exp_mul_gaussianReal m).const_mul _
   have h2 : Integrable (fun z=>Real.exp (-(m*(x+z)))) (gaussianReal 0 V) := by
     convert (integrable_exp_mul_comp_add (A:=fun y:ℝ=>y) (by
       exact ⟨0,1,zero_le_one,fun y=>by simp⟩) measurable_id (-m) V x) using 1 <;> ring
   rw [integral_const_mul,integral_add h1 h2,integral_exp_affine_gaussian]
   have he : (∫z,Real.exp (-(m*(x+z))) ∂gaussianReal 0 V)=Real.exp (-m*x+(V:ℝ)*m^2/2) := by
     simpa only [neg_mul,neg_sq] using integral_exp_affine_gaussian (-m) x V
   rw [he]
   unfold largeVarianceMain
   rw [Real.cosh_eq]
   rw [show (1-m)*Real.log 2+(V:ℝ)*m^2/2=Real.log 2+(-m*Real.log 2+(V:ℝ)*m^2/2) by ring]
   simp only [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
   rw [show -m*x=-(m*x) by ring]
   ring

 theorem largeVarianceMoment_deficit {m : ℝ} (hm : 0 ≤ m) (hm1 : m ≤ 1)
     (V : ℝ≥0) (x : ℝ) :
     0 ≤ largeVarianceMain m V x-largeVarianceMoment m V x ∧
       largeVarianceMain m V x-largeVarianceMoment m V x ≤ 1 := by
   have hres : Integrable (fun z=>largeVarianceResidual m (x+z)) (gaussianReal 0 V) := by
     apply (integrable_const (1:ℝ)).mono' (by
       unfold largeVarianceResidual coshPower
       fun_prop)
     exact .of_forall fun z=>by
       rw [Real.norm_of_nonneg (largeVarianceResidual_bounds hm hm1 _).1]
       exact (largeVarianceResidual_bounds hm hm1 _).2
   have hsum : Integrable (fun z=>2*Real.exp (-m*Real.log 2)*Real.cosh (m*(x+z))) (gaussianReal 0 V) := by
     convert hres.add (integrable_coshPower m V x) using 1
     funext z
     dsimp only [Pi.add_apply]
     unfold largeVarianceResidual
     ring
   have he : largeVarianceMain m V x-largeVarianceMoment m V x=
       ∫z,largeVarianceResidual m (x+z) ∂gaussianReal 0 V := by
     unfold largeVarianceResidual largeVarianceMoment
     rw [integral_sub hsum (integrable_coshPower m V x),integral_largeVarianceMain]
   rw [he]
   refine ⟨integral_nonneg (fun z=>(largeVarianceResidual_bounds hm hm1 _).1),?_⟩
   exact (integral_mono hres (integrable_const _) (fun z=>(largeVarianceResidual_bounds hm hm1 _).2)).trans_eq (by simp)

theorem coshPower_sum_lower {m : ℝ} (hm : 0 ≤ m) (x : ℝ) :
    2*Real.exp (-m*Real.log 2)*Real.cosh (m*x) ≤ 2*coshPower m x := by
  have h1 := Real.rpow_le_rpow (Real.exp_pos x).le
    (le_add_of_nonneg_right (Real.exp_pos (-x)).le) hm
  have h2 := Real.rpow_le_rpow (Real.exp_pos (-x)).le
    (le_add_of_nonneg_left (Real.exp_pos x).le) hm
  rw [←Real.exp_mul] at h1 h2
  rw [mul_comm x m] at h1
  rw [show (-x)*m=-(m*x) by ring] at h2
  rw [coshPower_exp_sum,Real.cosh_eq]
  have h := mul_le_mul_of_nonneg_left (add_le_add h1 h2)
    (Real.exp_pos (-m*Real.log 2)).le
  nlinarith

theorem largeVarianceMoment_main_bounds {m : ℝ} (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (V : ℝ≥0) (x : ℝ) :
    largeVarianceMain m V x/2 ≤ largeVarianceMoment m V x ∧
      largeVarianceMoment m V x ≤ largeVarianceMain m V x := by
  have hsum : Integrable (fun z=>2*Real.exp (-m*Real.log 2)*Real.cosh (m*(x+z)))
      (gaussianReal 0 V) := by
    have h1 : Integrable (fun z=>Real.exp (m*(x+z))) (gaussianReal 0 V) := by
      simp_rw [mul_add,Real.exp_add]
      exact (integrable_exp_mul_gaussianReal m).const_mul _
    have h2 : Integrable (fun z=>Real.exp (-m*(x+z))) (gaussianReal 0 V) := by
      simp_rw [mul_add,Real.exp_add]
      exact (integrable_exp_mul_gaussianReal (-m)).const_mul _
    convert (h1.add h2).const_mul (Real.exp (-m*Real.log 2)) using 1
    funext z
    dsimp only [Pi.add_apply]
    rw [Real.cosh_eq]
    rw [show -m*(x+z)=-(m*(x+z)) by ring]
    ring
  constructor
  · have hh := integral_mono hsum ((integrable_coshPower m V x).const_mul 2)
      (fun z=>coshPower_sum_lower hm (x+z))
    rw [integral_largeVarianceMain,integral_const_mul] at hh
    change _ ≤ 2*largeVarianceMoment m V x at hh
    linarith
  · exact sub_nonneg.mp (largeVarianceMoment_deficit hm hm1 V x).1

end DepthPaper
