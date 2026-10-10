module

public import GeneralDepthPaper.DoobKernelMeasures
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section


/-! Quantitative terminal heat-integral bounds for the actual normalized
Cole–Hopf kernels. These are the analytic estimates used in Lemma 4.3. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace GeneralDepthPaper
set_option maxHeartbeats 900000

theorem integrable_exp_neg_abs : Integrable (fun y:ℝ=>Real.exp (-|y|)) := by
  rw [←integrableOn_univ,←Iic_union_Ioi (a:=(0:ℝ)),integrableOn_union]
  constructor
  · exact (integrableOn_exp_Iic 0).congr_fun (fun y hy=>by
      rw [abs_of_nonpos hy];simp) measurableSet_Iic
  · exact (integrableOn_exp_neg_Ioi 0).congr_fun (fun y hy=>by
      rw [abs_of_nonneg hy.le]) measurableSet_Ioi

theorem integral_exp_neg_abs : (∫y:ℝ,Real.exp (-|y|))=2 := by
  change (∫y:ℝ,(fun x:ℝ=>Real.exp (-x)) |y|)=2
  calc
    _=2*(∫y:ℝ in Ioi 0,Real.exp (-y)):=integral_comp_abs (f:=fun y:ℝ=>Real.exp (-y))
    _=2:=by rw [integral_exp_neg_Ioi_zero];ring

theorem sech_le_two_exp_neg_abs (y:ℝ) : Paper.sech y≤2*Real.exp (-|y|) := by
  have hc:Real.exp |y|≤2*Real.cosh y := by
    rw [←Real.cosh_abs y,Real.cosh_eq]
    nlinarith [Real.exp_pos (-|y|)]
  rw [Paper.sech,div_le_iff₀ (Real.cosh_pos y)]
  have he:=mul_le_mul_of_nonneg_left hc (Real.exp_pos (-|y|)).le
  rw [←Real.exp_add,neg_add_cancel,Real.exp_zero] at he
  nlinarith

theorem terminalProfile_bounds {m:ℝ} (hm:0≤m) (hm1:m≤1) (y:ℝ) :
    0≤Paper.sech y^2*Real.cosh (m*y) ∧
      Paper.sech y^2*Real.cosh (m*y)≤2*Real.exp (-|y|) := by
  have hc:Real.cosh (m*y)≤Real.cosh y := Real.cosh_le_cosh.mpr (by
    rw [abs_mul,abs_of_nonneg hm]
    exact mul_le_of_le_one_left (abs_nonneg y) hm1)
  have hs:Paper.sech y^2*Real.cosh y=Paper.sech y := by
    unfold Paper.sech
    field_simp
  exact ⟨by positivity,(mul_le_mul_of_nonneg_left hc (sq_nonneg _)).trans
    (by rw [hs];exact sech_le_two_exp_neg_abs y)⟩

theorem integrable_terminalProfile {m:ℝ} (hm:0≤m) (hm1:m≤1) :
    Integrable (fun y=>Paper.sech y^2*Real.cosh (m*y)) := by
  apply (integrable_exp_neg_abs.const_mul 2).mono' (by unfold Paper.sech;fun_prop)
  exact .of_forall fun y=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (terminalProfile_bounds hm hm1 y).1]
    exact (terminalProfile_bounds hm hm1 y).2

theorem integral_terminalProfile_le_four {m:ℝ} (hm:0≤m) (hm1:m≤1) :
    (∫y,Paper.sech y^2*Real.cosh (m*y))≤4 := by
  have hh:=integral_mono (integrable_terminalProfile hm hm1)
    (integrable_exp_neg_abs.const_mul 2) (fun y=>(terminalProfile_bounds hm hm1 y).2)
  rw [integral_const_mul,integral_exp_neg_abs] at hh
  norm_num at hh ⊢
  exact hh

theorem integral_limitingDoobMeasure (m:ℝ) (W:ℝ≥0) (x:ℝ) (f:ℝ→ℝ) :
    (∫y,f y ∂limitingDoobMeasure m W x)=
      ∫y,f y*limitingDoobWeight m W x y ∂gaussianReal x W := by
  unfold limitingDoobMeasure
  rw [integral_withDensity_eq_integral_toReal_smul]
  · congr 1
    funext y
    rw [ENNReal.toReal_ofReal (limitingDoobWeight_pos m W x y).le,smul_eq_mul]
    ring
  · unfold limitingDoobWeight;fun_prop
  · exact .of_forall fun _=>ENNReal.ofReal_lt_top

theorem integrable_sech_sq_limitingDoobMeasure (m:ℝ) (W:ℝ≥0) (x:ℝ) :
    Integrable (fun y=>Paper.sech y^2) (limitingDoobMeasure m W x) := by
  letI:=isProbabilityMeasure_limitingDoobMeasure m W x
  exact (integrable_const (1:ℝ)).mono' ((show Continuous Paper.sech from continuous_iff_continuousAt.mpr (fun y=>(Paper.hasDerivAt_sech y).continuousAt)).pow 2).aestronglyMeasurable (.of_forall fun y=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact Paper.sech_sq_le_one y)

theorem gaussianPDFReal_le_normalization (x y:ℝ) (W:ℝ≥0) :
    gaussianPDFReal x W y≤(Real.sqrt (2*Real.pi*(W:ℝ)))⁻¹ := by
  unfold gaussianPDFReal
  apply mul_le_of_le_one_right (by positivity)
  rw [Real.exp_le_one_iff]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)

theorem limitingDoob_endpoint_upper {m:ℝ} (hm:0≤m) (hm1:m≤1)
    (W:ℝ≥0) (hW:W≠0) (x:ℝ) :
    (∫y,Paper.sech y^2 ∂limitingDoobMeasure m W x)≤
      4*(Real.sqrt (2*Real.pi*(W:ℝ)))⁻¹*Real.exp (-m^2*(W:ℝ)/2) := by
  rw [integral_limitingDoobMeasure,integral_gaussianReal_eq_integral_smul hW]
  have hi:=((integrable_terminalProfile hm hm1).const_mul
    ((Real.sqrt (2*Real.pi*(W:ℝ)))⁻¹*Real.exp (-m^2*(W:ℝ)/2)))
  have hbound:∀y,gaussianPDFReal x W y*(Paper.sech y^2*limitingDoobWeight m W x y)≤
      ((Real.sqrt (2*Real.pi*(W:ℝ)))⁻¹*Real.exp (-m^2*(W:ℝ)/2))*
        (Paper.sech y^2*Real.cosh (m*y)) := by
    intro y
    unfold limitingDoobWeight
    have hc:1≤Real.cosh (m*x):=Real.one_le_cosh _
    have hn:0≤Paper.sech y^2*Real.exp (-m^2*(W:ℝ)/2)*Real.cosh (m*y):=by positivity
    have hd:(Paper.sech y^2*Real.exp (-m^2*(W:ℝ)/2)*Real.cosh (m*y))/Real.cosh (m*x)≤
        Paper.sech y^2*Real.exp (-m^2*(W:ℝ)/2)*Real.cosh (m*y):=div_le_self hn hc
    have hp:=mul_le_mul_of_nonneg_left hd (gaussianPDFReal_nonneg x W y)
    have hg:=mul_le_mul_of_nonneg_right (gaussianPDFReal_le_normalization x y W) hn
    convert hp.trans hg using 1 <;> ring
  have hleft:Integrable (fun y=>gaussianPDFReal x W y*
      (Paper.sech y^2*limitingDoobWeight m W x y)) := by
    apply hi.mono' (by unfold limitingDoobWeight Paper.sech gaussianPDFReal;fun_prop)
    exact .of_forall fun y=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg x W y)
        (mul_nonneg (sq_nonneg _) (limitingDoobWeight_pos m W x y).le))]
      exact hbound y
  change (∫y,gaussianPDFReal x W y*(Paper.sech y^2*limitingDoobWeight m W x y))≤_
  have hh:=integral_mono hleft hi hbound
  rw [integral_const_mul] at hh
  have hg:=mul_le_mul_of_nonneg_left (integral_terminalProfile_le_four hm hm1)
    (by positivity : 0≤(Real.sqrt (2*Real.pi*(W:ℝ)))⁻¹*Real.exp (-m^2*(W:ℝ)/2))
  convert hh.trans hg using 1 <;> ring

end GeneralDepthPaper
