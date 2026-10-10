module

public import GeneralDepthPaper.DoobEndpointIntegralBounds

@[expose] public section


/-! A uniform lower terminal heat-integral bound on every fixed compact
set of starting states, using the literal Gaussian transition density. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace GeneralDepthPaper
set_option maxHeartbeats 900000

def doobCompactLowerConstant (R:ℝ) : ℝ :=
  2*Real.exp (-(R+1)^2/2)*Paper.sech 1^2/Real.cosh R

theorem doobCompactLowerConstant_pos (R:ℝ) : 0<doobCompactLowerConstant R := by
  unfold doobCompactLowerConstant Paper.sech
  positivity

theorem integrable_limitingEndpointDensity (m:ℝ) (W:ℝ≥0) (hW:W≠0) (x:ℝ) :
    Integrable (fun y=>gaussianPDFReal x W y*
      (Paper.sech y^2*limitingDoobWeight m W x y)) := by
  have hi:=integrable_sech_sq_limitingDoobMeasure m W x
  unfold limitingDoobMeasure at hi
  have hwm:Measurable (fun y=>ENNReal.ofReal (limitingDoobWeight m W x y)):=by
    unfold limitingDoobWeight;fun_prop
  have hg:Integrable (fun y=>Paper.sech y^2*limitingDoobWeight m W x y)
      (gaussianReal x W) := by
    have hh:=(integrable_withDensity_iff hwm (.of_forall fun _=>ENNReal.ofReal_lt_top)).mp hi
    simpa only [ENNReal.toReal_ofReal (limitingDoobWeight_pos m W x _).le] using hh
  rw [gaussianReal_of_var_ne_zero x hW] at hg
  have hh:=(integrable_withDensity_iff (measurable_gaussianPDF x W)
    (.of_forall fun _=>gaussianPDF_lt_top)).mp hg
  convert hh using 1
  funext y
  rw [toReal_gaussianPDF]
  ring

theorem gaussianPDFReal_lower_on_compact {R x y:ℝ} (hR:0≤R)
    (hx:|x|≤R) (hy:y∈Icc (-1:ℝ) 1) (W:ℝ≥0) (hW:1≤(W:ℝ)) :
    (Real.sqrt (2*Real.pi*(W:ℝ)))⁻¹*Real.exp (-(R+1)^2/2)≤gaussianPDFReal x W y := by
  have habs:|y-x|≤R+1 := by
    have hyabs:|y|≤1:=abs_le.mpr hy
    exact (abs_sub y x).trans (by linarith)
  have hsq:(y-x)^2≤(R+1)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) habs 2
  have he:-(R+1)^2/2≤-(y-x)^2/(2*(W:ℝ)) := by
    apply (le_div_iff₀ (by linarith : 0<2*(W:ℝ))).mpr
    nlinarith [sq_nonneg (R+1),mul_nonneg (sq_nonneg (R+1)) (sub_nonneg.mpr hW)]
  unfold gaussianPDFReal
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)

theorem limitingDoob_endpoint_lower {m R x:ℝ} (hm:0≤m) (hm1:m≤1)
    (hR:0≤R) (hx:|x|≤R) (W:ℝ≥0) (hW:1≤(W:ℝ)) :
    doobCompactLowerConstant R*(Real.sqrt (2*Real.pi*(W:ℝ)))⁻¹*
      Real.exp (-m^2*(W:ℝ)/2)≤
      ∫y,Paper.sech y^2 ∂limitingDoobMeasure m W x := by
  have hWne:W≠0 := by intro hh;subst W;norm_num at hW
  let K:ℝ := (Real.sqrt (2*Real.pi*(W:ℝ)))⁻¹*Real.exp (-(R+1)^2/2)*
    Paper.sech 1^2*Real.exp (-m^2*(W:ℝ)/2)/Real.cosh R
  have hn:∀y,0≤gaussianPDFReal x W y*(Paper.sech y^2*limitingDoobWeight m W x y):=by
    intro y
    exact mul_nonneg (gaussianPDFReal_nonneg x W y)
      (mul_nonneg (sq_nonneg _) (limitingDoobWeight_pos m W x y).le)
  have hb:∀y∈Icc (-1:ℝ) 1,K≤gaussianPDFReal x W y*
      (Paper.sech y^2*limitingDoobWeight m W x y) := by
    intro y hy
    have hpdf0:=gaussianPDFReal_nonneg x W y
    have hexp0:=(Real.exp_pos (-m^2*(W:ℝ)/2)).le
    have hs0:=sq_nonneg (Paper.sech y)
    have hinv0:=(inv_pos.mpr (Real.cosh_pos (m*x))).le
    have hc:Real.cosh y≤Real.cosh 1:=Real.cosh_le_cosh.mpr (by
      simpa only [abs_one] using (abs_le.mpr hy))
    have hs:Paper.sech 1≤Paper.sech y:=by
      unfold Paper.sech
      exact one_div_le_one_div_of_le (Real.cosh_pos y) hc
    have hss:Paper.sech 1^2≤Paper.sech y^2:=pow_le_pow_left₀ (Paper.sech_pos _).le hs 2
    have hmx:Real.cosh (m*x)≤Real.cosh R:=Real.cosh_le_cosh.mpr (by
      rw [abs_mul,abs_of_nonneg hm,abs_of_nonneg hR]
      exact (mul_le_of_le_one_left (abs_nonneg x) hm1).trans hx)
    have hci:(Real.cosh R)⁻¹≤(Real.cosh (m*x))⁻¹:=
      inv_anti₀ (Real.cosh_pos (m*x)) hmx
    have hg:=gaussianPDFReal_lower_on_compact hR hx hy W hW
    have hp:=mul_le_mul hg hss (sq_nonneg _) (by positivity)
    have hc1:1≤Real.cosh (m*y):=Real.one_le_cosh _
    have hp2:=mul_le_mul_of_nonneg_right hp (Real.exp_pos (-m^2*(W:ℝ)/2)).le
    have hp3:=mul_le_mul hp2 hci (by positivity)
      (by positivity : 0≤gaussianPDFReal x W y*Paper.sech y^2*Real.exp (-m^2*(W:ℝ)/2))
    have hp4:=mul_le_mul_of_nonneg_left hc1 (by positivity :
      0≤gaussianPDFReal x W y*Paper.sech y^2*Real.exp (-m^2*(W:ℝ)/2)*(Real.cosh (m*x))⁻¹)
    unfold K limitingDoobWeight
    convert hp3.trans (by simpa only [mul_one] using hp4) using 1 <;> ring
  have hi:=integrable_limitingEndpointDensity m W hWne x
  have hh:=setIntegral_mono_on (integrable_const K) hi.integrableOn measurableSet_Icc hb
  have hh2:=setIntegral_le_integral hi (.of_forall hn) (s:=Icc (-1:ℝ) 1)
  have hc:(∫_y:ℝ in Icc (-1:ℝ) 1,K)=2*K:=by
    norm_num [MeasureTheory.integral_const,measureReal_def,Real.volume_Icc]
  rw [hc] at hh
  rw [integral_limitingDoobMeasure,integral_gaussianReal_eq_integral_smul hWne]
  change _≤∫y,gaussianPDFReal x W y*(Paper.sech y^2*limitingDoobWeight m W x y)
  convert hh.trans hh2 using 1
  unfold doobCompactLowerConstant K
  ring

end GeneralDepthPaper
