module

public import DepthPaper.DoobEndpointAverageBounds

@[expose] public section


/-! The uniform heat-smoothing estimate for the scaled hyperbolic secant,
at every elapsed time of the actual terminal transition. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace DepthPaper

theorem integrable_scaledSech_sq_limitingDoobMeasure (m:ℝ) (t:ℝ≥0) (x:ℝ):
    Integrable (fun y=>Paper.sech (m*y)^2) (limitingDoobMeasure m t x):=by
  letI:=isProbabilityMeasure_limitingDoobMeasure m t x
  apply (integrable_const (1:ℝ)).mono'
    (((show Continuous Paper.sech from continuous_iff_continuousAt.mpr
      (fun y=>(Paper.hasDerivAt_sech y).continuousAt)).comp
        (continuous_const.mul continuous_id)).pow 2).aestronglyMeasurable
  exact .of_forall fun y=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact Paper.sech_sq_le_one _

theorem limitingDoob_scaledSech_upper (m:ℝ) (t:ℝ≥0) (x:ℝ):
    (∫y,Paper.sech (m*y)^2 ∂limitingDoobMeasure m t x)≤Real.exp (-m^2*(t:ℝ)/2):=by
  rw [integral_limitingDoobMeasure]
  have he:(fun y=>Paper.sech (m*y)^2*limitingDoobWeight m t x y)=
      (fun y=>(Real.exp (-m^2*(t:ℝ)/2)/Real.cosh (m*x))*Paper.sech (m*y)):=by
    funext y
    unfold Paper.sech limitingDoobWeight
    field_simp
  rw [he,integral_const_mul]
  have hi:Integrable (fun y=>Paper.sech (m*y)) (gaussianReal x t):=by
    apply (integrable_const (1:ℝ)).mono'
      ((show Continuous Paper.sech from continuous_iff_continuousAt.mpr
        (fun y=>(Paper.hasDerivAt_sech y).continuousAt)).comp
          (continuous_const.mul continuous_id)).aestronglyMeasurable
    exact .of_forall fun y=>by
      change ‖Paper.sech (m*y)‖≤1
      rw [Real.norm_eq_abs,abs_of_nonneg (Paper.sech_pos _).le]
      exact Paper.sech_le_one _
  have hh:=integral_mono hi (integrable_const (1:ℝ)) (fun y=>Paper.sech_le_one (m*y))
  have hb:(∫y,Paper.sech (m*y) ∂gaussianReal x t)≤1:=by simpa using hh
  have hs:=mul_le_mul_of_nonneg_left hb (by positivity :
    0≤Real.exp (-m^2*(t:ℝ)/2)/Real.cosh (m*x))
  have hs2:(Real.exp (-m^2*(t:ℝ)/2)/Real.cosh (m*x))*
    (∫y,Paper.sech (m*y) ∂gaussianReal x t)≤Real.exp (-m^2*(t:ℝ)/2)/Real.cosh (m*x):=by
    simpa only [mul_one] using hs
  exact hs2.trans
    (div_le_self (Real.exp_pos _).le (Real.one_le_cosh _))

theorem terminalDoob_scaledSech_upper {m:ℝ} (hm:0 < m) (hm1:m≤1)
    (W t:ℝ≥0) (ht:t≤W) (x:ℝ):
    (∫y,Paper.sech (m*y)^2 ∂terminalDoobMeasure m W t x)≤
      2*Real.exp (-m^2*(t:ℝ)/2):=by
  have hi:=(integrable_scaledSech_sq_limitingDoobMeasure m t x).smul_measure
    (c:=(2:ℝ≥0∞)) (by norm_num)
  have hh:=integral_mono_measure (terminalDoobMeasure_comparison_two hm hm1 W t ht x).2
    (.of_forall fun y=>sq_nonneg (Paper.sech (m*y))) hi
  have he:=mul_le_mul_of_nonneg_left (limitingDoob_scaledSech_upper m t x) (by norm_num : (0:ℝ)≤2)
  simp only [integral_smul_measure,ENNReal.toReal_ofNat,smul_eq_mul] at hh
  exact hh.trans he

end DepthPaper
