module

public import DepthPaper.DoobEndpointLowerBound

@[expose] public section


/-! The Appendix B.2 measure comparison transfers quantitative terminal
estimates to the genuine Cole–Hopf transition. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace DepthPaper

theorem integrable_sech_sq_terminalDoobMeasure (m:ℝ) (W:ℝ≥0) (x:ℝ) :
    Integrable (fun y=>Paper.sech y^2) (terminalDoobMeasure m W W x) := by
  letI:=isProbabilityMeasure_terminalDoobMeasure m W W le_rfl x
  exact (integrable_const (1:ℝ)).mono'
    ((show Continuous Paper.sech from continuous_iff_continuousAt.mpr
      (fun y=>(Paper.hasDerivAt_sech y).continuousAt)).pow 2).aestronglyMeasurable
      (.of_forall fun y=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact Paper.sech_sq_le_one y)

theorem terminalDoob_endpoint_comparison {m:ℝ} (hm:0 < m) (hm1:m≤1)
    (W:ℝ≥0) (x:ℝ) :
    (1/2)*(∫y,Paper.sech y^2 ∂limitingDoobMeasure m W x)≤
      (∫y,Paper.sech y^2 ∂terminalDoobMeasure m W W x) ∧
    (∫y,Paper.sech y^2 ∂terminalDoobMeasure m W W x)≤
      2*(∫y,Paper.sech y^2 ∂limitingDoobMeasure m W x) := by
  have hh:=terminalDoobMeasure_comparison_two hm hm1 W W le_rfl x
  constructor
  · have hi:=integrable_sech_sq_terminalDoobMeasure m W x
    have h:=integral_mono_measure hh.1 (.of_forall fun y=>sq_nonneg (Paper.sech y)) hi
    simpa only [integral_smul_measure,ENNReal.toReal_div,ENNReal.toReal_one,
      ENNReal.toReal_ofNat,ENNReal.toReal_inv,smul_eq_mul,one_div] using h
  · have hi:=(integrable_sech_sq_limitingDoobMeasure m W x).smul_measure
      (c:=(2:ℝ≥0∞)) (by norm_num)
    have h:=integral_mono_measure hh.2 (.of_forall fun y=>sq_nonneg (Paper.sech y)) hi
    simpa only [integral_smul_measure,ENNReal.toReal_ofNat,smul_eq_mul] using h

theorem terminalDoob_endpoint_upper {m:ℝ} (hm:0 < m) (hm1:m≤1)
    (W:ℝ≥0) (hW:W≠0) (x:ℝ) :
    (∫y,Paper.sech y^2 ∂terminalDoobMeasure m W W x)≤
      8*(Real.sqrt (2*Real.pi*(W:ℝ)))⁻¹*Real.exp (-m^2*(W:ℝ)/2) := by
  have hh:=(terminalDoob_endpoint_comparison hm hm1 W x).2
  have hu:=mul_le_mul_of_nonneg_left (limitingDoob_endpoint_upper hm.le hm1 W hW x)
    (by norm_num : (0:ℝ)≤2)
  convert hh.trans hu using 1 <;> ring

theorem terminalDoob_endpoint_lower {m R x:ℝ} (hm:0 < m) (hm1:m≤1)
    (hR:0≤R) (hx:|x|≤R) (W:ℝ≥0) (hW:1≤(W:ℝ)) :
    (1/2)*doobCompactLowerConstant R*(Real.sqrt (2*Real.pi*(W:ℝ)))⁻¹*
      Real.exp (-m^2*(W:ℝ)/2)≤
      ∫y,Paper.sech y^2 ∂terminalDoobMeasure m W W x := by
  have hl:=mul_le_mul_of_nonneg_left (limitingDoob_endpoint_lower hm.le hm1 hR hx W hW)
    (by norm_num : (0:ℝ)≤1/2)
  have hh:=(terminalDoob_endpoint_comparison hm hm1 W x).1
  convert hl.trans hh using 1 <;> ring

end DepthPaper
