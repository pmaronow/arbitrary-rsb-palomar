module

public import DepthPaper.DoobEndpointComparison
public import FRSB.ConstantMassKernel

@[expose] public section


/-! Averaging the terminal transition estimates over an arbitrary genuine
probability law with uniformly positive compact mass. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace DepthPaper
open ColeHopfFoundation.ProbabilityTheory

def terminalEndpointDeficit (m:ℝ) (W:ℝ≥0) (x:ℝ):ℝ :=
  ∫y,Paper.sech y^2 ∂terminalDoobMeasure m W W x

theorem terminalDoobMeasure_terminal_eq_kernel (m:ℝ) (W:ℝ≥0) (x:ℝ):
    terminalDoobMeasure m W W x=FRSB.constantMassKernel m W
      (fun y=>Real.log (Real.cosh y)) x := by
  rw [FRSB.constantMassKernel_apply m W _
    (Real.continuous_cosh.log (fun y=>(Real.cosh_pos y).ne')) hasLinearGrowth_logCosh x,
    terminalDoobMeasure_eq_constantMass m W W le_rfl x]
  congr 2
  funext y
  simp only [terminalDoobPotential,tsub_self,coleHopf_zero_var]

theorem stronglyMeasurable_terminalEndpointDeficit (m:ℝ) (W:ℝ≥0):
    StronglyMeasurable (terminalEndpointDeficit m W) := by
  have hf:Measurable (fun y=>Paper.sech y^2):=by unfold Paper.sech;fun_prop
  have hh:=FRSB.stronglyMeasurable_integral_constantMassKernel m W
    (fun y=>Real.log (Real.cosh y))
    (Real.continuous_cosh.log (fun y=>(Real.cosh_pos y).ne'))
    hasLinearGrowth_logCosh (fun y=>Paper.sech y^2) hf
  convert hh using 1
  funext x
  rw [terminalEndpointDeficit,terminalDoobMeasure_terminal_eq_kernel]

theorem terminalEndpointDeficit_nonneg (m:ℝ) (W:ℝ≥0) (x:ℝ):
    0≤terminalEndpointDeficit m W x:=integral_nonneg (fun y=>sq_nonneg _)

theorem terminalEndpointDeficit_le_one (m:ℝ) (W:ℝ≥0) (x:ℝ):
    terminalEndpointDeficit m W x≤1:=by
  letI:=isProbabilityMeasure_terminalDoobMeasure m W W le_rfl x
  have hh:=integral_mono (integrable_sech_sq_terminalDoobMeasure m W x)
    (integrable_const (1:ℝ)) (fun y=>Paper.sech_sq_le_one y)
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,terminalEndpointDeficit] using hh

theorem integrable_terminalEndpointDeficit (m:ℝ) (W:ℝ≥0)
    (ρ:Measure ℝ) [IsFiniteMeasure ρ]:Integrable (terminalEndpointDeficit m W) ρ:=
  (integrable_const (1:ℝ)).mono' (stronglyMeasurable_terminalEndpointDeficit m W).aestronglyMeasurable
    (.of_forall fun x=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (terminalEndpointDeficit_nonneg m W x)]
      exact terminalEndpointDeficit_le_one m W x)

theorem terminalEndpointDeficit_average_upper {m:ℝ} (hm:0 < m) (hm1:m≤1)
    (W:ℝ≥0) (hW:W≠0) (ρ:Measure ℝ) [IsProbabilityMeasure ρ]:
    (∫x,terminalEndpointDeficit m W x ∂ρ)≤
      8*(Real.sqrt (2*Real.pi*(W:ℝ)))⁻¹*Real.exp (-m^2*(W:ℝ)/2):=by
  have hh:=integral_mono (integrable_terminalEndpointDeficit m W ρ)
    (integrable_const (8*(Real.sqrt (2*Real.pi*(W:ℝ)))⁻¹*Real.exp (-m^2*(W:ℝ)/2)))
      (fun x=>terminalDoob_endpoint_upper hm hm1 W hW x)
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,terminalEndpointDeficit] using hh

theorem terminalEndpointDeficit_average_lower {m R:ℝ} (hm:0 < m) (hm1:m≤1)
    (hR:0≤R) (W:ℝ≥0) (hW:1≤(W:ℝ)) (ρ:Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ:(1/2:ℝ)≤ρ.real (Icc (-R) R)):
    (1/4)*doobCompactLowerConstant R*(Real.sqrt (2*Real.pi*(W:ℝ)))⁻¹*
      Real.exp (-m^2*(W:ℝ)/2)≤∫x,terminalEndpointDeficit m W x ∂ρ := by
  let K:ℝ:=(1/2)*doobCompactLowerConstant R*(Real.sqrt (2*Real.pi*(W:ℝ)))⁻¹*
    Real.exp (-m^2*(W:ℝ)/2)
  have hK:0≤K:=by dsimp [K];have:= (doobCompactLowerConstant_pos R).le;positivity
  have hh:=setIntegral_mono_on (integrable_const K)
    (integrable_terminalEndpointDeficit m W ρ).integrableOn measurableSet_Icc
      (fun x hx=>terminalDoob_endpoint_lower hm hm1 hR (abs_le.mpr hx) W hW)
  have hh2:=setIntegral_le_integral (integrable_terminalEndpointDeficit m W ρ)
    (.of_forall fun x=>terminalEndpointDeficit_nonneg m W x) (s:=Icc (-R) R)
  have hlo:=mul_le_mul_of_nonneg_right hρ hK
  rw [integral_const,smul_eq_mul,measureReal_restrict_apply_univ] at hh
  convert (hlo.trans hh).trans hh2 using 1
  dsimp [K]
  ring

end DepthPaper
