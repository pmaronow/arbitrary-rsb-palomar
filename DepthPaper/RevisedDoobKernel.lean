module

public import DepthPaper.TerminalDoobLaw
public import FRSB.ConstantMassKernel

@[expose] public section

/-! The literal finite-horizon Cole--Hopf kernel, moving Gaussian mixture,
and one-quarter/four comparison in revised Appendix C.3. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace DepthPaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 64

def revisedDoobKernel (m : ℝ) (W t : ℝ≥0) : Kernel ℝ ℝ :=
  FRSB.constantMassKernel m t (terminalDoobPotential m W t)

def revisedLimitingDoobDensity (m : ℝ) (t : ℝ≥0) (x y : ℝ) : ℝ :=
  gaussianPDFReal x t y * Real.exp (-m^2*(t:ℝ)/2) * Real.cosh (m*y) / Real.cosh (m*x)

theorem revised_gaussian_exponential_tilt (k x y : ℝ) (t : ℝ≥0) (ht : 0<t) :
    gaussianPDFReal x t y * Real.exp (k*y-k^2*(t:ℝ)/2) =
      Real.exp (k*x) * gaussianPDFReal (x+k*(t:ℝ)) t y := by
  unfold gaussianPDFReal
  calc
    _ = (Real.sqrt (2*Real.pi*(t:ℝ)))⁻¹ *
        Real.exp (-(y-x)^2/(2*(t:ℝ))+(k*y-k^2*(t:ℝ)/2)) := by
      rw [mul_assoc,←Real.exp_add]
    _ = (Real.sqrt (2*Real.pi*(t:ℝ)))⁻¹ *
        Real.exp (k*x + -(y-(x+k*(t:ℝ)))^2/(2*(t:ℝ))) := by
      congr 1
      congr 1
      field_simp [show (t:ℝ)≠0 from ne_of_gt ht]
      ring
    _ = _ := by rw [Real.exp_add];ring

theorem revisedLimitingDoobDensity_moving_gaussians
    (m : ℝ) (t : ℝ≥0) (ht : 0<t) (x y : ℝ) :
    revisedLimitingDoobDensity m t x y =
      (Real.exp (m*x)*gaussianPDFReal (x+m*(t:ℝ)) t y +
        Real.exp (-m*x)*gaussianPDFReal (x-m*(t:ℝ)) t y)/(2*Real.cosh (m*x)) := by
  unfold revisedLimitingDoobDensity
  have hp : Real.exp (-m^2*(t:ℝ)/2)*Real.exp (m*y)=Real.exp (m*y-m^2*(t:ℝ)/2) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have hn : Real.exp (-m^2*(t:ℝ)/2)*Real.exp (-m*y)=Real.exp (-m*y-m^2*(t:ℝ)/2) := by
    rw [←Real.exp_add]
    congr 1
    ring
  calc
    _ = (gaussianPDFReal x t y*(Real.exp (-m^2*(t:ℝ)/2)*Real.exp (m*y))+
        gaussianPDFReal x t y*(Real.exp (-m^2*(t:ℝ)/2)*Real.exp (-m*y)))/(2*Real.cosh (m*x)) := by
      rw [Real.cosh_eq]
      simp only [neg_mul]
      ring
    _ = (gaussianPDFReal x t y*Real.exp (m*y-m^2*(t:ℝ)/2)+
        gaussianPDFReal x t y*Real.exp (-m*y-m^2*(t:ℝ)/2))/(2*Real.cosh (m*x)) := by
      rw [hp,hn]
    _ = _ := by
      rw [revised_gaussian_exponential_tilt m x y t ht]
      have H := revised_gaussian_exponential_tilt (-m) x y t ht
      have Hn : gaussianPDFReal x t y*Real.exp (-m*y-m^2*(t:ℝ)/2)=
          Real.exp (-m*x)*gaussianPDFReal (x-m*(t:ℝ)) t y := by
        convert! H using 1 <;> congr 1 <;> ring
      rw [Hn]

theorem revised_limitingDoobMeasure_eq_density (m : ℝ) (t : ℝ≥0) (ht : 0<t) (x : ℝ) :
    limitingDoobMeasure m t x =
      volume.withDensity (fun y => ENNReal.ofReal (revisedLimitingDoobDensity m t x y)) := by
  rw [limitingDoobMeasure,gaussianReal_of_var_ne_zero x ht.ne',
    ←withDensity_mul volume (measurable_gaussianPDF x t)
      ((by unfold limitingDoobWeight;fun_prop : Measurable (limitingDoobWeight m t x)).ennreal_ofReal)]
  congr 1
  funext y
  change ENNReal.ofReal (gaussianPDFReal x t y)*ENNReal.ofReal (limitingDoobWeight m t x y)=_
  rw [←ENNReal.ofReal_mul (gaussianPDFReal_nonneg x t y)]
  congr 1
  unfold limitingDoobWeight revisedLimitingDoobDensity
  ring

theorem revisedDoobKernel_eq_terminalDoobMeasure (m : ℝ) (W t : ℝ≥0)
    (htW : t≤W) (x : ℝ) : revisedDoobKernel m W t x=terminalDoobMeasure m W t x := by
  rw [revisedDoobKernel,FRSB.constantMassKernel_apply m t _
    (by
      change Continuous (fun y => ColeHopfFoundation.ProbabilityTheory.coleHopf m (W-t)
        (fun z => Real.log (Real.cosh z)) y)
      simpa only [Real.toNNReal_coe,Function.comp_def,id_eq] using
        (ColeHopfFoundation.ProbabilityTheory.continuous_coleHopf
          (Real.continuous_cosh.log fun z => (Real.cosh_pos z).ne') hasLinearGrowth_logCosh m).comp
          (continuous_id.prodMk (continuous_const (y:=((W-t:ℝ≥0):ℝ)))))
    (ColeHopfFoundation.ProbabilityTheory.HasLinearGrowth.of_lipschitz (terminalDoobPotential_lipschitz m W t)),
    terminalDoobMeasure_eq_constantMass m W t htW x]

/-- Full kernel-only statement of revised Lemma C.3, including both density
expressions, probability normalization, and literal measure bounds. -/
theorem revised_doob_kernel {m : ℝ} (hm : 0 < m) (hm1 : m≤1)
    (W : ℝ≥0) (hW : 0<W) (t : ℝ≥0) (ht : 0<t) (htW : t≤W) (x : ℝ) :
    revisedDoobKernel m W t x = volume.withDensity (fun y => ENNReal.ofReal
      (gaussianPDFReal x t y*Real.exp (m*terminalDoobPotential m W t y)/
        Real.exp (m*terminalDoobPotential m W 0 x))) ∧
    limitingDoobMeasure m t x = volume.withDensity (fun y => ENNReal.ofReal
      ((Real.exp (m*x)*gaussianPDFReal (x+m*(t:ℝ)) t y+
        Real.exp (-m*x)*gaussianPDFReal (x-m*(t:ℝ)) t y)/(2*Real.cosh (m*x)))) ∧
    IsProbabilityMeasure (revisedDoobKernel m W t x) ∧
    IsProbabilityMeasure (limitingDoobMeasure m t x) ∧
    (1/4:ℝ≥0∞)•limitingDoobMeasure m t x≤revisedDoobKernel m W t x ∧
    revisedDoobKernel m W t x≤(4:ℝ≥0∞)•limitingDoobMeasure m t x := by
  rw [revisedDoobKernel_eq_terminalDoobMeasure m W t htW x]
  refine ⟨?_,?_,isProbabilityMeasure_terminalDoobMeasure m W t htW x,
    isProbabilityMeasure_limitingDoobMeasure m t x,terminalDoobMeasure_comparison_four hm hm1 W t htW x⟩
  · rw [terminalDoobMeasure_eq_density m W t ht x]
    congr 1
    funext y
    rw [terminalDoobDensity_explicit]
  · rw [revised_limitingDoobMeasure_eq_density m t ht x]
    congr 1
    funext y
    rw [revisedLimitingDoobDensity_moving_gaussians m t ht x y]

end DepthPaper
