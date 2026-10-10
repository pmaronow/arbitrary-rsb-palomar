module

public import GeneralDepthPaper.LargeVarianceZeroth
public import FRSB.ConstantMassTransform

@[expose] public section


/-! Genuine normalized Gaussian Cole–Hopf transition measures and the uniform
comparison of Appendix B.2. The diffusion identification is separate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open ColeHopfFoundation.ProbabilityTheory
open scoped NNReal ENNReal
namespace GeneralDepthPaper

def terminalDoobPotential (m : ℝ) (W t : ℝ≥0) (x : ℝ) : ℝ :=
  coleHopf m (W-t) (fun y=>Real.log (Real.cosh y)) x

def terminalDoobWeight (m : ℝ) (W t : ℝ≥0) (x y : ℝ) : ℝ :=
  Real.exp (m*(terminalDoobPotential m W t y-terminalDoobPotential m W 0 x))

def terminalDoobMeasure (m : ℝ) (W t : ℝ≥0) (x : ℝ) : Measure ℝ :=
  (gaussianReal x t).withDensity (fun y=>ENNReal.ofReal (terminalDoobWeight m W t x y))

def limitingDoobWeight (m : ℝ) (t : ℝ≥0) (x y : ℝ) : ℝ :=
  Real.exp (-m^2*(t:ℝ)/2)*Real.cosh (m*y)/Real.cosh (m*x)

def limitingDoobMeasure (m : ℝ) (t : ℝ≥0) (x : ℝ) : Measure ℝ :=
  (gaussianReal x t).withDensity (fun y=>ENNReal.ofReal (limitingDoobWeight m t x y))

theorem terminalDoobPotential_lipschitz (m : ℝ) (W t : ℝ≥0) (x y : ℝ) :
    |terminalDoobPotential m W t y-terminalDoobPotential m W t x| ≤ 1*|y-x| := by
  apply abs_coleHopf_sub_le_of_lipschitz m (by fun_prop)
  intro a b
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using Paper.lipschitzWith_logcosh.dist_le_mul b a

theorem terminalDoobMeasure_eq_constantMass (m : ℝ) (W t : ℝ≥0) (ht : t ≤ W) (x : ℝ) :
    terminalDoobMeasure m W t x=FRSB.constantMassTransition m t (terminalDoobPotential m W t) x := by
  have he : coleHopf m t (terminalDoobPotential m W t) x=terminalDoobPotential m W 0 x := by
    change coleHopf m t (coleHopf m (W-t) (fun y=>Real.log (Real.cosh y))) x =
      coleHopf m (W-0) (fun y=>Real.log (Real.cosh y)) x
    rw [coleHopf_coleHopf hasLinearGrowth_logCosh (by fun_prop)]
    rw [add_tsub_cancel_of_le ht]
    simp only [terminalDoobPotential,tsub_zero]
  unfold terminalDoobMeasure FRSB.constantMassTransition
  congr 1
  funext y
  rw [FRSB.constantMassWeight,he]
  rfl

theorem isProbabilityMeasure_terminalDoobMeasure (m : ℝ) (W t : ℝ≥0) (ht : t ≤ W) (x : ℝ) :
    IsProbabilityMeasure (terminalDoobMeasure m W t x) := by
  rw [terminalDoobMeasure_eq_constantMass m W t ht x]
  have hc : Continuous (terminalDoobPotential m W t) := by
    change Continuous (fun x=>coleHopf m (W-t) (fun y=>Real.log (Real.cosh y)) x)
    simpa only [Real.toNNReal_coe,Function.comp_def,id_eq] using
      (continuous_coleHopf (Real.continuous_cosh.log (fun y=>(Real.cosh_pos y).ne'))
        hasLinearGrowth_logCosh m).comp
        (continuous_id.prodMk (continuous_const (y:=((W-t:ℝ≥0):ℝ))))
  exact FRSB.isProbabilityMeasure_constantMassTransition m t _
    (HasLinearGrowth.of_lipschitz (terminalDoobPotential_lipschitz m W t))
    hc.measurable x

theorem terminalDoobWeight_eq_moment_ratio {m : ℝ} (hm : m ≠ 0) (W t : ℝ≥0) (x y : ℝ) :
    terminalDoobWeight m W t x y=largeVarianceMoment m (W-t) y/largeVarianceMoment m W x := by
  unfold terminalDoobWeight terminalDoobPotential
  rw [mul_sub,Real.exp_sub,exp_mul_coleHopf hasLinearGrowth_logCosh (by fun_prop) hm,
    exp_mul_coleHopf hasLinearGrowth_logCosh (by fun_prop) hm]
  simp only [tsub_zero]
  rfl

theorem largeVarianceMain_ratio (m : ℝ) (W t : ℝ≥0) (ht : t ≤ W) (x y : ℝ) :
    largeVarianceMain m (W-t) y/largeVarianceMain m W x=limitingDoobWeight m t x y := by
  unfold largeVarianceMain limitingDoobWeight
  rw [mul_div_mul_comm,←Real.exp_sub,NNReal.coe_sub ht]
  rw [show (1-m)*Real.log 2+((W:ℝ)-t)*m^2/2-
      ((1-m)*Real.log 2+(W:ℝ)*m^2/2)=-m^2*(t:ℝ)/2 by ring]
  ring

theorem terminalDoobWeight_comparison {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1)
    (W t : ℝ≥0) (ht : t ≤ W) (x y : ℝ) :
    (1/2)*limitingDoobWeight m t x y ≤ terminalDoobWeight m W t x y ∧
      terminalDoobWeight m W t x y ≤ 2*limitingDoobWeight m t x y := by
  have hN := largeVarianceMoment_main_bounds hm.le hm1 (W-t) y
  have hD := largeVarianceMoment_main_bounds hm.le hm1 W x
  have hpD := largeVarianceMoment_pos m W x
  have hpMD := largeVarianceMain_pos m W x
  have hpMN := largeVarianceMain_pos m (W-t) y
  rw [terminalDoobWeight_eq_moment_ratio hm.ne',←largeVarianceMain_ratio m W t ht x y]
  constructor
  · apply (le_div_iff₀ hpD).mpr
    have hh := mul_le_mul_of_nonneg_left hD.2 (by positivity : 0 ≤ (1/2)*(largeVarianceMain m (W-t) y/largeVarianceMain m W x))
    have he : ((1/2)*(largeVarianceMain m (W-t) y/largeVarianceMain m W x))*largeVarianceMain m W x=
        largeVarianceMain m (W-t) y/2 := by field_simp
    rw [he] at hh
    exact hh.trans hN.1
  · apply (div_le_iff₀ hpD).mpr
    have hh := mul_le_mul_of_nonneg_left hD.1 (by positivity : 0 ≤ 2*(largeVarianceMain m (W-t) y/largeVarianceMain m W x))
    have he : (2*(largeVarianceMain m (W-t) y/largeVarianceMain m W x))*(largeVarianceMain m W x/2)=
        largeVarianceMain m (W-t) y := by field_simp
    rw [he] at hh
    exact hN.2.trans hh

end GeneralDepthPaper
