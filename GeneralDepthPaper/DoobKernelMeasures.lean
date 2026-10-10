module

public import GeneralDepthPaper.DoobKernelBounds

@[expose] public section


/-! Genuine probability transition measures and the literal measure comparison
of Appendix B.2. The proved factor2 comparison is stronger than the printed
factor4 estimate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace GeneralDepthPaper

 theorem limitingDoobWeight_pos (m : ℝ) (t : ℝ≥0) (x y : ℝ) :
     0 < limitingDoobWeight m t x y := by
   unfold limitingDoobWeight
   positivity

 theorem integral_cosh_gaussian (m x : ℝ) (t : ℝ≥0) :
     (∫y,Real.cosh (m*y) ∂gaussianReal x t)=Real.exp ((t:ℝ)*m^2/2)*Real.cosh (m*x) := by
   have hp := integrable_exp_mul_gaussianReal (μ:=x) (v:=t) m
   have hn := integrable_exp_mul_gaussianReal (μ:=x) (v:=t) (-m)
   simp_rw [Real.cosh_eq]
   rw [integral_div,integral_add hp (by simpa only [neg_mul] using hn)]
   have he (a:ℝ) : (∫y,Real.exp (a*y) ∂gaussianReal x t)=Real.exp (x*a+(t:ℝ)*a^2/2) := by
     simpa only [mgf,id_eq] using congrFun (mgf_id_gaussianReal (μ:=x) (v:=t)) a
   rw [he m]
   have hne : (∫y,Real.exp (-(m*y)) ∂gaussianReal x t)=Real.exp (-m*x+(t:ℝ)*m^2/2) := by
     simpa only [neg_mul,neg_sq,mul_neg,mul_comm x m] using he (-m)
   rw [hne,show x*m=m*x by ring,show -m*x=-(m*x) by ring]
   simp only [Real.exp_add]
   ring

 theorem integrable_limitingDoobWeight (m : ℝ) (t : ℝ≥0) (x : ℝ) :
     Integrable (limitingDoobWeight m t x) (gaussianReal x t) := by
   have hp := integrable_exp_mul_gaussianReal (μ:=x) (v:=t) m
   have hn := integrable_exp_mul_gaussianReal (μ:=x) (v:=t) (-m)
   have hc : Integrable (fun y=>Real.cosh (m*y)) (gaussianReal x t) := by
     simp_rw [Real.cosh_eq]
     exact (hp.add (by simpa only [neg_mul] using hn)).div_const 2
   exact (hc.const_mul (Real.exp (-m^2*(t:ℝ)/2))).div_const _

 theorem integral_limitingDoobWeight (m : ℝ) (t : ℝ≥0) (x : ℝ) :
     (∫y,limitingDoobWeight m t x y ∂gaussianReal x t)=1 := by
   unfold limitingDoobWeight
   rw [integral_div,integral_const_mul,integral_cosh_gaussian]
   rw [←mul_assoc,←Real.exp_add,show -m^2*(t:ℝ)/2+(t:ℝ)*m^2/2=0 by ring,Real.exp_zero,one_mul,
     div_self (Real.cosh_pos (m*x)).ne']

 theorem isProbabilityMeasure_limitingDoobMeasure (m : ℝ) (t : ℝ≥0) (x : ℝ) :
     IsProbabilityMeasure (limitingDoobMeasure m t x) := ⟨by
   rw [limitingDoobMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
     ←ofReal_integral_eq_lintegral_ofReal (integrable_limitingDoobWeight m t x)
       (.of_forall fun y=>(limitingDoobWeight_pos m t x y).le),integral_limitingDoobWeight]
   simp⟩

 theorem terminalDoobMeasure_comparison_two {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1)
     (W t : ℝ≥0) (ht : t ≤ W) (x : ℝ) :
     (1/2:ℝ≥0∞)•limitingDoobMeasure m t x ≤ terminalDoobMeasure m W t x ∧
       terminalDoobMeasure m W t x ≤ (2:ℝ≥0∞)•limitingDoobMeasure m t x := by
   have hlo : (1/2:ℝ≥0∞)•limitingDoobMeasure m t x=
       (gaussianReal x t).withDensity (fun y=>ENNReal.ofReal ((1/2)*limitingDoobWeight m t x y)) := by
     rw [limitingDoobMeasure,←withDensity_smul' _ _ (by norm_num)]
     congr 1
     funext y
     simp only [Pi.smul_apply,smul_eq_mul,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
     rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
     norm_num
   have hup : (2:ℝ≥0∞)•limitingDoobMeasure m t x=
       (gaussianReal x t).withDensity (fun y=>ENNReal.ofReal (2*limitingDoobWeight m t x y)) := by
     rw [limitingDoobMeasure,←withDensity_smul' _ _ (by norm_num)]
     congr 1
     funext y
     simp only [Pi.smul_apply,smul_eq_mul,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
     norm_num
   rw [hlo,hup,terminalDoobMeasure]
   exact ⟨withDensity_mono (.of_forall fun y=>ENNReal.ofReal_le_ofReal
     (terminalDoobWeight_comparison hm hm1 W t ht x y).1),
     withDensity_mono (.of_forall fun y=>ENNReal.ofReal_le_ofReal
       (terminalDoobWeight_comparison hm hm1 W t ht x y).2)⟩

 theorem terminalDoobMeasure_comparison_four {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1)
     (W t : ℝ≥0) (ht : t ≤ W) (x : ℝ) :
     (1/4:ℝ≥0∞)•limitingDoobMeasure m t x ≤ terminalDoobMeasure m W t x ∧
       terminalDoobMeasure m W t x ≤ (4:ℝ≥0∞)•limitingDoobMeasure m t x := by
   have hh := terminalDoobMeasure_comparison_two hm hm1 W t ht x
   have hmono {a b:ℝ≥0∞} (hab:a≤b) : a•limitingDoobMeasure m t x ≤ b•limitingDoobMeasure m t x := by
     apply Measure.le_iff.mpr
     intro s _
     simp only [Measure.smul_apply,smul_eq_mul]
     gcongr
   exact ⟨(hmono (by norm_num : (1/4:ℝ≥0∞) ≤ 1/2)).trans hh.1,
     hh.2.trans (hmono (by norm_num : (2:ℝ≥0∞) ≤ 4))⟩

end GeneralDepthPaper
