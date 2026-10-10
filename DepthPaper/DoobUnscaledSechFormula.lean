module

public import DepthPaper.DoobScaledSechFormula

@[expose] public section


/-! Literal unscaled sech endpoint integral in the proof of Lemma 4.3.
The measure is the genuine normalized cosh Doob transform. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace DepthPaper

theorem limitingDoob_unscaledSech_heat_formula (m : ℝ) (t : ℝ≥0) (x : ℝ) :
    (∫y,Paper.sech y^2 ∂limitingDoobMeasure m t x)=
      Real.exp (-m^2*(t:ℝ)/2)/Real.cosh (m*x)*
        Paper.heatSemigroup (t:ℝ) (fun y=>Paper.sech y^2*Real.cosh (m*y)) x := by
  rw [integral_limitingDoobMeasure]
  have he : (fun y=>Paper.sech y^2*limitingDoobWeight m t x y)=
      (fun y=>(Real.exp (-m^2*(t:ℝ)/2)/Real.cosh (m*x))*
        (Paper.sech y^2*Real.cosh (m*y))) := by
    funext y
    unfold limitingDoobWeight
    ring
  rw [he,integral_const_mul]
  have hf : Measurable (fun y:ℝ=>Paper.sech y^2*Real.cosh (m*y)) :=
    ((Paper.continuous_sech.pow 2).mul
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).measurable
  rw [Paper.heatSemigroup_eq_gaussian_integral (t:ℝ) t.coe_nonneg _ hf x]
  simp only [Real.toNNReal_coe]

theorem limitingDoob_unscaledSech_density_formula (m : ℝ) (t : ℝ≥0) (ht:t≠0) (x : ℝ) :
    (∫y,Paper.sech y^2 ∂limitingDoobMeasure m t x)=
      Real.exp (-m^2*(t:ℝ)/2)/Real.cosh (m*x)*
        (∫y,gaussianPDFReal x t y*Paper.sech y^2*Real.cosh (m*y)) := by
  rw [integral_limitingDoobMeasure,integral_gaussianReal_eq_integral_smul ht]
  have he : (fun y=>gaussianPDFReal x t y • (Paper.sech y^2*limitingDoobWeight m t x y))=
      (fun y=>(Real.exp (-m^2*(t:ℝ)/2)/Real.cosh (m*x))*
        (gaussianPDFReal x t y*Paper.sech y^2*Real.cosh (m*y))) := by
    funext y
    unfold limitingDoobWeight
    simp only [smul_eq_mul]
    ring
  rw [he,integral_const_mul]

end DepthPaper
