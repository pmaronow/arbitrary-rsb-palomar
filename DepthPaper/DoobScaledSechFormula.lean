module

public import DepthPaper.DoobScaledSechBounds
public import Paper.DoobDifferentiation

@[expose] public section


/-! The literal scaled-sech heat identity in the terminal-region proof of
Proposition 4.10.  The underlying transition is the actual normalized Doob
measure, and the formula includes zero elapsed variance. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace DepthPaper

theorem limitingDoob_scaledSech_heat_formula (m : ℝ) (t : ℝ≥0) (x : ℝ) :
    (∫ y, Paper.sech (m * y) ^ 2 ∂limitingDoobMeasure m t x) =
      Real.exp (-m ^ 2 * (t : ℝ) / 2) / Real.cosh (m * x) *
        Paper.heatSemigroup (t : ℝ) (fun y => Paper.sech (m * y)) x := by
  rw [integral_limitingDoobMeasure]
  have he : (fun y => Paper.sech (m * y) ^ 2 * limitingDoobWeight m t x y) =
      (fun y => (Real.exp (-m ^ 2 * (t : ℝ) / 2) / Real.cosh (m * x)) *
        Paper.sech (m * y)) := by
    funext y
    unfold Paper.sech limitingDoobWeight
    field_simp
  rw [he, integral_const_mul]
  have hf : Measurable (fun y : ℝ => Paper.sech (m * y)) :=
    (Paper.continuous_sech.comp (continuous_const.mul continuous_id)).measurable
  rw [Paper.heatSemigroup_eq_gaussian_integral (t : ℝ) t.coe_nonneg _ hf x]
  simp only [Real.toNNReal_coe]

theorem limitingDoob_scaledSech_heat_identity_bound (m : ℝ) (t : ℝ≥0) (x : ℝ) :
    (∫ y, Paper.sech (m * y) ^ 2 ∂limitingDoobMeasure m t x) =
      Real.exp (-m ^ 2 * (t : ℝ) / 2) / Real.cosh (m * x) *
        Paper.heatSemigroup (t : ℝ) (fun y => Paper.sech (m * y)) x ∧
    (∫ y, Paper.sech (m * y) ^ 2 ∂limitingDoobMeasure m t x) ≤
      Real.exp (-m ^ 2 * (t : ℝ) / 2) :=
  ⟨limitingDoob_scaledSech_heat_formula m t x, limitingDoob_scaledSech_upper m t x⟩

end DepthPaper
