module

public import DepthPaper.ColeHopfCentered

@[expose] public section


/-! The literal centered exponential representation in Appendix A.
The Gaussian integral is genuine for every linear-growth measurable terminal
function, with the mass-zero branch retained. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace DepthPaper
open ColeHopfFoundation.ProbabilityTheory

theorem coleHopf_centered_exponential_representation (g : ℝ→ℝ)
    (hg : HasLinearGrowth g) (hm : Measurable g) (V : ℝ≥0) (x a : ℝ) :
    coleHopf a V g x-g x =
      if a=0 then ∫d,g (x+d)-g x ∂gaussianReal 0 V
      else a⁻¹*Real.log (∫d,Real.exp (a*(g (x+d)-g x)) ∂gaussianReal 0 V) := by
  have hshift:=coleHopf_add_const hg hm (-g x) a V x
  by_cases ha:a=0
  · subst a
    simp only [coleHopf_zero,ite_true]
    rw [integral_sub ((hg.toHasExpGrowth.comp_add_const x).integrable_gaussianReal
      (hm.comp (measurable_const_add x)).aestronglyMeasurable) (integrable_const _)]
    simp only [integral_const,probReal_univ,one_smul]
  · rw [if_neg ha]
    have hs : coleHopf a V (fun y=>g y+(-g x)) x=coleHopf a V g x-g x := by
      simpa only [sub_eq_add_neg] using hshift
    rw [←hs,coleHopf_of_ne ha]
    simp only [sub_eq_add_neg,one_div]

end DepthPaper
