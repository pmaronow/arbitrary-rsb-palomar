module

public import FourPapersCommon.PositiveHessianEquivalence
public import Mathlib.Analysis.Calculus.ImplicitContDiff

@[expose] public section


/-! The actual finite-dimensional implicit function theorem for a stationary
gradient. Positivity of the partial Hessian supplies the required inverse,
including for the sup/product norm on finite atomic charts. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace FourPapersCommon
variable {Θ E : Type*}
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_smooth_stationary_selector
    (G : Θ × E → E →L[ℝ] ℝ) (p : Θ × E) {N : ℕ∞ω}
    (hG : ContDiffAt ℝ N G p) (hN : N≠0) (hz : G p=0)
    (hB : ∀ v : E,v≠0 → 0 < (fderiv ℝ G p ∘L
      ContinuousLinearMap.inr ℝ Θ E) v v) :
    ∃ z : Θ → E,z p.1=p.2 ∧ ContDiffAt ℝ N z p.1 ∧
      (∀ᶠ θ in 𝓝 p.1,G (θ,z θ)=0) ∧
      (∀ᶠ u in 𝓝 p,G u=0 ↔ z u.1=u.2) := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ G p ∘L ContinuousLinearMap.inr ℝ Θ E
  have hi : B.IsInvertible := by
    change (positiveHessianEquivalence B hB : E →L[ℝ] E →L[ℝ] ℝ).IsInvertible
    exact ContinuousLinearMap.isInvertible_equiv
  refine ⟨hG.implicitFunction hN hi,hG.implicitFunction_apply_self hN hi,
    hG.contDiffAt_implicitFunction hN hi,?_,?_⟩
  · simpa only [hz] using hG.eventually_apply_implicitFunction hN hi
  · simpa only [hz] using hG.eventually_apply_eq_iff_implicitFunction hN hi

end FourPapersCommon
